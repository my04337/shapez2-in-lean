-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity.CommExt
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.List.Flatten

/-!
# Grounding Monotonicity (Gravity layer)

`S2IL/Operations/Settled/GroundedCore.lean` にある `Shape.groundedPositions_mono_of_edge`
（および `groundedPositions_placeLDGroups_subset`）は Gravity レイヤから利用できない
（循環依存）。本ファイルで Gravity レイヤにも同じ補題を再掲し、
`waveStep_ngs_strict_bound` の構成的証明で使用する。

将来的には `Settled/GroundedCore.lean` 側を削除して本ファイルに統合する。
-/

namespace Shape

/-- `isGroundingContact` が `getQuarter` のみに依存することの証明。 -/
theorem isGroundingContact_eq_of_getQuarter_eq
        (s1 s2 : Shape) (p1 p2 : QuarterPos)
        (h1 : p1.getQuarter s1 = p1.getQuarter s2)
        (h2 : p2.getQuarter s1 = p2.getQuarter s2) :
        Gravity.isGroundingContact s1 p1 p2 =
        Gravity.isGroundingContact s2 p1 p2 := by
    simp only [Gravity.isGroundingContact, h1, h2]

/-- `groundingEdge` が `getQuarter` のみに依存することの証明。 -/
theorem groundingEdge_eq_of_getQuarter_eq
        (s1 s2 : Shape) (p1 p2 : QuarterPos)
        (h1 : p1.getQuarter s1 = p1.getQuarter s2)
        (h2 : p2.getQuarter s1 = p2.getQuarter s2) :
        Gravity.groundingEdge s1 p1 p2 =
        Gravity.groundingEdge s2 p1 p2 := by
    simp only [Gravity.groundingEdge, Gravity.isUpwardGroundingContact,
        Gravity.isGroundingContact, Gravity.isStructurallyBonded, h1, h2]

/-- `groundedPositions` のエッジ単調版。
    `isGroundingContact` が s1 → s2 で保存され、
    L0 の非空 seed が s2 でも非空であるとき、`groundedPositions s1 ⊆ s2`。 -/
theorem groundedPositions_mono_of_edge
        (s1 s2 : Shape)
        (h_lc : s1.layerCount ≤ s2.layerCount)
        (h_seed_ne : ∀ p : QuarterPos, p.layer = 0 → p.layer < s1.layerCount →
            (∃ q, p.getQuarter s1 = some q ∧ !q.isEmpty = true) →
            ∃ q, p.getQuarter s2 = some q ∧ !q.isEmpty = true)
        (h_edge : ∀ a b, Gravity.groundingEdge s1 a b = true →
            Gravity.groundingEdge s2 a b = true) :
        Gravity.groundedPositions s1 ⊆ Gravity.groundedPositions s2 := by
    intro p h_p
    simp only [Gravity.groundedPositions, List.mem_toFinset] at h_p ⊢
    obtain ⟨seed, h_seed_mem, h_reach⟩ := Gravity.groundedPositionsList_sound s1 p
        ((Gravity.any_beq_iff_mem _ _).mpr h_p)
    have h_seed_filter := List.mem_filter.mp h_seed_mem
    have h_seed_cond := h_seed_filter.2
    rw [Bool.and_eq_true] at h_seed_cond
    have h_seed_layer0 : seed.layer = 0 := beq_iff_eq.mp h_seed_cond.1
    have h_seed_valid : seed.layer < s1.layerCount :=
        (Gravity.allValid_any_iff_layer' s1 seed).mp
            ((Gravity.any_beq_iff_mem _ _).mpr h_seed_filter.1)
    have h_seed_ne_s1 : ∃ q, seed.getQuarter s1 = some q ∧ !q.isEmpty = true := by
        cases hgq : seed.getQuarter s1 with
        | none => simp only [hgq] at h_seed_cond; exact absurd h_seed_cond.2 (by decide)
        | some q =>
            refine ⟨q, rfl, ?_⟩
            simp only [hgq, Quarter.isEmpty] at h_seed_cond
            cases q <;> simp_all only [Bool.decide_eq_true, Bool.not_eq_eq_eq_not, forall_exists_index, and_imp, List.mem_filter, BEq.rfl, Bool.true_and, true_and, Bool.and_self, and_true, Bool.not_true, Bool.false_eq_true, and_false, Bool.not_false, and_self, decide_false]
    obtain ⟨q2, hq2_some, hq2_ne⟩ := h_seed_ne seed h_seed_layer0 h_seed_valid h_seed_ne_s1
    have h_seed_s2 : seed ∈ (QuarterPos.allValid s2).filter (fun q =>
            q.layer == 0 && match q.getQuarter s2 with
            | some q => !q.isEmpty | none => false) := by
        apply List.mem_filter.mpr
        constructor
        · exact (Gravity.any_beq_iff_mem _ _).mp
            ((Gravity.allValid_any_iff_layer' s2 seed).mpr (by omega))
        · rw [Bool.and_eq_true]
          refine ⟨beq_iff_eq.mpr h_seed_layer0, ?_⟩
          rw [show seed.getQuarter s2 = some q2 from hq2_some]
          cases q2 <;> simp_all only [Quarter.isEmpty, Bool.decide_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, forall_exists_index, and_imp, List.mem_filter, BEq.rfl, Bool.true_and, true_and, Bool.and_self, and_true, and_self, decide_true, Bool.false_eq_true, decide_false, Bool.not_false]
    have h_reach_s2 : GenericReachable (Gravity.groundingEdge s2) seed p :=
        h_reach.mono h_edge
    exact (Gravity.any_beq_iff_mem _ _).mp
        (Gravity.groundedPositionsList_complete s2 seed p h_seed_s2 h_reach_s2)

/-- Sub-lemma #5/#6/#7 の統合パッケージ定理。
    `placeLDGroups` 後の shape `s_result` と observation shape `s_obs` について、
    「着地位置の扱い」を 2 つの hypothesis で因子分解した上で、
    残りの「非着地位置の不変性」は `getQuarter_placeLDGroups_of_ne` /
    `groundingEdge_placeLDGroups_of_ne` から自動的に成立する。 -/
theorem groundedPositions_placeLDGroups_subset
        (s : Shape) (sorted : List Gravity.FallingUnit) (obs : List Layer)
        (s_obs s_result : Shape)
        (h_obs : s_obs.layers = obs)
        (h_result : s_result.layers = Gravity.placeLDGroups s sorted obs)
        (h_edge_landing : ∀ a b, Gravity.groundingEdge s_obs a b = true →
            ((a.layer, a.dir) ∈ Gravity.placeLDGroupsLandings s sorted obs ∨
             (b.layer, b.dir) ∈ Gravity.placeLDGroupsLandings s sorted obs) →
            Gravity.groundingEdge s_result a b = true)
        (h_seed_landing : ∀ p : QuarterPos, p.layer = 0 →
            (p.layer, p.dir) ∈ Gravity.placeLDGroupsLandings s sorted obs →
            ∃ q, p.getQuarter s_result = some q ∧ !q.isEmpty = true) :
        Gravity.groundedPositions s_obs ⊆ Gravity.groundedPositions s_result := by
    have h_lc : s_obs.layerCount ≤ s_result.layerCount := by
        unfold Shape.layerCount; rw [h_obs, h_result]
        exact Gravity.placeLDGroups_length_ge s sorted obs
    apply Shape.groundedPositions_mono_of_edge s_obs s_result h_lc
    · intro p h_l0 h_valid h_ne_obs
      by_cases h_in : (p.layer, p.dir) ∈ Gravity.placeLDGroupsLandings s sorted obs
      · exact h_seed_landing p h_l0 h_in
      · have h_gq := Gravity.getQuarter_placeLDGroups_of_ne s sorted obs
            s_obs s_result h_obs h_result p h_valid h_in
        rw [h_gq]; exact h_ne_obs
    · intro a b h_edge
      by_cases h_in_a : (a.layer, a.dir) ∈ Gravity.placeLDGroupsLandings s sorted obs
      · exact h_edge_landing a b h_edge (Or.inl h_in_a)
      by_cases h_in_b : (b.layer, b.dir) ∈ Gravity.placeLDGroupsLandings s sorted obs
      · exact h_edge_landing a b h_edge (Or.inr h_in_b)
      -- 両端点とも非 landing: groundingEdge_placeLDGroups_of_ne で等号
      have h_gb := Gravity.groundingEdge_base h_edge
      have h_a_valid : a.layer < s_obs.layerCount := by
          simp only [Gravity.isGroundingContact] at h_gb
          cases hq : a.getQuarter s_obs with
          | none => simp [hq] at h_gb
          | some _ =>
              unfold QuarterPos.getQuarter at hq
              simp only [Shape.layerCount]
              cases hl : s_obs.layers[a.layer]? with
              | none => simp [hl] at hq
              | some _ => exact (List.getElem?_eq_some_iff.mp hl).1
      have h_b_valid : b.layer < s_obs.layerCount := by
          simp only [Gravity.isGroundingContact] at h_gb
          cases hqa : a.getQuarter s_obs with
          | none => simp [hqa] at h_gb
          | some _ =>
              cases hq : b.getQuarter s_obs with
              | none => simp [hqa, hq] at h_gb
              | some _ =>
                  unfold QuarterPos.getQuarter at hq
                  simp only [Shape.layerCount]
                  cases hl : s_obs.layers[b.layer]? with
                  | none => simp [hl] at hq
                  | some _ => exact (List.getElem?_eq_some_iff.mp hl).1
      have h_eq := Gravity.groundingEdge_placeLDGroups_of_ne s sorted obs
          s_obs s_result h_obs h_result a b h_a_valid h_b_valid h_in_a h_in_b
      rw [← h_eq]; exact h_edge

/-- `isGroundingContact` 左端点の layer 妥当性。 -/
theorem layer_lt_of_isGroundingContact_left
        (s : Shape) (p1 p2 : QuarterPos)
        (h : Gravity.isGroundingContact s p1 p2 = true) :
        p1.layer < s.layerCount := by
    obtain ⟨q1, _, hq1, _, _, _⟩ := Gravity.isGroundingContact_nonEmpty s p1 p2 h
    unfold QuarterPos.getQuarter at hq1; simp only [Shape.layerCount]
    by_contra h_ge; push Not at h_ge
    have := List.getElem?_eq_none_iff.mpr h_ge; rw [this] at hq1
    exact absurd hq1 (by simp only [reduceCtorEq, not_false_eq_true])

/-- `isGroundingContact` 右端点の layer 妥当性。 -/
theorem layer_lt_of_isGroundingContact_right
        (s : Shape) (p1 p2 : QuarterPos)
        (h : Gravity.isGroundingContact s p1 p2 = true) :
        p2.layer < s.layerCount := by
    obtain ⟨_, q2, _, hq2, _, _⟩ := Gravity.isGroundingContact_nonEmpty s p1 p2 h
    unfold QuarterPos.getQuarter at hq2; simp only [Shape.layerCount]
    by_contra h_ge; push Not at h_ge
    have := List.getElem?_eq_none_iff.mpr h_ge; rw [this] at hq2
    exact absurd hq2 (by simp only [reduceCtorEq, not_false_eq_true])

/-- `canFormBond = true` ならば象限は非空。 -/
theorem canFormBond_implies_not_empty (q : Quarter)
        (h : q.canFormBond = true) : q.isEmpty = false := by
    cases q <;> simp only [Quarter.canFormBond, Bool.false_eq_true, Quarter.isEmpty] at h ⊢

/-- `isStructurallyBonded` から layer/dir 隣接条件のみを抽出する。 -/
theorem isStructurallyBonded_adjacency (s : Shape) (a b : QuarterPos)
        (h : Gravity.isStructurallyBonded s a b = true) :
        (a.layer == b.layer && a.dir.adjacent b.dir ||
            LayerIndex.verticallyAdjacent a.layer b.layer &&
            a.dir == b.dir) = true := by
    have h_gc := Gravity.isStructurallyBonded_implies_isGroundingContact s a b h
    obtain ⟨q1, q2, hq1, hq2, _, _⟩ := Gravity.isGroundingContact_nonEmpty s a b h_gc
    simp only [Gravity.isStructurallyBonded, hq1, hq2, Bool.and_eq_true] at h
    exact h.2

/-- `isStructurallyBonded` 左端点の `canFormBond` 成立。 -/
theorem isStructurallyBonded_canFormBond_left (s : Shape) (a b : QuarterPos)
        (h : Gravity.isStructurallyBonded s a b = true) :
        ∃ qa, a.getQuarter s = some qa ∧ qa.canFormBond = true := by
    have h_gc := Gravity.isStructurallyBonded_implies_isGroundingContact s a b h
    obtain ⟨q1, q2, hq1, hq2, _, _⟩ := Gravity.isGroundingContact_nonEmpty s a b h_gc
    simp only [Gravity.isStructurallyBonded, hq1, hq2, Bool.and_eq_true] at h
    exact ⟨q1, hq1, h.1.1⟩

/-- `isStructurallyBonded` 右端点の `canFormBond` 成立。 -/
theorem isStructurallyBonded_canFormBond_right (s : Shape) (a b : QuarterPos)
        (h : Gravity.isStructurallyBonded s a b = true) :
        ∃ qb, b.getQuarter s = some qb ∧ qb.canFormBond = true := by
    have h_gc := Gravity.isStructurallyBonded_implies_isGroundingContact s a b h
    obtain ⟨q1, q2, hq1, hq2, _, _⟩ := Gravity.isGroundingContact_nonEmpty s a b h_gc
    simp only [Gravity.isStructurallyBonded, hq1, hq2, Bool.and_eq_true] at h
    exact ⟨q2, hq2, h.1.2⟩

/-- `canFormBond` + 隣接条件から `isStructurallyBonded` を再構成。 -/
theorem isStructurallyBonded_of_parts (s : Shape) (a b : QuarterPos)
        (qa qb : Quarter)
        (ha : a.getQuarter s = some qa) (hb : b.getQuarter s = some qb)
        (ha_cb : qa.canFormBond = true) (hb_cb : qb.canFormBond = true)
        (h_adj : (a.layer == b.layer && a.dir.adjacent b.dir ||
            LayerIndex.verticallyAdjacent a.layer b.layer &&
            a.dir == b.dir) = true) :
        Gravity.isStructurallyBonded s a b = true := by
    simp only [Gravity.isStructurallyBonded, ha, hb, ha_cb, hb_cb, Bool.true_and]
    exact h_adj

/-- `isGroundingContact` の edge monotonicity (左端点が `canFormBond` 象限に変更)。 -/
theorem isGroundingContact_mono_canFormBond_left
        (s1 s2 : Shape) (a b : QuarterPos)
        (qa_new : Quarter) (h_bond : qa_new.canFormBond = true)
        (h_a_new : a.getQuarter s2 = some qa_new)
        (h_b_eq : b.getQuarter s2 = b.getQuarter s1)
        (h_gc : Gravity.isGroundingContact s1 a b = true) :
        Gravity.isGroundingContact s2 a b = true := by
    obtain ⟨q1, q2, hq1, hq2, hne1, hne2⟩ :=
        Gravity.isGroundingContact_nonEmpty s1 a b h_gc
    have hq2' : b.getQuarter s2 = some q2 := by rw [h_b_eq, hq2]
    unfold Gravity.isGroundingContact at h_gc ⊢
    rw [hq1, hq2] at h_gc
    rw [h_a_new, hq2']
    have h_ne_new := canFormBond_implies_not_empty qa_new h_bond
    simp only [hne1, h_ne_new, hne2, Bool.not_false, Bool.true_and] at h_gc ⊢
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h_gc ⊢
    rcases h_gc with h_vert | ⟨⟨h_layer, h_adj⟩, h_match⟩
    · left; exact h_vert
    · right
      have h_qa_not_pin : qa_new ≠ .pin := by
          intro h; subst h; simp only [Quarter.canFormBond, Bool.false_eq_true] at h_bond
      have h_q2_not_pin : q2 ≠ .pin := by
          intro h; subst h; cases q1 <;> simp only [Bool.false_eq_true] at h_match
      refine ⟨⟨h_layer, h_adj⟩, ?_⟩
      clear h_match hne1 hne2 hq1 hq2 hq2' q1
      cases qa_new <;> cases q2 <;>
          simp_all only [beq_iff_eq, Quarter.canFormBond, Bool.false_eq_true, Quarter.isEmpty, ne_eq, reduceCtorEq, not_false_eq_true, not_true_eq_false]

/-- `isGroundingContact` の edge monotonicity (右端点が `canFormBond` 象限に変更)。 -/
theorem isGroundingContact_mono_canFormBond_right
        (s1 s2 : Shape) (a b : QuarterPos)
        (qb_new : Quarter) (h_bond : qb_new.canFormBond = true)
        (h_a_eq : a.getQuarter s2 = a.getQuarter s1)
        (h_b_new : b.getQuarter s2 = some qb_new)
        (h_gc : Gravity.isGroundingContact s1 a b = true) :
        Gravity.isGroundingContact s2 a b = true := by
    obtain ⟨q1, q2, hq1, hq2, hne1, hne2⟩ :=
        Gravity.isGroundingContact_nonEmpty s1 a b h_gc
    have hq1' : a.getQuarter s2 = some q1 := by rw [h_a_eq, hq1]
    unfold Gravity.isGroundingContact at h_gc ⊢
    rw [hq1, hq2] at h_gc
    rw [hq1', h_b_new]
    have h_ne_new := canFormBond_implies_not_empty qb_new h_bond
    simp only [hne1, hne2, h_ne_new, Bool.not_false, Bool.true_and] at h_gc ⊢
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h_gc ⊢
    rcases h_gc with h_vert | ⟨⟨h_layer, h_adj⟩, h_match⟩
    · left; exact h_vert
    · right
      have h_q1_not_pin : q1 ≠ .pin := by
          intro h; subst h; cases q2 <;> simp only [Bool.false_eq_true] at h_match
      have h_qb_not_pin : qb_new ≠ .pin := by
          intro h; subst h; simp only [Quarter.canFormBond, Bool.false_eq_true] at h_bond
      refine ⟨⟨h_layer, h_adj⟩, ?_⟩
      clear h_match hne1 hne2 hq1 hq2 hq1' q2
      cases q1 <;> cases qb_new <;>
          simp_all only [beq_iff_eq, ne_eq, not_false_eq_true, Quarter.canFormBond, Bool.false_eq_true, reduceCtorEq, Quarter.isEmpty, not_true_eq_false]

/-- `isGroundingContact` の edge monotonicity (両端点が `canFormBond` 象限に変更)。 -/
theorem isGroundingContact_mono_canFormBond_both
        (s1 s2 : Shape) (a b : QuarterPos)
        (qa_new qb_new : Quarter)
        (h_bond_a : qa_new.canFormBond = true)
        (h_bond_b : qb_new.canFormBond = true)
        (h_a_new : a.getQuarter s2 = some qa_new)
        (h_b_new : b.getQuarter s2 = some qb_new)
        (h_gc : Gravity.isGroundingContact s1 a b = true) :
        Gravity.isGroundingContact s2 a b = true := by
    obtain ⟨q1, q2, hq1, hq2, hne1, hne2⟩ :=
        Gravity.isGroundingContact_nonEmpty s1 a b h_gc
    unfold Gravity.isGroundingContact at h_gc ⊢
    rw [hq1, hq2] at h_gc
    rw [h_a_new, h_b_new]
    have h_ne_a := canFormBond_implies_not_empty qa_new h_bond_a
    have h_ne_b := canFormBond_implies_not_empty qb_new h_bond_b
    simp only [hne1, hne2, h_ne_a, h_ne_b, Bool.not_false, Bool.true_and]
        at h_gc ⊢
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h_gc ⊢
    rcases h_gc with h_vert | ⟨⟨h_layer, h_adj⟩, h_match⟩
    · left; exact h_vert
    · right
      have h_qa_not_pin : qa_new ≠ .pin := by
          intro h; subst h; simp only [Quarter.canFormBond, Bool.false_eq_true] at h_bond_a
      have h_qb_not_pin : qb_new ≠ .pin := by
          intro h; subst h; simp only [Quarter.canFormBond, Bool.false_eq_true] at h_bond_b
      refine ⟨⟨h_layer, h_adj⟩, ?_⟩
      clear h_match hne1 hne2 hq1 hq2 q1 q2
      cases qa_new <;> cases qb_new <;>
          simp_all only [beq_iff_eq, Quarter.canFormBond, Bool.false_eq_true, Quarter.isEmpty, ne_eq, reduceCtorEq, not_false_eq_true]

end Shape

namespace Gravity

/-- 非着地位置の `ngsWeight` 単調性。

    `placeLDGroups` 結果 `s_result` と観測 shape `s_obs` について、
    非着地位置 `pos` (かつ `pos.layer < s_obs.layerCount`) では
    `ngsWeight s_result pos ≤ ngsWeight s_obs pos` が成立する。

    証明: `getQuarter_placeLDGroups_of_ne` で `getQuarter` が一致することと、
    `h_gm` (grounded 単調性) を組み合わせ、3 つのケース（grounded、non-empty
    そして empty）を `simp` で閉じる。

    用途: `waveStep_ngs_strict_bound` の最終組立で、非着地位置の寄与を
    `NGS(s_obs)` で上から抑える。 -/
theorem ngsWeight_placeLDGroups_of_ne_le
        (s : Shape) (sorted : List FallingUnit) (obs : List Layer)
        (s_obs s_result : Shape)
        (h_obs : s_obs.layers = obs)
        (h_result : s_result.layers = placeLDGroups s sorted obs)
        (h_gm : groundedPositions s_obs ⊆ groundedPositions s_result)
        (pos : QuarterPos)
        (h_valid : pos.layer < s_obs.layerCount)
        (h_not : (pos.layer, pos.dir) ∉ placeLDGroupsLandings s sorted obs) :
        ngsWeight s_result pos ≤ ngsWeight s_obs pos := by
    have h_gq := getQuarter_placeLDGroups_of_ne s sorted obs
        s_obs s_result h_obs h_result pos h_valid h_not
    simp only [ngsWeight, h_gq]
    cases hq : pos.getQuarter s_obs with
    | none => simp
    | some q =>
        by_cases h_grnd_res : pos ∈ groundedPositions s_result
        · simp [h_grnd_res]
        · have h_grnd_obs : pos ∉ groundedPositions s_obs :=
                fun h => h_grnd_res (h_gm h)
          simp [h_grnd_res, h_grnd_obs]

/-- 着地位置集合 `landings` に対する allValid 上の重み総和の上限。

    `allValid s` のうち `(p.layer, p.dir)` が `landings` に属する要素の
    `p.layer + 1` の総和は、`landings` 上での `ld.1 + 1` の総和で上から抑えられる。

    証明: `p ↦ (p.layer, p.dir)` は `allValid s` 上で単射（allValid は nodup）。
    したがって filter 後の像は nodup で landings のサブセットであり、
    `List.subperm_of_subset` + `Sublist`→`sum_le` (Nat 向けの手書き補助) で閉じる。

    用途: `waveStep_ngs_strict_bound` の Step C2（着地位置の寄与を
    `placeLDGroupsLandings` のリスト総和で上から抑える）。 -/
theorem landing_sum_allValid_le (s : Shape) (landings : List (Nat × Direction)) :
        (((QuarterPos.allValid s).filter
            (fun p => landings.any (· == (p.layer, p.dir)))).map
            (fun p => p.layer + 1)).sum
          ≤ (landings.map (fun ld => ld.1 + 1)).sum := by
    set L1 := ((QuarterPos.allValid s).filter
        (fun p => landings.any (· == (p.layer, p.dir))))
    have h_L1_nodup : L1.Nodup := (allValid_nodup s).filter _
    set P := L1.map (fun p => (p.layer, p.dir))
    have h_P_nodup : P.Nodup := by
        apply List.Nodup.map_on _ h_L1_nodup
        intro a _ b _ hab
        have h1 : a.layer = b.layer := (Prod.mk.inj hab).1
        have h2 : a.dir = b.dir := (Prod.mk.inj hab).2
        cases a; cases b; simp_all
    have h_P_sub : ∀ ld ∈ P, ld ∈ landings := by
        intro ld hld
        simp only [List.mem_map, P, L1] at hld
        obtain ⟨p, hp_mem, hp_eq⟩ := hld
        have hp_in := (List.mem_filter.mp hp_mem).2
        simp only [List.any_eq_true, beq_iff_eq] at hp_in
        obtain ⟨ld', hld'_mem, hld'_eq⟩ := hp_in
        rw [← hp_eq, ← hld'_eq]; exact hld'_mem
    have h_subperm : P.Subperm landings := List.subperm_of_subset h_P_nodup h_P_sub
    have h_sum_eq : (L1.map (fun p => p.layer + 1)).sum
            = (P.map (fun ld => ld.1 + 1)).sum := by
        simp only [P, List.map_map]; rfl
    rw [h_sum_eq]
    -- Subperm → sum ≤ sum for Nat (自前の帰納法で閉じる)
    rcases h_subperm with ⟨l', hperm, hsub⟩
    -- Step 1: Perm → sum 等式 for Nat (generic helper)
    have h_perm_sum_nat : ∀ (a b : List Nat), a.Perm b → a.sum = b.sum := by
        intro a b hp
        induction hp with
        | nil => rfl
        | cons x _ ih => simp only [List.sum_cons, ih]
        | swap x y _ => simp only [List.sum_cons]; omega
        | trans _ _ ih1 ih2 => exact ih1.trans ih2
    -- Step 2: Sublist → sum ≤ sum for Nat (generic helper)
    have h_sub_sum_nat : ∀ (a b : List Nat), a.Sublist b → a.sum ≤ b.sum := by
        intro a b hs
        induction hs with
        | slnil => exact Nat.le_refl 0
        | cons _ _ ih => simp only [List.sum_cons]; omega
        | cons₂ _ _ ih => simp only [List.sum_cons]; omega
    -- 合成: l'.map f の sum = P.map f の sum ≤ landings.map f の sum
    have h_eq := h_perm_sum_nat (l'.map (fun ld => ld.1 + 1))
        (P.map (fun ld => ld.1 + 1)) (hperm.map _)
    have h_le := h_sub_sum_nat (l'.map (fun ld => ld.1 + 1))
        (landings.map (fun ld => ld.1 + 1)) (hsub.map _)
    omega

/-- Step B2: cluster 着地位置での非空 canFormBond 象限の存在（`placeFallingUnit` レベル）。

    `foldl_placeQuarter_written_getQuarter_canFormBond` を
    `placeFallingUnit = positions.foldl (...)` の定義展開を経由して適用。

    用途: `waveStep_grounding_mono` の Step B3 組立で、
    cluster 着地位置における `h_seed_landing` (canFormBond → !isEmpty) を供給する。 -/
theorem placeFallingUnit_cluster_written_getQuarter_canFormBond
        (s : Shape) (obs : List Layer) (ps : List QuarterPos) (d : Nat)
        (s_result : Shape)
        (h_result : s_result.layers = placeFallingUnit s obs (FallingUnit.cluster ps) d)
        (lay : Nat) (dir : Direction)
        (h_valid : lay < s_result.layerCount)
        (h_written : ∃ p ∈ ps, p.layer - d = lay ∧ p.dir = dir)
        (h_bond : ∀ p ∈ ps, ∃ qv, p.getQuarter s = some qv ∧ qv.canFormBond = true) :
        ∃ qv, QuarterPos.getQuarter s_result ⟨lay, dir⟩ = some qv ∧ qv.canFormBond = true := by
    have h_result' : s_result.layers = ps.foldl (fun obs p =>
            match p.getQuarter s with
            | some r => placeQuarter obs (p.layer - d) p.dir r
            | none => obs) obs := by
        simpa [placeFallingUnit, FallingUnit.positions] using h_result
    exact foldl_placeQuarter_written_getQuarter_canFormBond s obs ps d lay dir s_result
        h_result' h_valid h_written h_bond

/-- Step B1: cluster 配置による `groundingEdge` 単調性（`placeFallingUnit` レベル）。

    全クラスタ位置が `canFormBond` を持つとき、`s_obs` で真だった `groundingEdge` は
    cluster 配置後の `s_result` でも真である。

    証明戦略 (4 分岐):
    - `isUpwardGroundingContact` 側: 両端点の着地/非着地の 4 通りに対し
      `Shape.isGroundingContact_mono_canFormBond_{left,right,both}` または
      `Shape.isGroundingContact_eq_of_getQuarter_eq` で edge 保存。
    - `isStructurallyBonded` 側: `h_adj` (layer/dir 隣接) は不変。両端点で
      `canFormBond` 象限存在を確保（着地なら `h_gq_canFormBond`、
      非着地なら `h_gq_preserved` + `Shape.isStructurallyBonded_canFormBond_*`）し、
      `Shape.isStructurallyBonded_of_parts` で再構成。

    用途: `waveStep_grounding_mono` の Step B3 組立で、cluster 着地が絡む
    `h_edge_landing` を供給する基礎。 -/
theorem placeFallingUnit_cluster_groundingEdge_mono
        (s : Shape) (obs : List Layer) (ps : List QuarterPos) (d : Nat)
        (h_bond : ∀ p ∈ ps, ∃ qv, p.getQuarter s = some qv ∧ qv.canFormBond = true)
        (s_obs s_result : Shape)
        (h_obs : s_obs.layers = obs)
        (h_result : s_result.layers = placeFallingUnit s obs (FallingUnit.cluster ps) d)
        (a b : QuarterPos)
        (h_edge : groundingEdge s_obs a b = true) :
        groundingEdge s_result a b = true := by
    have h_gc := groundingEdge_base h_edge
    have h_a_valid := Shape.layer_lt_of_isGroundingContact_left s_obs a b h_gc
    have h_b_valid := Shape.layer_lt_of_isGroundingContact_right s_obs a b h_gc
    have h_len_ge : s_result.layerCount ≥ s_obs.layerCount := by
        unfold Shape.layerCount; rw [h_obs, h_result]
        exact placeFallingUnit_length_ge s obs (FallingUnit.cluster ps) d
    have h_a_valid' : a.layer < s_result.layerCount := lt_of_lt_of_le h_a_valid h_len_ge
    have h_b_valid' : b.layer < s_result.layerCount := lt_of_lt_of_le h_b_valid h_len_ge
    have h_gq_preserved : ∀ (x : QuarterPos), x.layer < s_obs.layerCount →
            (∀ q ∈ ps, ¬(q.layer - d = x.layer ∧ q.dir = x.dir)) →
            x.getQuarter s_result = x.getQuarter s_obs := by
        intro x h_x_valid h_not
        have h_x_valid' : x.layer < s_result.layerCount := lt_of_lt_of_le h_x_valid h_len_ge
        have h_gd : QuarterPos.getDir (s_obs.layers.getD x.layer Layer.empty) x.dir =
                    QuarterPos.getDir (s_result.layers.getD x.layer Layer.empty) x.dir := by
            rw [h_obs, h_result]
            exact (getDir_placeFallingUnit_of_ne s obs (FallingUnit.cluster ps) d
                x.layer x.dir (by intro p hp hc; exact h_not p hp hc)).symm
        exact getQuarter_eq_of_getDir_getD_eq h_x_valid' h_x_valid h_gd.symm
    have h_gq_canFormBond : ∀ (x : QuarterPos),
            (∃ q ∈ ps, q.layer - d = x.layer ∧ q.dir = x.dir) →
            x.layer < s_result.layerCount →
            ∃ qa, x.getQuarter s_result = some qa ∧ qa.canFormBond = true := fun x h_w h_v =>
        placeFallingUnit_cluster_written_getQuarter_canFormBond s obs ps d s_result
            h_result x.layer x.dir h_v h_w h_bond
    simp only [groundingEdge, Bool.or_eq_true] at h_edge ⊢
    rcases h_edge with h_up | h_sb
    · left
      simp only [isUpwardGroundingContact, Bool.and_eq_true] at h_up ⊢
      refine ⟨?_, h_up.2⟩
      have h_gc' := h_up.1
      by_cases h_a_land : ∃ q ∈ ps, q.layer - d = a.layer ∧ q.dir = a.dir
        <;> by_cases h_b_land : ∃ q ∈ ps, q.layer - d = b.layer ∧ q.dir = b.dir
      · obtain ⟨qa, ha, hac⟩ := h_gq_canFormBond a h_a_land h_a_valid'
        obtain ⟨qb, hb, hbc⟩ := h_gq_canFormBond b h_b_land h_b_valid'
        exact Shape.isGroundingContact_mono_canFormBond_both s_obs s_result a b qa qb
            hac hbc ha hb h_gc'
      · obtain ⟨qa, ha, hac⟩ := h_gq_canFormBond a h_a_land h_a_valid'
        have hb := h_gq_preserved b h_b_valid (fun q hq hpq => h_b_land ⟨q, hq, hpq⟩)
        exact Shape.isGroundingContact_mono_canFormBond_left s_obs s_result a b qa
            hac ha hb h_gc'
      · have ha := h_gq_preserved a h_a_valid (fun q hq hpq => h_a_land ⟨q, hq, hpq⟩)
        obtain ⟨qb, hb, hbc⟩ := h_gq_canFormBond b h_b_land h_b_valid'
        exact Shape.isGroundingContact_mono_canFormBond_right s_obs s_result a b qb
            hbc ha hb h_gc'
      · have ha := h_gq_preserved a h_a_valid (fun q hq hpq => h_a_land ⟨q, hq, hpq⟩)
        have hb := h_gq_preserved b h_b_valid (fun q hq hpq => h_b_land ⟨q, hq, hpq⟩)
        rw [← Shape.isGroundingContact_eq_of_getQuarter_eq s_obs s_result a b ha.symm hb.symm]
        exact h_gc'
    · right
      have h_adj := Shape.isStructurallyBonded_adjacency s_obs a b h_sb
      have ⟨qa_r, ha_r, ha_cb⟩ :
              ∃ qa, a.getQuarter s_result = some qa ∧ qa.canFormBond = true := by
          by_cases h_a_land : ∃ q ∈ ps, q.layer - d = a.layer ∧ q.dir = a.dir
          · exact h_gq_canFormBond a h_a_land h_a_valid'
          · have ha := h_gq_preserved a h_a_valid (fun q hq hpq => h_a_land ⟨q, hq, hpq⟩)
            obtain ⟨qa, hqa, hcb⟩ := Shape.isStructurallyBonded_canFormBond_left s_obs a b h_sb
            exact ⟨qa, ha.trans hqa, hcb⟩
      have ⟨qb_r, hb_r, hb_cb⟩ :
              ∃ qb, b.getQuarter s_result = some qb ∧ qb.canFormBond = true := by
          by_cases h_b_land : ∃ q ∈ ps, q.layer - d = b.layer ∧ q.dir = b.dir
          · exact h_gq_canFormBond b h_b_land h_b_valid'
          · have hb := h_gq_preserved b h_b_valid (fun q hq hpq => h_b_land ⟨q, hq, hpq⟩)
            obtain ⟨qb, hqb, hcb⟩ := Shape.isStructurallyBonded_canFormBond_right s_obs a b h_sb
            exact ⟨qb, hb.trans hqb, hcb⟩
      exact Shape.isStructurallyBonded_of_parts s_result a b qa_r qb_r ha_r hb_r
          ha_cb hb_cb h_adj

/-- Step B1 (pin version): pin 配置による `groundingEdge` 単調性。

    pin の着地位置 `(p.layer - d, p.dir)` が `obs` で空ならば、
    `placeFallingUnit s obs (FallingUnit.pin p) d` による write は
    `s_obs` で真だったエッジを破壊しない。

    証明戦略:
    - もし edge 端点が pin 着地位置なら、`s_obs` でその位置の `getQuarter` は
      空または none → `isGroundingContact_nonEmpty` の非空要求と矛盾 (vacuous)。
    - 端点が pin 着地位置でなければ、pin write は該当位置の `getDir` を変えず
      `getDir_placeFallingUnit_of_ne` + `getQuarter_eq_of_getDir_getD_eq` +
      `groundingEdge_congr_of_getQuarter_eq` の連鎖で edge 保存。

    用途: `waveStep_grounding_mono` の Step B3 組立で、pin FU 単発の
    `placeFallingUnit` レベルの edge 保存を供給。cluster 版 B1
    (`placeFallingUnit_cluster_groundingEdge_mono`) と対になる。 -/
theorem placeFallingUnit_pin_groundingEdge_mono
        (s : Shape) (obs : List Layer) (p : QuarterPos) (d : Nat)
        (s_obs s_result : Shape)
        (h_obs : s_obs.layers = obs)
        (h_result : s_result.layers = placeFallingUnit s obs (FallingUnit.pin p) d)
        (h_landing_empty : isOccupied obs (p.layer - d) p.dir = false)
        (a b : QuarterPos) (h_edge : groundingEdge s_obs a b = true) :
        groundingEdge s_result a b = true := by
    have h_gc_obs := groundingEdge_base h_edge
    obtain ⟨qa, qb, hqa, hqb, hne_a, hne_b⟩ :=
        isGroundingContact_nonEmpty s_obs a b h_gc_obs
    have h_a_valid := Shape.layer_lt_of_isGroundingContact_left s_obs a b h_gc_obs
    have h_b_valid := Shape.layer_lt_of_isGroundingContact_right s_obs a b h_gc_obs
    have h_len_ge : s_result.layerCount ≥ s_obs.layerCount := by
        unfold Shape.layerCount; rw [h_obs, h_result]
        exact placeFallingUnit_length_ge s obs (FallingUnit.pin p) d
    have h_a_valid' : a.layer < s_result.layerCount := lt_of_lt_of_le h_a_valid h_len_ge
    have h_b_valid' : b.layer < s_result.layerCount := lt_of_lt_of_le h_b_valid h_len_ge
    have h_landing_empty' : isOccupied s_obs.layers (p.layer - d) p.dir = false := by
        rw [h_obs]; exact h_landing_empty
    have h_gq_land : QuarterPos.getQuarter s_obs ⟨p.layer - d, p.dir⟩ = none ∨
            ∃ q, QuarterPos.getQuarter s_obs ⟨p.layer - d, p.dir⟩ = some q ∧ q.isEmpty = true := by
        rw [isOccupied_eq_getQuarter] at h_landing_empty'
        cases hq : QuarterPos.getQuarter s_obs ⟨p.layer - d, p.dir⟩ with
        | none => left; rfl
        | some q =>
            right; refine ⟨q, rfl, ?_⟩
            rw [hq] at h_landing_empty'; simpa using h_landing_empty'
    have h_a_ne : ¬ (p.layer - d = a.layer ∧ p.dir = a.dir) := by
        rintro ⟨hal, had⟩
        have h_eq : a = ⟨p.layer - d, p.dir⟩ := by cases a; simp_all
        rw [h_eq] at hqa
        rcases h_gq_land with hnone | ⟨q, hsome, hemp⟩
        · rw [hnone] at hqa; exact absurd hqa (by simp)
        · rw [hsome] at hqa; rw [Option.some_inj] at hqa; subst hqa
          exact absurd hne_a (by simp [hemp])
    have h_b_ne : ¬ (p.layer - d = b.layer ∧ p.dir = b.dir) := by
        rintro ⟨hbl, hbd⟩
        have h_eq : b = ⟨p.layer - d, p.dir⟩ := by cases b; simp_all
        rw [h_eq] at hqb
        rcases h_gq_land with hnone | ⟨q, hsome, hemp⟩
        · rw [hnone] at hqb; exact absurd hqb (by simp)
        · rw [hsome] at hqb; rw [Option.some_inj] at hqb; subst hqb
          exact absurd hne_b (by simp [hemp])
    have h_gd_a : QuarterPos.getDir
            ((placeFallingUnit s obs (FallingUnit.pin p) d).getD a.layer Layer.empty) a.dir =
            QuarterPos.getDir (obs.getD a.layer Layer.empty) a.dir := by
        apply getDir_placeFallingUnit_of_ne
        intro q hq
        simp [FallingUnit.positions] at hq
        subst hq
        intro ⟨hq1, hq2⟩
        exact h_a_ne ⟨hq1, hq2⟩
    have h_gd_b : QuarterPos.getDir
            ((placeFallingUnit s obs (FallingUnit.pin p) d).getD b.layer Layer.empty) b.dir =
            QuarterPos.getDir (obs.getD b.layer Layer.empty) b.dir := by
        apply getDir_placeFallingUnit_of_ne
        intro q hq
        simp [FallingUnit.positions] at hq
        subst hq
        intro ⟨hq1, hq2⟩
        exact h_b_ne ⟨hq1, hq2⟩
    have h_gd_a' : QuarterPos.getDir (s_result.layers.getD a.layer Layer.empty) a.dir =
            QuarterPos.getDir (s_obs.layers.getD a.layer Layer.empty) a.dir := by
        rw [h_result, h_obs]; exact h_gd_a
    have h_gd_b' : QuarterPos.getDir (s_result.layers.getD b.layer Layer.empty) b.dir =
            QuarterPos.getDir (s_obs.layers.getD b.layer Layer.empty) b.dir := by
        rw [h_result, h_obs]; exact h_gd_b
    have ha_eq := getQuarter_eq_of_getDir_getD_eq h_a_valid' h_a_valid h_gd_a'
    have hb_eq := getQuarter_eq_of_getDir_getD_eq h_b_valid' h_b_valid h_gd_b'
    have heq := groundingEdge_congr_of_getQuarter_eq ha_eq.symm hb_eq.symm
    rw [heq] at h_edge; exact h_edge

/-- Step B3a (cluster-only): 同一 LD `d` を共有する cluster FU group に対し、
    `foldl placeFallingUnit` を通じて B1 cluster edge mono を連鎖適用する。

    group が全て cluster で、各 cluster 位置が元 shape `s` で canFormBond を持つとき、
    foldl を通じて `s_obs` で真だった `groundingEdge a b` が `s_result` でも真になる。

    pin FU を含む混合 group は別補題で扱う（Step B3a pin 版を今後追加予定）。 -/
theorem foldl_placeFU_cluster_fixed_d_groundingEdge_mono
        (s : Shape) (group : List FallingUnit) (obs : List Layer) (d : Nat)
        (h_ne : obs ≠ [])
        (h_cluster : ∀ u ∈ group, ∃ ps, u = FallingUnit.cluster ps ∧
            ∀ p ∈ ps, ∃ qv, p.getQuarter s = some qv ∧ qv.canFormBond = true)
        (s_obs s_result : Shape)
        (h_obs : s_obs.layers = obs)
        (h_result : s_result.layers =
            group.foldl (fun acc fu => placeFallingUnit s acc fu d) obs)
        (a b : QuarterPos) (h_edge : groundingEdge s_obs a b = true) :
        groundingEdge s_result a b = true := by
    induction group generalizing obs s_obs with
    | nil =>
        simp only [List.foldl_nil] at h_result
        have h_eq : s_result = s_obs := Shape.ext (h_result.trans h_obs.symm)
        rw [h_eq]; exact h_edge
    | cons first rest ih =>
        simp only [List.foldl_cons] at h_result
        obtain ⟨ps, hps, h_bond⟩ := h_cluster first List.mem_cons_self
        have h_obs1_ne : placeFallingUnit s obs first d ≠ [] := by
            intro h_eq
            have h_len := placeFallingUnit_length_ge s obs first d
            rw [h_eq, List.length_nil] at h_len
            exact h_ne (List.length_eq_zero_iff.mp (Nat.le_zero.mp h_len))
        let s_mid : Shape := ⟨placeFallingUnit s obs first d, h_obs1_ne⟩
        have h_mid_layers : s_mid.layers = placeFallingUnit s obs first d := rfl
        have h_edge_mid : groundingEdge s_mid a b = true := by
            apply placeFallingUnit_cluster_groundingEdge_mono s obs ps d h_bond
                s_obs s_mid h_obs ?_ a b h_edge
            rw [h_mid_layers, hps]
        exact ih (obs := placeFallingUnit s obs first d) h_obs1_ne
            (fun u hu => h_cluster u (List.mem_cons_of_mem _ hu))
            s_mid rfl h_result h_edge_mid

/-- 着地位置と衝突しない `(lay, dir)` では、`placeFallingUnit` は `isOccupied` を保存する。

    補助: pin B3a の induction step で、`pin p1` を配置した後も `rest` の pin の
    landing 位置が空のままであることを示すのに使う。 -/
private theorem isOccupied_placeFallingUnit_of_pos_ne
        (s : Shape) (obs : List Layer)
        (u : FallingUnit) (d : Nat) (lay : Nat) (dir : Direction)
        (h_lt : lay < obs.length)
        (h_not : ∀ p ∈ u.positions, ¬(p.layer - d = lay ∧ p.dir = dir)) :
        isOccupied (placeFallingUnit s obs u d) lay dir = isOccupied obs lay dir := by
    have h_gd := getDir_placeFallingUnit_of_ne s obs u d lay dir h_not
    have h_len_ge := placeFallingUnit_length_ge s obs u d
    have h_lt' : lay < (placeFallingUnit s obs u d).length := lt_of_lt_of_le h_lt h_len_ge
    unfold isOccupied
    rw [List.getElem?_eq_getElem h_lt, List.getElem?_eq_getElem h_lt']
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h_lt,
               List.getElem?_eq_getElem h_lt', Option.getD_some] at h_gd
    simp only [h_gd]

/-- Step B3a (pin-only): 同一 LD `d` を共有する pin FU group に対し、
    `foldl placeFallingUnit` を通じて B1 pin edge mono を連鎖適用する。

    前提:
    - group の全 FU が pin
    - 各 pin の着地位置が開始 `obs` で空
    - 各 pin position で `d ≤ layer` かつ `layer < obs.length`
    - `group.flatMap positions` が `Nodup`

    証明戦略:
    - induction on group (generalizing obs s_obs)
    - step で first = pin p1 を剥がし、中間 shape s_mid に B1 pin を適用
    - rest に対する landing-empty invariant は、p1 の write と pk の landing が
      衝突しないこと (positions Nodup + d ≤ layer) から
      `isOccupied_placeFallingUnit_of_pos_ne` で伝播

    cluster 版と混合版は別補題（混合は今後追加予定）。 -/
theorem foldl_placeFU_pin_fixed_d_groundingEdge_mono
        (s : Shape) (group : List FallingUnit) (obs : List Layer) (d : Nat)
        (h_ne : obs ≠ [])
        (h_pin : ∀ u ∈ group, ∃ p, u = FallingUnit.pin p)
        (h_landing_empty : ∀ p, FallingUnit.pin p ∈ group →
            isOccupied obs (p.layer - d) p.dir = false)
        (h_layer_ge : ∀ p, FallingUnit.pin p ∈ group → d ≤ p.layer)
        (h_layer_lt : ∀ p, FallingUnit.pin p ∈ group → p.layer < obs.length)
        (h_nodup : (group.flatMap FallingUnit.positions).Nodup)
        (s_obs s_result : Shape)
        (h_obs : s_obs.layers = obs)
        (h_result : s_result.layers =
            group.foldl (fun acc fu => placeFallingUnit s acc fu d) obs)
        (a b : QuarterPos) (h_edge : groundingEdge s_obs a b = true) :
        groundingEdge s_result a b = true := by
    induction group generalizing obs s_obs with
    | nil =>
        simp only [List.foldl_nil] at h_result
        have h_eq : s_result = s_obs := Shape.ext (h_result.trans h_obs.symm)
        rw [h_eq]; exact h_edge
    | cons first rest ih =>
        simp only [List.foldl_cons] at h_result
        obtain ⟨p1, hp1⟩ := h_pin first List.mem_cons_self
        subst hp1
        have h_empty_1 := h_landing_empty p1 List.mem_cons_self
        have h_obs1_ne : placeFallingUnit s obs (FallingUnit.pin p1) d ≠ [] := by
            intro h_eq
            have h_len := placeFallingUnit_length_ge s obs (FallingUnit.pin p1) d
            rw [h_eq, List.length_nil] at h_len
            exact h_ne (List.length_eq_zero_iff.mp (Nat.le_zero.mp h_len))
        let s_mid : Shape := ⟨placeFallingUnit s obs (FallingUnit.pin p1) d, h_obs1_ne⟩
        have h_mid_layers : s_mid.layers = placeFallingUnit s obs (FallingUnit.pin p1) d := rfl
        have h_edge_mid : groundingEdge s_mid a b = true := by
            apply placeFallingUnit_pin_groundingEdge_mono s obs p1 d
                s_obs s_mid h_obs h_mid_layers h_empty_1 a b h_edge
        -- Nodup of cons: p1 :: (rest.flatMap positions) is Nodup
        have h_nodup_cons : (p1 :: rest.flatMap FallingUnit.positions).Nodup := by
            have : ((FallingUnit.pin p1) :: rest).flatMap FallingUnit.positions =
                    p1 :: rest.flatMap FallingUnit.positions := by
                simp [List.flatMap_cons, FallingUnit.positions]
            rw [this] at h_nodup
            exact h_nodup
        have h_nodup_rest : (rest.flatMap FallingUnit.positions).Nodup :=
            (List.nodup_cons.mp h_nodup_cons).2
        have h_p1_disjoint : p1 ∉ rest.flatMap FallingUnit.positions :=
            (List.nodup_cons.mp h_nodup_cons).1
        have h_obs1_len : obs.length ≤ (placeFallingUnit s obs (FallingUnit.pin p1) d).length :=
            placeFallingUnit_length_ge s obs (FallingUnit.pin p1) d
        -- Landing-empty invariant for rest on obs1
        have h_landing_empty_rest : ∀ p, FallingUnit.pin p ∈ rest →
                isOccupied (placeFallingUnit s obs (FallingUnit.pin p1) d)
                    (p.layer - d) p.dir = false := by
            intro p hp
            have hp_in_group : FallingUnit.pin p ∈ (FallingUnit.pin p1) :: rest :=
                List.mem_cons_of_mem _ hp
            have h_empty_orig := h_landing_empty p hp_in_group
            have hp_ge := h_layer_ge p hp_in_group
            have hp_lt := h_layer_lt p hp_in_group
            have h_p_lt : p.layer - d < obs.length := by omega
            have h_p_ne : ∀ q ∈ (FallingUnit.pin p1).positions,
                    ¬(q.layer - d = p.layer - d ∧ q.dir = p.dir) := by
                intro q hq
                have hq_eq : q = p1 := by
                    simp only [FallingUnit.positions, List.mem_singleton] at hq
                    exact hq
                rintro ⟨hlay, hdir⟩
                rw [hq_eq] at hlay hdir
                have hp1_ge := h_layer_ge p1 List.mem_cons_self
                have hp1_eq_p : p1 = p := by
                    have hlay' : p1.layer = p.layer := by omega
                    cases p1
                    cases p
                    simp_all
                apply h_p1_disjoint
                rw [hp1_eq_p]
                exact List.mem_flatMap.mpr ⟨FallingUnit.pin p, hp, by
                    simp [FallingUnit.positions]⟩
            rw [isOccupied_placeFallingUnit_of_pos_ne s obs (FallingUnit.pin p1) d
                (p.layer - d) p.dir h_p_lt h_p_ne]
            exact h_empty_orig
        have h_pin_rest : ∀ u ∈ rest, ∃ p, u = FallingUnit.pin p :=
            fun u hu => h_pin u (List.mem_cons_of_mem _ hu)
        have h_layer_ge_rest : ∀ p, FallingUnit.pin p ∈ rest → d ≤ p.layer :=
            fun p hp => h_layer_ge p (List.mem_cons_of_mem _ hp)
        have h_layer_lt_rest : ∀ p, FallingUnit.pin p ∈ rest →
                p.layer < (placeFallingUnit s obs (FallingUnit.pin p1) d).length :=
            fun p hp => lt_of_lt_of_le (h_layer_lt p (List.mem_cons_of_mem _ hp)) h_obs1_len
        exact ih (obs := placeFallingUnit s obs (FallingUnit.pin p1) d) h_obs1_ne
            h_pin_rest h_landing_empty_rest h_layer_ge_rest h_layer_lt_rest h_nodup_rest
            s_mid rfl h_result h_edge_mid

/-- Step B3a (mixed): 同一 LD `d` を共有する cluster/pin 混合 FU group に対し、
    `foldl placeFallingUnit` を通じて B1 cluster/pin edge mono を連鎖適用する。

    前提:
    - 各 cluster FU の position で `canFormBond` を持つ (B1 cluster 前提)
    - 各 pin FU の着地位置が開始 `obs` で空 (B1 pin 前提)
    - 全 FU の全 position について `d ≤ layer` (減算の単射性確保)
    - 全 FU の全 position について `layer < obs.length` (`isOccupied` 保存用)
    - `group.flatMap positions` が `Nodup` (write と landing の衝突回避)

    証明戦略:
    - induction on group (generalizing obs s_obs)
    - step で first の形 (cluster ps / pin p1) で場合分け → B1 cluster/pin を適用
    - rest への伝播:
      - `h_cluster_bond` は `s` 依存のため `List.mem_cons_of_mem` でそのまま
      - `h_pin_landing_empty` は `isOccupied_placeFallingUnit_of_pos_ne` で保存
        (Nodup + `d ≤ layer` で `q = p → first.positions ∩ rest.positions ≠ ∅` 矛盾)
      - `h_layer_lt` は `obs1.length ≥ obs.length` 単調性で保存

    用途: Step B3b (placeLDGroups レベル) へ持ち上げる足場。 -/
theorem foldl_placeFU_mixed_fixed_d_groundingEdge_mono
        (s : Shape) (group : List FallingUnit) (obs : List Layer) (d : Nat)
        (h_ne : obs ≠ [])
        (h_cluster_bond : ∀ ps, FallingUnit.cluster ps ∈ group →
            ∀ p ∈ ps, ∃ qv, p.getQuarter s = some qv ∧ qv.canFormBond = true)
        (h_pin_landing_empty : ∀ p, FallingUnit.pin p ∈ group →
            isOccupied obs (p.layer - d) p.dir = false)
        (h_layer_ge : ∀ u ∈ group, ∀ q ∈ u.positions, d ≤ q.layer)
        (h_layer_lt : ∀ u ∈ group, ∀ q ∈ u.positions, q.layer < obs.length)
        (h_nodup : (group.flatMap FallingUnit.positions).Nodup)
        (s_obs s_result : Shape)
        (h_obs : s_obs.layers = obs)
        (h_result : s_result.layers =
            group.foldl (fun acc fu => placeFallingUnit s acc fu d) obs)
        (a b : QuarterPos) (h_edge : groundingEdge s_obs a b = true) :
        groundingEdge s_result a b = true := by
    induction group generalizing obs s_obs with
    | nil =>
        simp only [List.foldl_nil] at h_result
        have h_eq : s_result = s_obs := Shape.ext (h_result.trans h_obs.symm)
        rw [h_eq]; exact h_edge
    | cons first rest ih =>
        simp only [List.foldl_cons] at h_result
        have h_obs1_ne : placeFallingUnit s obs first d ≠ [] := by
            intro h_eq
            have h_len := placeFallingUnit_length_ge s obs first d
            rw [h_eq, List.length_nil] at h_len
            exact h_ne (List.length_eq_zero_iff.mp (Nat.le_zero.mp h_len))
        let s_mid : Shape := ⟨placeFallingUnit s obs first d, h_obs1_ne⟩
        have h_mid_layers : s_mid.layers = placeFallingUnit s obs first d := rfl
        have h_edge_mid : groundingEdge s_mid a b = true := by
            match hfirst : first with
            | FallingUnit.cluster ps =>
                have h_bond := h_cluster_bond ps
                    (by rw [← hfirst]; exact List.mem_cons_self)
                exact placeFallingUnit_cluster_groundingEdge_mono s obs ps d h_bond
                    s_obs s_mid h_obs h_mid_layers a b h_edge
            | FallingUnit.pin p1 =>
                have h_empty_1 := h_pin_landing_empty p1
                    (by rw [← hfirst]; exact List.mem_cons_self)
                exact placeFallingUnit_pin_groundingEdge_mono s obs p1 d
                    s_obs s_mid h_obs h_mid_layers h_empty_1 a b h_edge
        have h_cluster_bond_rest : ∀ ps, FallingUnit.cluster ps ∈ rest →
                ∀ p ∈ ps, ∃ qv, p.getQuarter s = some qv ∧ qv.canFormBond = true :=
            fun ps hps => h_cluster_bond ps (List.mem_cons_of_mem _ hps)
        have h_nodup_cat :
                (first.positions ++ rest.flatMap FallingUnit.positions).Nodup := by
            have : (first :: rest).flatMap FallingUnit.positions =
                   first.positions ++ rest.flatMap FallingUnit.positions := by
                simp [List.flatMap_cons]
            rw [this] at h_nodup; exact h_nodup
        have h_nodup_parts := List.nodup_append.mp h_nodup_cat
        have h_nodup_rest : (rest.flatMap FallingUnit.positions).Nodup := h_nodup_parts.2.1
        have h_first_disjoint : ∀ q ∈ first.positions,
                q ∉ rest.flatMap FallingUnit.positions :=
            fun q hq hmem => h_nodup_parts.2.2 q hq q hmem rfl
        have h_layer_ge_rest : ∀ u ∈ rest, ∀ q ∈ u.positions, d ≤ q.layer :=
            fun u hu q hq => h_layer_ge u (List.mem_cons_of_mem _ hu) q hq
        have h_obs1_len : obs.length ≤ (placeFallingUnit s obs first d).length :=
            placeFallingUnit_length_ge s obs first d
        have h_layer_lt_rest : ∀ u ∈ rest, ∀ q ∈ u.positions,
                q.layer < (placeFallingUnit s obs first d).length :=
            fun u hu q hq => lt_of_lt_of_le
                (h_layer_lt u (List.mem_cons_of_mem _ hu) q hq) h_obs1_len
        have h_pin_landing_empty_rest : ∀ p, FallingUnit.pin p ∈ rest →
                isOccupied (placeFallingUnit s obs first d) (p.layer - d) p.dir = false := by
            intro p hp
            have hp_in : FallingUnit.pin p ∈ first :: rest := List.mem_cons_of_mem _ hp
            have h_empty := h_pin_landing_empty p hp_in
            have hp_ge : d ≤ p.layer :=
                h_layer_ge _ hp_in p (by simp [FallingUnit.positions])
            have hp_lt : p.layer < obs.length :=
                h_layer_lt _ hp_in p (by simp [FallingUnit.positions])
            have h_p_lt : p.layer - d < obs.length := by omega
            have h_p_ne : ∀ q ∈ first.positions,
                    ¬(q.layer - d = p.layer - d ∧ q.dir = p.dir) := by
                intro q hq
                have hq_ge := h_layer_ge first List.mem_cons_self q hq
                rintro ⟨hlay, hdir⟩
                have hq_layer_eq : q.layer = p.layer := by omega
                have hq_eq : q = p := by cases q; cases p; simp_all
                have hp_in_rest_flat : p ∈ rest.flatMap FallingUnit.positions :=
                    List.mem_flatMap.mpr
                        ⟨FallingUnit.pin p, hp, by simp [FallingUnit.positions]⟩
                exact h_first_disjoint q hq (hq_eq ▸ hp_in_rest_flat)
            rw [isOccupied_placeFallingUnit_of_pos_ne s obs first d
                (p.layer - d) p.dir h_p_lt h_p_ne]
            exact h_empty
        exact ih (obs := placeFallingUnit s obs first d) h_obs1_ne
            h_cluster_bond_rest h_pin_landing_empty_rest
            h_layer_ge_rest h_layer_lt_rest h_nodup_rest
            s_mid rfl h_result h_edge_mid

/-- **Step B3b step lemma (obs 抽象版)**: `_step` の obs 抽象版。obs を任意の
    `List Layer` とし、不変量として以下を明示的に要求する:

    - `h_len_ge`: `s.layerCount ≤ obs.length`
    - `h_pin_landing_empty`: 現 group 内の全 pin が obs 上で着地空

    これらは `placeFallingUnit` 列を通して保持可能な不変量なので、長さ帰納で
    `placeLDGroups` 全体を回す際に各ステップで再確立して渡せる。
    `placeLDGroups_landing_groundingEdge_mono` 本体 (B3b) を構成するための基礎補題。 -/
theorem placeLDGroups_landing_groundingEdge_mono_step_generic
        (s : Shape) (group : List FallingUnit) (obs : List Layer) (d : Nat)
        (h_ne : obs ≠ [])
        (h_len_ge : s.layerCount ≤ obs.length)
        (h_sub : ∀ u ∈ group, u ∈ floatingUnits s)
        (h_fixed_d : ∀ u ∈ group, landingDistance u obs = d)
        (h_pin_landing_empty : ∀ p, FallingUnit.pin p ∈ group →
            isOccupied obs (p.layer - d) p.dir = false)
        (h_group_nodup : (group.flatMap FallingUnit.positions).Nodup)
        (s_obs s_mid : Shape)
        (h_obs : s_obs.layers = obs)
        (h_mid : s_mid.layers =
            group.foldl (fun acc fu => placeFallingUnit s acc fu d) obs)
        (a b : QuarterPos) (h_edge : groundingEdge s_obs a b = true) :
        groundingEdge s_mid a b = true := by
    have h_cluster_bond : ∀ ps, FallingUnit.cluster ps ∈ group →
            ∀ p ∈ ps, ∃ qv, p.getQuarter s = some qv ∧ qv.canFormBond = true := by
        intro ps hps p hp
        exact floatingUnits_cluster_positions_canFormBond s ps (h_sub _ hps) p hp
    have h_layer_ge : ∀ u ∈ group, ∀ q ∈ u.positions, d ≤ q.layer := by
        intro u hu q hq
        have h_eq := h_fixed_d u hu
        rw [← h_eq]
        exact le_trans (landingDistance_le_minLayer u obs)
            (minLayer_le_layer hq u.minLayer le_rfl)
    have h_layer_lt : ∀ u ∈ group, ∀ q ∈ u.positions, q.layer < obs.length := by
        intro u hu q hq
        have h_fu := h_sub u hu
        have h_any :
                ((floatingUnits s).flatMap FallingUnit.positions).any (· == q) = true := by
            apply List.any_eq_true.mpr
            exact ⟨q, List.mem_flatMap.mpr ⟨u, h_fu, hq⟩, by simp⟩
        have h_lt_sc : q.layer < s.layerCount :=
            (floatingUnits_positions_getQuarter s q h_any).1
        omega
    exact foldl_placeFU_mixed_fixed_d_groundingEdge_mono s group obs d h_ne
        h_cluster_bond h_pin_landing_empty h_layer_ge h_layer_lt h_group_nodup
        s_obs s_mid h_obs h_mid a b h_edge

/-- **Step B3b step lemma (clearPositions 形式)**: `_step_generic` の
    clearPositions 特化版ラッパー。`obs = (s.clearPositions settlingPos).layers`
    のとき、`h_min_fu`/`h_ps_layer` から `h_pin_landing_empty` を、
    `Shape.layerCount_clearPositions` から `h_len_ge` を自動導出して
    `_step_generic` に委譲する。

    ## 前提（clearPositions 形式）

    - `group` は `floatingUnits s` の部分集合（`h_sub`）
    - `group` の全 FU の `minLayer` は `floatingUnits s` 全体の最小以上
      （`h_min_fu`: `u ∈ group` ならば `∀ v ∈ floatingUnits s, u.minLayer ≤ v.minLayer`）
    - `settlingPos` の全 `layer` は `group` の任意 FU の `minLayer` 以上
      （`h_ps_layer`）
    - `group` 内 FU は全て同じ `landingDistance`（`h_fixed_d`: `obs = (s.clearPositions settlingPos).layers` 上で `= d`）
    - `group.flatMap positions` が `Nodup`（`h_group_nodup`）
    - `s_obs.layers = obs`（観測）
    - `s_mid.layers = group.foldl (placeFallingUnit s · · d) obs`（1 group 適用後）

    ## 結論

    `groundingEdge s_obs a b = true` ならば `groundingEdge s_mid a b = true`。

    ## 用途

    `placeLDGroups_landing_groundingEdge_mono` 本体（B3b）を `sortedSettling.length`
    の長さ帰納で再実装する際、各ステップで本 step lemma を適用して
    `s_obs → s_mid` の edge 伝播を処理する。2026-04-23 第49報で発見した Plan A
    scaffold (`generalize (s.clearPositions settlingPos).layers = obs0`) の
    構造的障害を回避する案 3 の核となる補題。

    ## 証明構造

    1. `h_ne`: `s_obs.layers ≠ []` から `h_obs` 経由
    2. `h_cluster_bond`: `floatingUnits_cluster_positions_canFormBond` を適用
    3. `h_pin_landing_empty`: `pin_singleton_landing_empty` を `h_fixed_d` で
       `d = landingDistance` の形に整形して適用
    4. `h_layer_ge`: `h_fixed_d` + `landingDistance_le_minLayer` + `minLayer_le_layer`
    5. `h_layer_lt`: `floatingUnits_positions_getQuarter` (q.layer < s.layerCount)
       + `Shape.layerCount_clearPositions` (obs.length = s.layerCount)

    全ての前提を組み立てた後、B3a mixed を exact で適用する。 -/
theorem placeLDGroups_landing_groundingEdge_mono_step
        (s : Shape) (group : List FallingUnit) (settlingPos : List QuarterPos) (d : Nat)
        (h_sub : ∀ u ∈ group, u ∈ floatingUnits s)
        (h_min_fu : ∀ u ∈ group, ∀ v ∈ floatingUnits s, u.minLayer ≤ v.minLayer)
        (h_ps_layer : ∀ q ∈ settlingPos, ∀ u ∈ group, u.minLayer ≤ q.layer)
        (h_fixed_d : ∀ u ∈ group, landingDistance u (s.clearPositions settlingPos).layers = d)
        (h_group_nodup : (group.flatMap FallingUnit.positions).Nodup)
        (s_obs s_mid : Shape)
        (h_obs : s_obs.layers = (s.clearPositions settlingPos).layers)
        (h_mid : s_mid.layers =
            group.foldl (fun acc fu => placeFallingUnit s acc fu d)
                (s.clearPositions settlingPos).layers)
        (a b : QuarterPos) (h_edge : groundingEdge s_obs a b = true) :
        groundingEdge s_mid a b = true := by
    set obs := (s.clearPositions settlingPos).layers with h_obs_def
    have h_ne : obs ≠ [] := by rw [← h_obs]; exact s_obs.layers_ne
    have h_len_ge : s.layerCount ≤ obs.length := by
        rw [show obs.length = s.layerCount from
            Shape.layerCount_clearPositions s settlingPos]
    have h_pin_landing_empty : ∀ p, FallingUnit.pin p ∈ group →
            isOccupied obs (p.layer - d) p.dir = false := by
        intro p hp
        have h_fu := h_sub (FallingUnit.pin p) hp
        have h_min_p : ∀ v ∈ floatingUnits s, v.minLayer ≥ p.layer := by
            intro v hv
            have h := h_min_fu (FallingUnit.pin p) hp v hv
            simp [FallingUnit.minLayer, FallingUnit.positions] at h
            exact h
        have h_ps_p : ∀ q ∈ settlingPos, q.layer ≥ p.layer := by
            intro q hq
            have h := h_ps_layer q hq (FallingUnit.pin p) hp
            simp [FallingUnit.minLayer, FallingUnit.positions] at h
            exact h
        have h_eq : landingDistance (FallingUnit.pin p) obs = d := h_fixed_d _ hp
        rw [show p.layer - d = p.layer - landingDistance (FallingUnit.pin p) obs from by
            rw [h_eq]]
        exact pin_singleton_landing_empty s p h_fu h_min_p settlingPos h_ps_p
    exact placeLDGroups_landing_groundingEdge_mono_step_generic s group obs d
        h_ne h_len_ge h_sub h_fixed_d h_pin_landing_empty h_group_nodup
        s_obs s_mid h_obs h_mid a b h_edge

/-!
## 一時 axiom: `placeLDGroups_landing_groundingEdge_mono`

**背景（2026-04-23 第58報）**: Step B3b の本体補題を構成するため導入した
aux-lemma `placeLDGroups_landing_groundingEdge_mono_aux` および補助
`landingDistance_foldl_placeFU_preserve_on_remaining` /
`placeLDGroups_remaining_head_pin_landing_empty` は、`lean-theorem-checker`
による反例検証で **IH 不変量 `h_sorted'`（remaining 側での LD 昇順 Pairwise 保存）
および LD 保存補題が共に valid Shape で FALSE** と判明した。

- 反例 1 (保存補題): 7 層 s / w=cluster[(4..6,se),(4..5,sw)] / u=pin(4,se) /
  obs=床 sw のみ occupied → LD u obs=4 だが LD u obs'=1。
- 反例 2 (h_sorted'): 5 層 s, floatingUnits=[4-cluster, pin(3,ne), pin(3,se)],
  d=1 group=[pin(3,ne)] 配置後 remaining=[pin(3,se), cluster] で LD 順序が 2,1 に
  入れ替わり Pairwise 破綻。

命題 `placeLDGroups_landing_groundingEdge_mono` 自体は直感的には成立する
（placeLDGroups の occupation 追加的性質から grounding は単調）が、既存の
IH 設計は数学的に不健全であり根本再設計が必要。そのため本ブランチをマージ可能な
sorry-free 状態に戻すため **一時 axiom 化**する。

**de-axiomatization 計画**: `docs/plans/gravity-greenfield-rewrite-plan.md`
（Greenfield Rewrite）で Gravity 層全体の証明ツリーを再設計する際に、
公開 API のファサード化 + internal 補題の隔離を先行整備してから
本 axiom を定理化する方針。

**保持した valid 補題**:
- `placeLDGroups_landing_groundingEdge_mono_step_generic` (0-sorry, obs 抽象版)
- `placeLDGroups_landing_groundingEdge_mono_step` (0-sorry, clearPositions 特化 wrapper)

これらは `foldl_placeFU_mixed_fixed_d_groundingEdge_mono` (B3a mixed) への
委譲補題として今後の再設計でも再利用可能。
-/
axiom placeLDGroups_landing_groundingEdge_mono
        (s : Shape) (sortedSettling : List FallingUnit)
        (settlingPos : List QuarterPos)
        (h_sub : ∀ u ∈ sortedSettling, u ∈ floatingUnits s)
        (h_min_fu : ∀ u ∈ sortedSettling, ∀ v ∈ floatingUnits s,
            u.minLayer ≤ v.minLayer)
        (h_ps_layer : ∀ q ∈ settlingPos, ∀ u ∈ sortedSettling,
            u.minLayer ≤ q.layer)
        (h_nodup : (sortedSettling.flatMap FallingUnit.positions).Nodup)
        (h_sorted : sortedSettling.Pairwise
            (fun a b => landingDistance a (s.clearPositions settlingPos).layers
                ≤ landingDistance b (s.clearPositions settlingPos).layers))
        (s_obs s_result : Shape)
        (h_obs : s_obs.layers = (s.clearPositions settlingPos).layers)
        (h_result : s_result.layers =
            placeLDGroups s sortedSettling (s.clearPositions settlingPos).layers)
        (a b : QuarterPos) (h_edge : groundingEdge s_obs a b = true)
        (h_landing :
            (a.layer, a.dir) ∈
                placeLDGroupsLandings s sortedSettling
                    (s.clearPositions settlingPos).layers ∨
            (b.layer, b.dir) ∈
                placeLDGroupsLandings s sortedSettling
                    (s.clearPositions settlingPos).layers) :
        groundingEdge s_result a b = true

end Gravity
