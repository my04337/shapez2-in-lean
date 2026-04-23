-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity

namespace Shape

-- clearPositions 後の接地保存（gravity_IsSettled の補題）
-- ============================================================

-- isGroundingContact_eq_of_getQuarter_eq / groundingEdge_eq_of_getQuarter_eq は
-- S2IL/Operations/Gravity/GroundedMono.lean で public 定義済み（2026-04-21 移設）

/-- clearPositions で position が fus に含まれない場合、getQuarter は保存される -/
theorem getQuarter_clearPositions_of_not_mem
        (s : Shape) (fus : List QuarterPos) (p : QuarterPos)
        (h_valid : p.layer < s.layerCount)
        (h_nf : ¬ (fus.any (· == p) = true)) :
        p.getQuarter (s.clearPositions fus) = p.getQuarter s := by
    rw [QuarterPos.getQuarter_clearPositions s fus p h_valid]
    have hf : (fus.any (· == p)) = false := Bool.eq_false_iff.mpr h_nf
    rw [hf, if_neg (by decide)]

/-- isGroundingContact の端点の layer が有効であること（左側） -/
theorem layer_lt_of_isGroundingContact_left
        (s : Shape) (p1 p2 : QuarterPos)
        (h : Gravity.isGroundingContact s p1 p2 = true) :
        p1.layer < s.layerCount := by
    obtain ⟨q1, _, hq1, _, _, _⟩ := Gravity.isGroundingContact_nonEmpty s p1 p2 h
    unfold QuarterPos.getQuarter at hq1; simp only [Shape.layerCount]
    by_contra h_ge; push Not at h_ge
    have := List.getElem?_eq_none_iff.mpr h_ge; rw [this] at hq1
    exact absurd hq1 (by simp only [reduceCtorEq, not_false_eq_true])

/-- isGroundingContact の端点の layer が有効であること（右側） -/
theorem layer_lt_of_isGroundingContact_right
        (s : Shape) (p1 p2 : QuarterPos)
        (h : Gravity.isGroundingContact s p1 p2 = true) :
        p2.layer < s.layerCount := by
    obtain ⟨_, q2, _, hq2, _, _⟩ := Gravity.isGroundingContact_nonEmpty s p1 p2 h
    unfold QuarterPos.getQuarter at hq2; simp only [Shape.layerCount]
    by_contra h_ge; push Not at h_ge
    have := List.getElem?_eq_none_iff.mpr h_ge; rw [this] at hq2
    exact absurd hq2 (by simp only [reduceCtorEq, not_false_eq_true])

/-- grounded 位置間の GenericReachable パスは clearPositions 後も有効。
    clearPositions で除去されるのは ungrounded 位置のみであるため、
    grounded 位置間の groundingEdge は保存され、BFS 到達可能性も保存される -/
theorem isBondedInLayer_preserves_groundedness
        (s : Shape) {a mid : QuarterPos}
        (h_a_grounded : a ∈ Gravity.groundedPositions s)
        (h_edge : Gravity.groundingEdge s a mid = true) :
        mid ∈ Gravity.groundedPositions s := by
    simp only [Gravity.groundedPositions, List.mem_toFinset] at h_a_grounded ⊢
    have h_a_vis : (Gravity.groundedPositionsList s).any (· == a) = true :=
        (Gravity.any_beq_iff_mem _ _).mpr h_a_grounded
    have h_mid_valid := layer_lt_of_isGroundingContact_right s a mid
        (Gravity.groundingEdge_base h_edge)
    have h_mid_all := (Gravity.allValid_any_iff_layer' s mid).mpr h_mid_valid
    exact ((Gravity.groundedPositionsList_inv s) a h_a_vis mid h_mid_all h_edge).elim
        (fun h => (Gravity.any_beq_iff_mem _ _).mp h)
        (by simp only [List.any, Bool.false_eq_true, IsEmpty.forall_iff])

/-- grounded 位置間の GenericReachable パスは clearPositions 後も有効。
    clearPositions で除去されるのは ungrounded 位置のみであるため、
    grounded 位置間の groundingEdge は保存され、BFS 到達可能性も保存される -/
theorem reachable_preserved_of_grounded
        (s : Shape) (fus : List QuarterPos)
        (h_fus : ∀ q, (fus.any (· == q) = true) → q ∉ Gravity.groundedPositions s)
        {start target : QuarterPos}
        (h_reach : GenericReachable (Gravity.groundingEdge s) start target)
        (h_start_g : start ∈ Gravity.groundedPositions s) :
        GenericReachable (Gravity.groundingEdge (s.clearPositions fus))
            start target := by
    induction h_reach with
    | refl => exact GenericReachable.refl
    | @step a mid b h_edge_ge h_tail ih =>
        have h_edge := Gravity.groundingEdge_base h_edge_ge
        have h_mid_g : mid ∈ Gravity.groundedPositions s :=
            isBondedInLayer_preserves_groundedness s h_start_g h_edge_ge
        -- getQuarter 保存（a, mid とも grounded → fus に含まれない）
        have h_valid_a := layer_lt_of_isGroundingContact_left s a mid h_edge
        have h_valid_mid := layer_lt_of_isGroundingContact_right s a mid h_edge
        have hqa := getQuarter_clearPositions_of_not_mem s fus a h_valid_a
            (fun h => h_fus a h h_start_g)
        have hqm := getQuarter_clearPositions_of_not_mem s fus mid h_valid_mid
            (fun h => h_fus mid h h_mid_g)
        -- groundingEdge 保存（getQuarter 依存のため）
        have h_edge_cleared :
                Gravity.groundingEdge (s.clearPositions fus) a mid = true := by
            rw [← groundingEdge_eq_of_getQuarter_eq _ _ a mid hqa.symm hqm.symm]
            exact h_edge_ge
        exact GenericReachable.step h_edge_cleared (ih h_mid_g)

/-- grounded seed 条件の転送。
    s1 側で有効だった layer0 非空 seed は、getQuarter 保存仮定の下で s2 側でも有効。 -/
theorem groundedSeed_mono
        (s1 s2 : Shape)
        (h_lc : s1.layerCount ≤ s2.layerCount)
        (h_gq : ∀ p : QuarterPos, p.layer < s1.layerCount →
            (∃ q, p.getQuarter s1 = some q ∧ !q.isEmpty = true) →
            p.getQuarter s2 = p.getQuarter s1)
        (seed : QuarterPos)
        (h_seed_mem : seed ∈ (QuarterPos.allValid s1).filter (fun q =>
            q.layer == 0 && match q.getQuarter s1 with
            | some q => !q.isEmpty | none => false)) :
        seed ∈ (QuarterPos.allValid s2).filter (fun q =>
            q.layer == 0 && match q.getQuarter s2 with
            | some q => !q.isEmpty | none => false) := by
    have h_seed_filter := List.mem_filter.mp h_seed_mem
    have h_seed_cond := h_seed_filter.2
    rw [Bool.and_eq_true] at h_seed_cond
    have h_seed_valid : seed.layer < s1.layerCount :=
        (Gravity.allValid_any_iff_layer' s1 seed).mp
            ((Gravity.any_beq_iff_mem _ _).mpr h_seed_filter.1)
    have h_seed_ne : ∃ q, seed.getQuarter s1 = some q ∧ !q.isEmpty = true := by
        cases hgq : seed.getQuarter s1 with
        | none => simp only [hgq] at h_seed_cond; exact absurd h_seed_cond.2 (by decide)
        | some q =>
            refine ⟨q, rfl, ?_⟩
            simp only [hgq, Quarter.isEmpty] at h_seed_cond
            cases q <;> simp_all only [Bool.decide_eq_true, Bool.not_eq_eq_eq_not,
                forall_exists_index, and_imp, List.mem_filter, Bool.true_and, true_and,
                Bool.and_self, and_true, beq_iff_eq, Bool.not_true, Bool.false_eq_true,
                and_false, Bool.not_false, decide_false]
    have h_seed_gq : seed.getQuarter s2 = seed.getQuarter s1 :=
        h_gq seed h_seed_valid h_seed_ne
    apply List.mem_filter.mpr
    constructor
    · exact (Gravity.any_beq_iff_mem _ _).mp
        ((Gravity.allValid_any_iff_layer' s2 seed).mpr (by omega))
    · rw [h_seed_gq]; exact h_seed_filter.2

/-- getQuarter 保存仮定から isGroundingContact の単調性を得る。 -/
theorem isGroundingContact_mono
        (s1 s2 : Shape)
        (h_gq : ∀ p : QuarterPos, p.layer < s1.layerCount →
            (∃ q, p.getQuarter s1 = some q ∧ !q.isEmpty = true) →
            p.getQuarter s2 = p.getQuarter s1) :
        ∀ a b, Gravity.isGroundingContact s1 a b = true →
            Gravity.isGroundingContact s2 a b = true := by
    intro a b h_edge
    obtain ⟨q1, q2, hq1_some, hq2_some, _, _⟩ :=
        Gravity.isGroundingContact_nonEmpty s1 a b h_edge
    have h_a_ne : ∃ q, a.getQuarter s1 = some q ∧ !q.isEmpty = true :=
        ⟨q1, hq1_some, by cases q1 <;> simp_all⟩
    have h_b_ne : ∃ q, b.getQuarter s1 = some q ∧ !q.isEmpty = true :=
        ⟨q2, hq2_some, by cases q2 <;> simp_all⟩
    have h_a_valid : a.layer < s1.layerCount := by
        unfold QuarterPos.getQuarter at hq1_some; simp only [Shape.layerCount]
        by_contra h_ge; push Not at h_ge
        rw [List.getElem?_eq_none_iff.mpr h_ge] at hq1_some
        exact absurd hq1_some (by simp only [reduceCtorEq, not_false_eq_true])
    have h_b_valid : b.layer < s1.layerCount := by
        unfold QuarterPos.getQuarter at hq2_some; simp only [Shape.layerCount]
        by_contra h_ge; push Not at h_ge
        rw [List.getElem?_eq_none_iff.mpr h_ge] at hq2_some
        exact absurd hq2_some (by simp only [reduceCtorEq, not_false_eq_true])
    rw [← isGroundingContact_eq_of_getQuarter_eq s1 s2 a b
        (h_gq a h_a_valid h_a_ne).symm (h_gq b h_b_valid h_b_ne).symm]
    exact h_edge

/-- getQuarter 保存仮定から groundingEdge の単調性を得る。 -/
theorem groundingEdge_mono
        (s1 s2 : Shape)
        (h_gq : ∀ p : QuarterPos, p.layer < s1.layerCount →
            (∃ q, p.getQuarter s1 = some q ∧ !q.isEmpty = true) →
            p.getQuarter s2 = p.getQuarter s1) :
        ∀ a b, Gravity.groundingEdge s1 a b = true →
            Gravity.groundingEdge s2 a b = true := by
    intro a b h
    have h_gc := Gravity.groundingEdge_base h
    obtain ⟨q1, q2, hq1, hq2, _, _⟩ :=
        Gravity.isGroundingContact_nonEmpty s1 a b h_gc
    have h_a_valid : a.layer < s1.layerCount := by
        unfold QuarterPos.getQuarter at hq1; simp only [Shape.layerCount]
        by_contra h_ge; push Not at h_ge
        rw [List.getElem?_eq_none_iff.mpr h_ge] at hq1
        exact absurd hq1 (by simp only [reduceCtorEq, not_false_eq_true])
    have h_b_valid : b.layer < s1.layerCount := by
        unfold QuarterPos.getQuarter at hq2; simp only [Shape.layerCount]
        by_contra h_ge; push Not at h_ge
        rw [List.getElem?_eq_none_iff.mpr h_ge] at hq2
        exact absurd hq2 (by simp only [reduceCtorEq, not_false_eq_true])
    rw [← groundingEdge_eq_of_getQuarter_eq s1 s2 a b
        (h_gq a h_a_valid ⟨q1, hq1, by cases q1 <;> simp_all⟩).symm
        (h_gq b h_b_valid ⟨q2, hq2, by cases q2 <;> simp_all⟩).symm]
    exact h

/-- 非空象限が保存されるとき groundedPositions は単調。
    s2 が s1 の全非空象限を保存する（同じ getQuarter 値）場合、
    s1 で接地していた位置は s2 でも接地している -/
theorem groundedPositions_mono
        (s1 s2 : Shape)
        (h_lc : s1.layerCount ≤ s2.layerCount)
        (h_gq : ∀ p : QuarterPos, p.layer < s1.layerCount →
            (∃ q, p.getQuarter s1 = some q ∧ !q.isEmpty = true) →
            p.getQuarter s2 = p.getQuarter s1) :
        Gravity.groundedPositions s1 ⊆ Gravity.groundedPositions s2 := by
    intro p h_p
    simp only [Gravity.groundedPositions, List.mem_toFinset] at h_p ⊢
    obtain ⟨seed, h_seed_mem, h_reach⟩ := Gravity.groundedPositionsList_sound s1 p
        ((Gravity.any_beq_iff_mem _ _).mpr h_p)
    have h_seed_s2 := groundedSeed_mono s1 s2 h_lc h_gq seed h_seed_mem
    have h_ge_mono := groundingEdge_mono s1 s2 h_gq
    have h_reach_s2 : GenericReachable (Gravity.groundingEdge s2) seed p :=
        h_reach.mono h_ge_mono
    exact (Gravity.any_beq_iff_mem _ _).mp
        (Gravity.groundedPositionsList_complete s2 seed p h_seed_s2 h_reach_s2)

/-- groundedPositions のエッジ単調版は
    S2IL/Operations/Gravity/GroundedMono.lean に移設済み（2026-04-21）。 -/

/-- clearPositions 後の障害物形状で、全非空位置が接地している。
    floatingUnits の位置を除去しても、残った非空位置の接地パスは保存される -/
theorem obstacle_all_grounded (s : Shape)
        (allFallingPos : List QuarterPos)
        (h_perm : List.Perm allFallingPos
            ((Gravity.floatingUnits s).flatMap Gravity.FallingUnit.positions)) :
        ∀ (p : QuarterPos),
        p.layer < (s.clearPositions allFallingPos).layerCount →
        (∃ q, p.getQuarter (s.clearPositions allFallingPos) = some q ∧ !q.isEmpty = true) →
        p ∈ Gravity.groundedPositions (s.clearPositions allFallingPos) := by
    intro p h_valid h_ne_p
    have h_lc := Shape.layerCount_clearPositions s allFallingPos
    have h_valid_s : p.layer < s.layerCount := by omega
    -- p は cleared shape で非空 → p ∉ allFallingPos
    have h_not_falling : ¬ (allFallingPos.any (· == p) = true) := by
        intro h_in_afp
        rw [QuarterPos.getQuarter_clearPositions s allFallingPos p h_valid_s] at h_ne_p
        simp only [h_in_afp, ite_true] at h_ne_p
        obtain ⟨q, hq, hq_ne⟩ := h_ne_p
        exact absurd (Option.some.inj hq ▸ hq_ne) (by decide)
    -- p ∉ (floatingUnits s).flatMap positions
    have h_not_fu : ¬ (((Gravity.floatingUnits s).flatMap
            Gravity.FallingUnit.positions).any (· == p) = true) := by
        intro h_fu
        have : allFallingPos.any (· == p) = true := by
            rw [h_perm.any_eq]; exact h_fu
        exact h_not_falling this
    -- p の getQuarter は s と同じ
    have h_gq_s : p.getQuarter (s.clearPositions allFallingPos) = p.getQuarter s := by
        rw [QuarterPos.getQuarter_clearPositions s allFallingPos p h_valid_s]
        have hf : (allFallingPos.any (· == p)) = false := Bool.eq_false_iff.mpr h_not_falling
        rw [hf, if_neg (by decide)]
    have h_ne_s : ∃ q, p.getQuarter s = some q ∧ !q.isEmpty = true := by
        obtain ⟨q, hq, hq_ne⟩ := h_ne_p
        exact ⟨q, h_gq_s ▸ hq, hq_ne⟩
    -- p は s で grounded
    have h_grounded_s : p ∈ Gravity.groundedPositions s := by
        by_contra h_ug
        exact h_not_fu (Gravity.ungrounded_in_floatingUnits_positions s p h_valid_s h_ne_s h_ug)
    -- reachable path を clearPositions 後に保存
    simp only [Gravity.groundedPositions, List.mem_toFinset] at h_grounded_s ⊢
    obtain ⟨seed, h_seed_mem, h_reach⟩ := Gravity.groundedPositionsList_sound s p
        ((Gravity.any_beq_iff_mem _ _).mpr h_grounded_s)
    have h_seed_filter := List.mem_filter.mp h_seed_mem
    have h_seed_g : seed ∈ Gravity.groundedPositions s := by
        simp only [Gravity.groundedPositions, List.mem_toFinset]
        exact (Gravity.any_beq_iff_mem _ _).mp
            (Gravity.groundedPositionsList_complete s seed seed h_seed_mem GenericReachable.refl)
    -- allFallingPos 内の位置は groundedPositions s に含まれない
    have h_fus_not_grounded : ∀ q, (allFallingPos.any (· == q) = true) →
            q ∉ Gravity.groundedPositions s := by
        intro q h_q_in
        have h_fu : (((Gravity.floatingUnits s).flatMap
                Gravity.FallingUnit.positions).any (· == q)) = true := by
            rw [← h_perm.any_eq]; exact h_q_in
        exact (Gravity.floatingUnits_positions_getQuarter s q h_fu).2.2
    -- BFS path preserved
    have h_reach' := reachable_preserved_of_grounded s allFallingPos
        h_fus_not_grounded h_reach h_seed_g
    -- seed は cleared shape でも有効 seed
    have h_seed_valid_s : seed.layer < s.layerCount :=
        (Gravity.allValid_any_iff_layer' s seed).mp
            ((Gravity.any_beq_iff_mem _ _).mpr h_seed_filter.1)
    have h_seed_not_falling : ¬ (allFallingPos.any (· == seed) = true) :=
        fun h => h_fus_not_grounded seed h h_seed_g
    have h_seed_gq : seed.getQuarter (s.clearPositions allFallingPos) =
            seed.getQuarter s := by
        rw [QuarterPos.getQuarter_clearPositions s allFallingPos seed h_seed_valid_s]
        have hf : (allFallingPos.any (· == seed)) = false :=
            Bool.eq_false_iff.mpr h_seed_not_falling
        rw [hf, if_neg (by decide)]
    have h_seed_s' : seed ∈ (QuarterPos.allValid (s.clearPositions allFallingPos)).filter
            (fun q => q.layer == 0 && match q.getQuarter (s.clearPositions allFallingPos) with
            | some q => !q.isEmpty | none => false) := by
        apply List.mem_filter.mpr
        constructor
        · exact (Gravity.any_beq_iff_mem _ _).mp
            ((Gravity.allValid_any_iff_layer' (s.clearPositions allFallingPos) seed).mpr
                (by rw [h_lc]; exact h_seed_valid_s))
        · rw [h_seed_gq]; exact h_seed_filter.2
    exact (Gravity.any_beq_iff_mem _ _).mp
        (Gravity.groundedPositionsList_complete (s.clearPositions allFallingPos)
            seed p h_seed_s' h_reach')

/-- placeQuarter はリストの長さを減らさない -/
theorem placeQuarter_length_ge (obs : List Layer) (l : Nat) (d : Direction) (q : Quarter) :
        (Gravity.placeQuarter obs l d q).length ≥ obs.length := by
    unfold Gravity.placeQuarter
    split_ifs with h
    · dsimp only
      split <;> simp_all only [List.length_set, ge_iff_le, le_refl]
    · dsimp only
      split
      · simp only [List.length_set, List.length_append, List.length_replicate]; omega
      · simp only [List.length_append, List.length_replicate]; omega

/-- isOccupied = false ↔ getDir(getD).isEmpty = true 変換 -/
lemma isOccupied_false_isEmpty (obs : List Layer) (layer : Nat)
        (dir : Direction)
        (h : Gravity.isOccupied obs layer dir = false) :
        (QuarterPos.getDir (obs.getD layer Layer.empty) dir).isEmpty
            = true := by
    unfold Gravity.isOccupied at h
    simp only [List.getD_eq_getElem?_getD]
    cases h_idx : obs[layer]? with
    | none =>
      simp only [h_idx, Option.getD_none] at h ⊢
      cases dir <;> rfl
    | some l =>
      rw [h_idx] at h
      dsimp only [] at h
      simp only [Option.getD_some]
      cases h_b : (QuarterPos.getDir l dir).isEmpty with
      | false => rw [h_b] at h; exact absurd h (by decide)
      | true => rfl

/-- placeFallingUnit はリストの長さを減らさない -/
theorem placeFallingUnit_length_ge (s : Shape) (obs : List Layer)
        (u : Gravity.FallingUnit) (d : Nat) :
        (Gravity.placeFallingUnit s obs u d).length ≥ obs.length := by
    unfold Gravity.placeFallingUnit
    suffices h : ∀ (ps : List QuarterPos) (acc : List Layer),
        acc.length ≥ obs.length →
        (ps.foldl (fun obs' p =>
            match p.getQuarter s with
            | some q => Gravity.placeQuarter obs' (p.layer - d) p.dir q
            | none => obs') acc).length ≥ obs.length by
      exact h u.positions obs (le_refl _)
    intro ps
    induction ps with
    | nil => intro acc h; simpa only [List.foldl_nil]
    | cons p rest ih =>
      intro acc h_acc
      simp only [List.foldl_cons]
      apply ih
      split
      · calc (Gravity.placeQuarter acc _ _ _).length
            ≥ acc.length := placeQuarter_length_ge _ _ _ _
          _ ≥ obs.length := h_acc
      · exact h_acc

-- ============================================================
-- groundedPositions_placeLDGroups_subset は
-- S2IL/Operations/Gravity/GroundedMono.lean に移設済み（2026-04-21）。
-- ============================================================

end Shape

