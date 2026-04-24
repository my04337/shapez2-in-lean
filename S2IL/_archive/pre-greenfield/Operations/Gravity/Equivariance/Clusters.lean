-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity.Equivariance

/-!
# Gravity Equivariance: クラスタ構造・floatingUnits 詳細・rotateCW・placeLDGroups

`Equivariance.lean` の続き。allStructuralClustersList の位置素性、
floatingUnits の詳細な等変性、S1-aux 補題、rotateCW 等変性チェーン、
placeLDGroups の rotate180 等変性を提供する。
-/

namespace Gravity

open _root_.QuarterPos (getDir_rotate180 getQuarter_rotate180 getQuarter_rotate180_inv)
open _root_.Shape (layers_rotate180 clearPositions_rotate180)

-- ============================================================
-- floatingUnits_isEmpty のヘルパー補題群
-- ============================================================

/-- 接地接触は対称的である -/
theorem isGroundingContact_symm (s : Shape) (p1 p2 : QuarterPos) :
        isGroundingContact s p1 p2 = isGroundingContact s p2 p1 := by
    simp only [isGroundingContact]
    generalize p1.getQuarter s = q1
    generalize p2.getQuarter s = q2
    cases q1 with
    | none => cases q2 <;> rfl
    | some v1 => cases q2 with
        | none => rfl
        | some v2 =>
            dsimp only []
            rw [Bool.and_comm (x := !v1.isEmpty) (y := !v2.isEmpty)]
            congr 1
            have h_match_symm : (match v1, v2 with
                    | .pin, _ | _, .pin => false
                    | _, _ => true : Bool) =
                (match v2, v1 with
                    | .pin, _ | _, .pin => false
                    | _, _ => true : Bool) := by
                cases v1 <;> cases v2 <;> rfl
            rw [BEq.comm (a := p1.layer),
                LayerIndex.verticallyAdjacent_symm p1.layer p2.layer,
                BEq.comm (a := p1.dir),
                Direction.adjacent_symm p1.dir p2.dir]
            -- match 式は cross-file unfold で内部表現が異なるため、直接 cases で解決
            cases v1 <;> cases v2 <;> rfl

/-- GenericReachable の推移律 -/
theorem genericReachable_trans {edge : α → α → Bool}
        (h1 : GenericReachable edge a b) (h2 : GenericReachable edge b c) :
        GenericReachable edge a c := by
    induction h1 with
    | refl => exact h2
    | step h_bond _ ih => exact .step h_bond (ih h2)

/-- 対称エッジでの GenericReachable 逆転 -/
theorem genericReachable_reverse {edge : α → α → Bool}
        (h_symm : ∀ x y, edge x y = edge y x)
        (h : GenericReachable edge a b) :
        GenericReachable edge b a := by
    induction h with
    | refl => exact .refl
    | step h_bond _ ih =>
        exact genericReachable_trans ih (.step (h_symm _ _ ▸ h_bond) .refl)

/-- エッジ述語の包含による GenericReachable の単調性 -/
theorem genericReachable_mono {edge1 edge2 : α → α → Bool}
        (h_sub : ∀ a b, edge1 a b = true → edge2 a b = true)
        (h : GenericReachable edge1 a b) :
        GenericReachable edge2 a b := by
    induction h with
    | refl => exact .refl
    | step h_bond _ ih => exact .step (h_sub _ _ h_bond) ih

/-- groundedPositionsList の BFS 不変条件 -/
theorem groundedPositionsList_inv (s : Shape) :
        GenericBfsInv (groundingEdge s) (QuarterPos.allValid s)
            (groundedPositionsList s) [] := by
    -- 定義を展開するが、rfl 経由で明示的な形式を維持し内部表現の不一致を回避
    have h_def : groundedPositionsList s =
        let allPos := QuarterPos.allValid s
        let seeds := allPos.filter fun p =>
            p.layer == 0 && match p.getQuarter s with | some q => !q.isEmpty | none => false
        let n := s.layerCount * 4
        groundingBfs s allPos [] seeds (n * n + n) := rfl
    rw [h_def]; dsimp only []
    rw [groundingBfs_eq_generic]
    apply genericBfs_invariant_preserved
    · intro v hv; simp only [List.any, Bool.false_eq_true] at hv
    · have h_filter : (QuarterPos.allValid s).filter (fun p =>
          !(([] : List QuarterPos).any (· == p))) = QuarterPos.allValid s :=
          List.filter_eq_self.mpr (by intro x _; simp only [List.any, Bool.not_false])
      simp only [h_filter, allValid_length']
      have := List.length_filter_le (fun p =>
          p.layer == 0 && match p.getQuarter s with
          | some q => !q.isEmpty | none => false) (QuarterPos.allValid s)
      rw [allValid_length' s] at this; omega
    · intro p q h
      exact (allValid_any_iff_layer' s p).mpr
          (isGroundingContact_valid_fst s p q
              (groundingEdge_base h))

/-- allStructuralClustersList は全ての bondable 位置をカバーする -/
theorem allStructuralClustersList_covers (s : Shape) (p : QuarterPos)
        (h_valid : p.layer < s.layerCount)
        (h_bondable : match p.getQuarter s with | some q => q.canFormBond = true | none => False) :
        (allStructuralClustersList s).any (fun c => c.any (· == p)) = true := by
    unfold allStructuralClustersList
    -- p が bondable リストに含まれることを示す
    have h_p_mem : p ∈ (QuarterPos.allValid s).filter (fun pos =>
            match pos.getQuarter s with | some q => q.canFormBond | none => false) := by
        rw [List.mem_filter]
        exact ⟨by
            have h_any := (allValid_any_iff_layer' s p).mpr h_valid
            rw [List.any_eq_true] at h_any
            obtain ⟨x, hx, hxe⟩ := h_any; exact eq_of_beq hxe ▸ hx,
          by revert h_bondable; cases p.getQuarter s with
             | none => intro h; exact h.elim
             | some q => intro h; exact h⟩
    -- foldl 不変条件: p ∈ remaining ∨ acc がカバー → 結果がカバー
    suffices h_inv : ∀ (remaining : List QuarterPos) (acc : List (List QuarterPos)),
        (p ∈ remaining ∨ acc.any (fun c => c.any (· == p)) = true) →
        (remaining.foldl (fun clusters pos =>
            if clusters.any (fun cluster => cluster.any (· == pos)) then clusters
            else clusters ++ [structuralClusterList s pos]) acc).any
            (fun c => c.any (· == p)) = true by
      exact h_inv _ [] (.inl h_p_mem)
    intro remaining acc h_or
    induction remaining generalizing acc with
    | nil => exact h_or.elim (fun h => by cases h) id
    | cons pos rest ih =>
        dsimp only [List.foldl]
        cases h_cov : acc.any (fun cluster => cluster.any (· == pos)) with
        | true =>
            simp only [ite_true]
            exact ih acc (h_or.elim (fun h_mem => by
                cases h_mem with
                | head => exact .inr h_cov
                | tail _ h => exact .inl h) .inr)
        | false =>
            exact ih (acc ++ [structuralClusterList s pos]) (h_or.elim (fun h_mem => by
                cases h_mem with
                | head =>
                    right; rw [List.any_append]
                    simp only [Bool.or_eq_true]
                    right; simp only [List.any_cons, List.any_nil, Bool.or_false]
                    unfold structuralClusterList; rw [structuralBfs_eq_generic]
                    cases hn : s.layerCount with
                    | zero => omega
                    | succ k => exact genericBfs_contains_start _ _ _ _ (Nat.mul_pos (by omega) (by omega))
                | tail _ h => exact .inl h) (fun h => .inr (by
                    rw [List.any_append]; simp only [Bool.or_eq_true]; exact .inl h)))

/-- allStructuralClustersList の各クラスタは structuralClusterList s pos として生成される -/
theorem allStructuralClustersList_is_structuralClusterList (s : Shape) (c : List QuarterPos)
        (hc : c ∈ allStructuralClustersList s) :
        ∃ pos, c = structuralClusterList s pos ∧ pos.layer < s.layerCount ∧
            (∃ q, pos.getQuarter s = some q ∧ q.canFormBond = true) := by
    unfold allStructuralClustersList at hc
    -- foldl 不変条件: acc の全クラスタが structuralClusterList pos の形
    suffices ∀ (remaining : List QuarterPos) (acc : List (List QuarterPos)),
        (∀ c' ∈ acc, ∃ pos, c' = structuralClusterList s pos ∧ pos.layer < s.layerCount ∧
            (∃ q, pos.getQuarter s = some q ∧ q.canFormBond = true)) →
        (∀ pos ∈ remaining, pos.layer < s.layerCount ∧
            (∃ q, pos.getQuarter s = some q ∧ q.canFormBond = true)) →
        c ∈ remaining.foldl (fun clusters pos =>
            if clusters.any (fun cluster => cluster.any (· == pos)) then clusters
            else clusters ++ [structuralClusterList s pos]) acc →
        ∃ pos, c = structuralClusterList s pos ∧ pos.layer < s.layerCount ∧
            (∃ q, pos.getQuarter s = some q ∧ q.canFormBond = true) by
      exact this _ [] (fun _ h => nomatch h) (fun pos h_mem => by
          rw [List.mem_filter] at h_mem
          obtain ⟨h_allValid, h_bond⟩ := h_mem
          refine ⟨(allValid_any_iff_layer' s pos).mp
              (List.any_eq_true.mpr ⟨pos, h_allValid, BEq.rfl⟩), ?_⟩
          cases hq : pos.getQuarter s with
          | none => simp only [hq, Bool.false_eq_true] at h_bond
          | some q =>
              cases q with
              | empty => simp only [hq, Quarter.canFormBond, Bool.false_eq_true] at h_bond
              | pin => simp only [hq, Quarter.canFormBond, Bool.false_eq_true] at h_bond
              | crystal c => exact ⟨.crystal c, rfl, rfl⟩
              | colored r c => exact ⟨.colored r c, rfl, rfl⟩) hc
    intro remaining acc h_inv h_props hc
    induction remaining generalizing acc with
    | nil => exact h_inv c hc
    | cons pos rest ih =>
        dsimp only [List.foldl] at hc
        have h_pos_props := h_props pos (.head _)
        have h_rest_props := fun p hp => h_props p (.tail _ hp)
        cases h_cov : acc.any (fun cluster => cluster.any (· == pos))
        · -- false: pos は新規 → structuralClusterList s pos を追加
          simp only [h_cov] at hc
          exact ih (acc ++ [structuralClusterList s pos])
              (fun c' hc' => by
                  rw [List.mem_append, List.mem_singleton] at hc'
                  cases hc' with
                  | inl h => exact h_inv c' h
                  | inr h => exact ⟨pos, h, h_pos_props⟩) h_rest_props hc
        · -- true: pos は既存 → スキップ
          simp only [h_cov, ite_true] at hc
          exact ih acc h_inv h_rest_props hc

-- ============================================================
-- allStructuralClustersList の位置素性（クラスタ間素性）
-- ============================================================

/-- allStructuralClustersList foldl 不変条件:
    異なるインデックスのクラスタは位置を共有しない -/
theorem allStructuralClustersList_disjoint (s : Shape)
        (i j : Nat) (hi : i < (allStructuralClustersList s).length)
        (hj : j < (allStructuralClustersList s).length) (h_ne : i ≠ j)
        (p : QuarterPos)
        (hp1 : ((allStructuralClustersList s)[i]).any (· == p) = true) :
        ((allStructuralClustersList s)[j]).any (· == p) = false := by
    unfold allStructuralClustersList at hi hj hp1 ⊢
    -- foldl 不変条件:
    -- INV1: 各クラスタは structuralClusterList s pos の形（pos.layer < s.layerCount）
    -- INV2: 位置を共有するインデックスは同一
    suffices ∀ (remaining : List QuarterPos) (acc : List (List QuarterPos)),
        (∀ (k : Nat) (hk : k < acc.length), ∃ pos,
            acc[k] = structuralClusterList s pos ∧ pos.layer < s.layerCount) →
        (∀ (a b : Nat) (ha : a < acc.length) (hb : b < acc.length),
            a ≠ b → ∀ q, acc[a].any (· == q) = true → acc[b].any (· == q) = false) →
        (∀ pos ∈ remaining, pos.layer < s.layerCount) →
        let result := remaining.foldl (fun clusters pos =>
            if clusters.any (fun cluster => cluster.any (· == pos)) then clusters
            else clusters ++ [structuralClusterList s pos]) acc
        ∀ (a b : Nat) (ha : a < result.length) (hb : b < result.length),
            a ≠ b → ∀ q, result[a].any (· == q) = true → result[b].any (· == q) = false by
      exact this _ [] (fun _ hk => absurd hk (by simp only [List.length, Nat.not_lt_zero, not_false_eq_true])) (fun _ _ ha => absurd ha (by simp only [List.length, Nat.not_lt_zero, not_false_eq_true]))
          (fun pos h_mem => by
              rw [List.mem_filter] at h_mem
              exact (allValid_any_iff_layer' s pos).mp
                  (List.any_eq_true.mpr ⟨pos, h_mem.1, BEq.rfl⟩))
          i j hi hj h_ne p hp1
    intro remaining
    induction remaining with
    | nil =>
      intro acc _ h_disj _
      dsimp only [List.foldl]
      exact h_disj
    | cons pos rest ih =>
      intro acc h_inv1 h_disj h_props
      have h_pos_layer := h_props pos (.head _)
      have h_rest_props := fun p hp => h_props p (.tail _ hp)
      dsimp only [List.foldl]
      split <;> rename_i h_cov
      · -- pos は既存クラスタにカバー → スキップ
        exact ih acc h_inv1 h_disj h_rest_props
      · -- pos は新規
        -- pos が既存クラスタに含まれないことの展開
        have h_pos_not_in : ∀ (k : Nat) (hk : k < acc.length),
            acc[k].any (· == pos) = false := by
          intro k hk
          cases h_eq : acc[k].any (· == pos) with
          | false => rfl
          | true =>
            have : acc.any (fun c => c.any (· == pos)) = true :=
                List.any_eq_true.mpr ⟨acc[k], List.getElem_mem hk, h_eq⟩
            rw [this] at h_cov; exact absurd h_cov (by decide)
        -- 新不変条件 1
        have h_inv1' : ∀ (k : Nat) (hk : k < (acc ++ [structuralClusterList s pos]).length),
            ∃ p, (acc ++ [structuralClusterList s pos])[k] = structuralClusterList s p ∧
            p.layer < s.layerCount := by
          intro k hk
          rw [List.length_append, List.length_singleton] at hk
          by_cases hk_lt : k < acc.length
          · rw [List.getElem_append_left hk_lt]; exact h_inv1 k hk_lt
          · have hk_eq : k = acc.length := by omega
            subst hk_eq
            rw [List.getElem_append_right (by omega)]
            exact ⟨pos, by simp only [Nat.sub_self, List.getElem_cons_zero], h_pos_layer⟩
        -- 新不変条件 2: 直接素性
        have h_disj' : ∀ (a b : Nat)
            (ha : a < (acc ++ [structuralClusterList s pos]).length)
            (hb : b < (acc ++ [structuralClusterList s pos]).length),
            a ≠ b → ∀ q, (acc ++ [structuralClusterList s pos])[a].any (· == q) = true →
            (acc ++ [structuralClusterList s pos])[b].any (· == q) = false := by
          intro a b ha hb h_ne_ab q hq_a
          rw [List.length_append, List.length_singleton] at ha hb
          by_cases ha_lt : a < acc.length <;> by_cases hb_lt : b < acc.length
          · -- a, b 共に acc 内
            rw [List.getElem_append_left ha_lt] at hq_a
            rw [List.getElem_append_left hb_lt]
            exact h_disj a b ha_lt hb_lt h_ne_ab q hq_a
          · -- a は acc 内, b は新規クラスタ
            have hb_eq : b = acc.length := by omega
            subst hb_eq
            rw [List.getElem_append_left ha_lt] at hq_a
            rw [List.getElem_append_right (by omega)]
            simp only [Nat.sub_self, List.getElem_cons_zero]
            cases h_nc_q : (structuralClusterList s pos).any (· == q) with
            | false => rfl
            | true =>
              obtain ⟨pos_a, h_eq_a, h_la⟩ := h_inv1 a ha_lt
              rw [h_eq_a] at hq_a
              have h_lc : s.layerCount > 0 := by omega
              have h_pos_in := structuralClusterList_shared_contains_seed
                  s pos_a pos q h_lc hq_a h_nc_q
              rw [← h_eq_a] at h_pos_in
              have h_pos_not := h_pos_not_in a ha_lt
              rw [h_pos_in] at h_pos_not; exact absurd h_pos_not (by decide)
          · -- a は新規クラスタ, b は acc 内
            have ha_eq : a = acc.length := by omega
            subst ha_eq
            rw [List.getElem_append_right (by omega)] at hq_a
            simp only [Nat.sub_self] at hq_a
            rw [List.getElem_append_left hb_lt]
            cases h_acc_q : acc[b].any (· == q) with
            | false => rfl
            | true =>
              obtain ⟨pos_b, h_eq_b, h_lb⟩ := h_inv1 b hb_lt
              rw [h_eq_b] at h_acc_q
              have h_lc : s.layerCount > 0 := by omega
              have h_pos_in := structuralClusterList_shared_contains_seed
                  s pos_b pos q h_lc h_acc_q hq_a
              rw [← h_eq_b] at h_pos_in
              have h_pos_not := h_pos_not_in b hb_lt
              rw [h_pos_in] at h_pos_not; exact absurd h_pos_not (by decide)
          · omega
        exact ih (acc ++ [structuralClusterList s pos])
            h_inv1' h_disj' h_rest_props

/-- 非空かつ非接地の位置が存在すれば floatingUnits は非空 -/
private theorem floatingUnits_isEmpty_false_of_exists_mem (s : Shape)
        (h_exists : ∃ u, u ∈ floatingUnits s) :
        (floatingUnits s).isEmpty = false := by
    obtain ⟨u, hu⟩ := h_exists
    cases hl : floatingUnits s with
    | nil => rw [hl] at hu; nomatch hu
    | cons _ _ => rfl

private theorem ungrounded_nonempty_implies_floatingUnits_nonempty_pinCase
        (s : Shape) (p : QuarterPos)
        (h_p_allValid : p ∈ QuarterPos.allValid s)
    (h_is_pin : p.getQuarter s = some .pin)
        (h_ug_bool : (groundedPositionsList s).any (· == p) = false) :
        ∃ u, u ∈ floatingUnits s := by
    exact ⟨.pin p, by
        unfold floatingUnits
        simp_rw [decide_not_mem_groundedPositions]
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨p, List.mem_filter.mpr
            ⟨by unfold allIsolatedPins
                exact List.mem_filter.mpr ⟨h_p_allValid, by simp [h_is_pin]⟩,
                by simp only [h_ug_bool, Bool.not_false]⟩, rfl⟩⟩

private theorem ungrounded_nonempty_implies_floatingUnits_nonempty_bondCase
        (s : Shape) (p : QuarterPos)
        (h_valid : p.layer < s.layerCount)
        (h_bondable : match p.getQuarter s with
            | some q => q.canFormBond = true
            | none => False)
        (h_ug_bool : (groundedPositionsList s).any (· == p) = false) :
        ∃ u, u ∈ floatingUnits s := by
    have h_covers := allStructuralClustersList_covers s p h_valid h_bondable
    rw [List.any_eq_true] at h_covers
    obtain ⟨c, hc_mem, hc_has_p⟩ := h_covers
    obtain ⟨pos, hc_is_sc, _, _⟩ :=
        allStructuralClustersList_is_structuralClusterList s c hc_mem
    have h_all_ug : c.all
            (fun x => !((groundedPositionsList s).any (· == x))) = true := by
        rw [List.all_eq_true]
        intro x hx
        cases h_x_ground : (groundedPositionsList s).any (· == x) with
        | false => rfl
        | true =>
            exfalso
            have h_x_in_sc : (structuralClusterList s pos).any (· == x) = true := by
                rw [← hc_is_sc]; exact List.any_eq_true.mpr ⟨x, hx, BEq.rfl⟩
            have h_p_in_sc := hc_is_sc ▸ hc_has_p
            have h_reach_pos_x := structuralClusterList_sound s pos x h_x_in_sc
            have h_reach_pos_p := structuralClusterList_sound s pos p h_p_in_sc
            have h_reach_x_pos := genericReachable_reverse
                (fun a b => isStructurallyBonded_symm s a b) h_reach_pos_x
            have h_reach_x_p :=
                genericReachable_trans h_reach_x_pos h_reach_pos_p
            have h_reach_ge := h_reach_x_p.mono
                (fun _ _ h => groundingEdge_of_isStructurallyBonded h)
            have h_p_ground := groundedPositionsList_closed s x p
                h_x_ground h_reach_ge
            rw [h_ug_bool] at h_p_ground
            exact absurd h_p_ground (by decide)
    exact ⟨.cluster c, by
        unfold floatingUnits
        simp_rw [decide_not_mem_groundedPositions]
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc_mem, h_all_ug⟩, rfl⟩⟩

theorem ungrounded_nonempty_implies_floatingUnits_nonempty (s : Shape) (p : QuarterPos)
        (h_valid : p.layer < s.layerCount)
        (h_ne : ∃ q, p.getQuarter s = some q ∧ !q.isEmpty = true)
        (h_ug : p ∉ groundedPositions s) :
        (floatingUnits s).isEmpty = false := by
    have h_ug_bool := (not_mem_groundedPositions_iff s p).mp h_ug
    obtain ⟨q, hq_some, hq_ne⟩ := h_ne
    -- 非空象限はピンか結合可能のいずれか
    have h_cases : q = .pin ∨ q.canFormBond = true := by
        cases q with
        | empty => simp only [Quarter.isEmpty, decide_true, Bool.not_true, Bool.false_eq_true] at hq_ne
        | pin => exact .inl rfl
        | crystal => exact .inr rfl
        | colored => exact .inr rfl
    -- p は allValid に含まれる
    have h_p_allValid : p ∈ QuarterPos.allValid s := by
        have h_any := (allValid_any_iff_layer' s p).mpr h_valid
        rw [List.any_eq_true] at h_any
        obtain ⟨x, hx, hxe⟩ := h_any
        exact eq_of_beq hxe ▸ hx
    -- isEmpty = false を ∃ u ∈ floatingUnits s から導出
    have h_exists : ∃ u, u ∈ floatingUnits s := by
        cases h_cases with
        | inl h_pin =>
            subst h_pin
            exact ungrounded_nonempty_implies_floatingUnits_nonempty_pinCase
                s p h_p_allValid (by simp [hq_some]) h_ug_bool
        | inr h_bond =>
            have h_bondable : match p.getQuarter s with
                    | some q => q.canFormBond = true | none => False := by
                rw [hq_some]; exact h_bond
            exact ungrounded_nonempty_implies_floatingUnits_nonempty_bondCase
                s p h_valid h_bondable h_ug_bool
    exact floatingUnits_isEmpty_false_of_exists_mem s h_exists

/-- floatingUnits が非空なら非空かつ非接地の位置が存在する -/
theorem floatingUnits_nonempty_implies_exists_ungrounded (s : Shape)
        (h : (floatingUnits s).isEmpty = false) :
        ∃ p : QuarterPos, p.layer < s.layerCount ∧
            (∃ q, p.getQuarter s = some q ∧ !q.isEmpty = true) ∧
            p ∉ groundedPositions s := by
    -- floatingUnits s が非空なので要素を取得
    obtain ⟨u, hu_mem⟩ : ∃ u, u ∈ floatingUnits s := by
        cases hfl : floatingUnits s with
        | nil => rw [hfl] at h; simp only [List.isEmpty_nil, Bool.true_eq_false] at h
        | cons hd tl => exact ⟨hd, .head _⟩
    -- floatingUnits の定義を展開してメンバーシップ情報を抽出
    unfold floatingUnits at hu_mem
    simp_rw [decide_not_mem_groundedPositions] at hu_mem
    rw [List.mem_append] at hu_mem
    cases hu_mem with
    | inl h_cluster =>
        -- 浮遊クラスタから位置を抽出
        rw [List.mem_map] at h_cluster
        obtain ⟨c, hc_filt, _⟩ := h_cluster
        rw [List.mem_filter] at hc_filt
        obtain ⟨hc_in_all, hc_all_ug⟩ := hc_filt
        -- c = structuralClusterList s pos
        obtain ⟨pos, hc_is_sc, h_pos_valid, q_pos, hq_pos, h_pos_bond⟩ :=
            allStructuralClustersList_is_structuralClusterList s c hc_in_all
        -- pos ∈ c（BFS 開始位置は結果に含まれる）
        have h_pos_in_c : pos ∈ c := by
            have h_any : c.any (· == pos) = true := by
                rw [hc_is_sc]; unfold structuralClusterList; rw [structuralBfs_eq_generic]
                have h_n_pos : s.layerCount * 4 > 0 := by omega
                exact genericBfs_contains_start _ _ _ _ (Nat.mul_pos h_n_pos h_n_pos)
            rw [List.any_eq_true] at h_any
            obtain ⟨y, hy, hye⟩ := h_any
            have := eq_of_beq hye; subst this; exact hy
        -- pos は非接地
        have h_pos_ug : (groundedPositionsList s).any (· == pos) = false := by
            have := (List.all_eq_true.mp hc_all_ug) pos h_pos_in_c
            revert this; cases (groundedPositionsList s).any (· == pos) <;> simp only [Bool.not_false, imp_self, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false]
        -- pos は非空（canFormBond → not empty）
        have h_pos_ne : !q_pos.isEmpty = true := by
            cases q_pos <;> simp only [Quarter.canFormBond, Bool.false_eq_true] at h_pos_bond
                <;> simp only [Quarter.isEmpty, Bool.false_eq_true, decide_false, Bool.not_false]
        exact ⟨pos, h_pos_valid, ⟨q_pos, hq_pos, h_pos_ne⟩,
            (not_mem_groundedPositions_iff s pos).mpr h_pos_ug⟩
    | inr h_pin =>
        -- 浮遊ピンから位置を抽出
        rw [List.mem_map] at h_pin
        obtain ⟨p', hp'_filt, _⟩ := h_pin
        rw [List.mem_filter] at hp'_filt
        obtain ⟨hp'_in_iso, hp'_ug⟩ := hp'_filt
        -- p' ∈ allIsolatedPins s → allValid + ピン条件
        unfold allIsolatedPins at hp'_in_iso
        rw [List.mem_filter] at hp'_in_iso
        obtain ⟨hp'_allValid, hp'_is_pin⟩ := hp'_in_iso
        -- p' は valid
        have h_p'_valid : p'.layer < s.layerCount :=
            (allValid_any_iff_layer' s p').mp
                (List.any_eq_true.mpr ⟨p', hp'_allValid, BEq.rfl⟩)
        -- p' は非空（ピンは非空）
        have h_p'_ne : ∃ q, p'.getQuarter s = some q ∧ !q.isEmpty = true := by
            cases hq : p'.getQuarter s with
            | none => simp only [hq, Bool.false_eq_true] at hp'_is_pin
            | some q =>
                cases q <;> simp_all only [List.isEmpty_eq_false_iff, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false, beq_iff_eq, Bool.false_eq_true, Option.some.injEq, Quarter.isEmpty, Bool.decide_eq_true, exists_eq_left']
        -- p' は非接地
        have h_p'_ug : (groundedPositionsList s).any (· == p') = false := by
            revert hp'_ug; cases (groundedPositionsList s).any (· == p') <;> simp only [Bool.not_false, imp_self, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false]
        exact ⟨p', h_p'_valid, h_p'_ne,
            (not_mem_groundedPositions_iff s p').mpr h_p'_ug⟩

-- ============================================================
-- S1-aux: nonGroundedLayerSum = 0 → floatingUnits 空（構成的証明）
-- ============================================================

/-- 単調な自然数 foldl は初期値より小さくならない -/
private theorem foldl_mono_nat {α : Type*} (f : α → Nat → Nat)
        (h_mono : ∀ x acc, acc ≤ f x acc) (l : List α) (init : Nat) :
        init ≤ l.foldl (fun acc x => f x acc) init := by
    induction l generalizing init with
    | nil => exact Nat.le_refl _
    | cons x xs ih =>
        simp only [List.foldl_cons]
        exact Nat.le_trans (h_mono x init) (ih (f x init))

/-- 単調な自然数 foldl は任意の要素で下限 `init + n` を持つ -/
private theorem foldl_mem_ge_nat {α : Type*} (f : α → Nat → Nat)
        (h_mono : ∀ x acc, acc ≤ f x acc) (l : List α) (init : Nat)
        (p : α) (hp : p ∈ l) (n : Nat) (h_ge : ∀ acc, acc + n ≤ f p acc) :
        init + n ≤ l.foldl (fun acc x => f x acc) init := by
    induction l generalizing init with
    | nil => exact absurd hp (List.not_mem_nil)
    | cons x xs ih =>
        simp only [List.foldl_cons]
        rcases List.mem_cons.mp hp with rfl | hmem
        · exact Nat.le_trans (h_ge init) (foldl_mono_nat f h_mono xs _)
        · calc init + n
                ≤ f x init + n := by have := h_mono x init; omega
              _ ≤ xs.foldl (fun acc x => f x acc) (f x init) := ih _ hmem

/-- nonGroundedLayerSum = 0 ならば浮遊単位は空。
    構成的証明: 浮遊単位が非空なら非接地・非空・valid な位置 p が存在し、
    p の寄与 p.layer + 1 ≥ 1 が nonGroundedLayerSum に含まれるため sum ≥ 1 > 0 となり矛盾。
    （S1-aux の公理化を除去し Mathlib 標準補題のみで導出） -/
theorem nonGroundedLayerSum_zero_fus_empty (s : Shape)
        (h : nonGroundedLayerSum s = 0) :
        (floatingUnits s).isEmpty = true := by
    by_contra hcontra
    have h_ne : (floatingUnits s).isEmpty = false := by
        cases heq : (floatingUnits s).isEmpty with
        | true => exact absurd heq hcontra
        | false => rfl
    obtain ⟨p, h_valid, ⟨q, hq_some, hq_ne⟩, h_ug⟩ :=
        floatingUnits_nonempty_implies_exists_ungrounded s h_ne
    have h_p_allValid : p ∈ QuarterPos.allValid s := by
        have h_any := (allValid_any_iff_layer' s p).mpr h_valid
        rw [List.any_eq_true] at h_any
        obtain ⟨y, hy, hye⟩ := h_any
        exact eq_of_beq hye ▸ hy
    -- nonGroundedLayerSum の foldl に単調性下限を適用
    -- F := foldl のボディ関数
    let F : QuarterPos → Nat → Nat := fun p' acc =>
        match p'.getQuarter s with
        | some q' => if !q'.isEmpty && p' ∉ groundedPositions s
                     then acc + p'.layer + 1 else acc
        | none => acc
    have h_mono : ∀ x acc, acc ≤ F x acc := by
        intro x acc
        show acc ≤ match x.getQuarter s with
            | some q' => if !q'.isEmpty && x ∉ groundedPositions s
                         then acc + x.layer + 1 else acc
            | none => acc
        cases x.getQuarter s with
        | none => exact Nat.le_refl _
        | some q' =>
            show acc ≤ if !q'.isEmpty && x ∉ groundedPositions s
                       then acc + x.layer + 1 else acc
            split
            · omega
            · exact Nat.le_refl _
    have h_ge_p : ∀ acc, acc + (p.layer + 1) ≤ F p acc := by
        intro acc
        show acc + (p.layer + 1) ≤ match p.getQuarter s with
            | some q' => if !q'.isEmpty && p ∉ groundedPositions s
                         then acc + p.layer + 1 else acc
            | none => acc
        rw [hq_some]
        -- hq_ne を Bool 形式に変換
        have hq_ne_bool : (!q.isEmpty) = true := by
            simpa [decide_eq_true_eq] using hq_ne
        -- if の条件（Bool 型）が true になることを証明
        have hcond : (!q.isEmpty && decide (p ∉ groundedPositions s)) = true := by
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨hq_ne_bool, h_ug⟩
        -- if の条件を真として展開
        simp only [hcond, if_true]
        -- ゴール: acc + (p.layer + 1) ≤ acc + p.layer + 1
        rw [Nat.add_assoc]
    have h_lb : (0 : Nat) + (p.layer + 1) ≤ nonGroundedLayerSum s := by
        show (0 : Nat) + (p.layer + 1) ≤
            (QuarterPos.allValid s).foldl (fun acc p' => F p' acc) 0
        exact foldl_mem_ge_nat F h_mono (QuarterPos.allValid s) 0 p h_p_allValid
            (p.layer + 1) h_ge_p
    rw [h] at h_lb
    omega

-- ============================================================
-- processWave_floatingUnits_empty は ProcessWave.lean に移設（2026-04-21）
-- ============================================================

/-- floatingUnits 非空ならば σ 変換後も非空（汎用版） -/
theorem floatingUnits_nonempty_implies_σ_nonempty (s : Shape)
        (σ_qpos : QuarterPos → QuarterPos) (σ_shape : Shape)
        (h_lc : σ_shape.layerCount = s.layerCount)
        (h_layer : ∀ p, (σ_qpos p).layer = p.layer)
        (h_gq : ∀ p, (σ_qpos p).getQuarter σ_shape = p.getQuarter s)
        (h_gp : ∀ p, p ∈ groundedPositions s ↔ σ_qpos p ∈ groundedPositions σ_shape)
        (h : (floatingUnits s).isEmpty = false) :
        (floatingUnits σ_shape).isEmpty = false := by
    obtain ⟨p, h_valid, ⟨q, hq, h_ne⟩, h_ug⟩ :=
        floatingUnits_nonempty_implies_exists_ungrounded s h
    apply ungrounded_nonempty_implies_floatingUnits_nonempty σ_shape (σ_qpos p)
    · rw [h_layer, h_lc]; exact h_valid
    · exact ⟨q, by rw [h_gq]; exact hq, h_ne⟩
    · exact fun h => h_ug ((h_gp p).mpr h)

/-- floatingUnits が非空なら s.rotate180 でも非空 -/
theorem floatingUnits_nonempty_implies_rotate180_nonempty (s : Shape)
        (h : (floatingUnits s).isEmpty = false) :
        (floatingUnits s.rotate180).isEmpty = false :=
    floatingUnits_nonempty_implies_σ_nonempty s QuarterPos.rotate180 s.rotate180
        (Shape.layerCount_rotate180 s) (fun _ => rfl) (fun _ => getQuarter_rotate180 s _)
        (fun p => mem_groundedPositions_rotate180 s p) h

/-- floatingUnits の isEmpty は rotate180 で不変 -/
theorem floatingUnits_isEmpty_rotate180 (s : Shape) :
        (floatingUnits s).isEmpty = (floatingUnits s.rotate180).isEmpty :=
    floatingUnits_isEmpty_σ s s.rotate180
        (floatingUnits_nonempty_implies_rotate180_nonempty s)
        (fun h => by
            have := floatingUnits_nonempty_implies_rotate180_nonempty s.rotate180 h
            rw [Shape.rotate180_rotate180] at this; exact this)

-- ============================================================
-- rotateCW 等変性チェーン
-- ============================================================

/-- isGroundingContact は rotateCW で不変 -/
theorem isGroundingContact_rotateCW (s : Shape) (p1 p2 : QuarterPos) :
        isGroundingContact (s.rotateCW) (p1.rotateCW) (p2.rotateCW) =
        isGroundingContact s p1 p2 := by
    simp only [isGroundingContact, QuarterPos.getQuarter_rotateCW]
    simp only [QuarterPos.rotateCW, Direction.adjacent_rotateCW]
    cases h1 : p1.getQuarter s <;> cases h2 : p2.getQuarter s <;> try rfl
    rename_i q1 q2
    cases q1 <;> cases q2 <;> simp only [Quarter.isEmpty] <;> (try rfl) <;>
    simp only [Bool.not_false, Bool.true_and] <;>
    congr 1 <;> cases p1.dir <;> cases p2.dir <;> rfl

/-- isUpwardGroundingContact は rotateCW で不変（レイヤが変わらないため） -/
theorem isUpwardGroundingContact_rotateCW (s : Shape) (p1 p2 : QuarterPos) :
        isUpwardGroundingContact (s.rotateCW) (p1.rotateCW) (p2.rotateCW) =
        isUpwardGroundingContact s p1 p2 := by
    unfold isUpwardGroundingContact
    rw [isGroundingContact_rotateCW]
    congr 1

/-- groundingEdge は rotateCW で不変 -/
theorem groundingEdge_rotateCW (s : Shape) (p1 p2 : QuarterPos) :
        groundingEdge (s.rotateCW) (p1.rotateCW) (p2.rotateCW) =
        groundingEdge s p1 p2 := by
    simp only [groundingEdge, isUpwardGroundingContact_rotateCW,
        isStructurallyBonded_rotateCW]

/-- groundingBfs は rotateCW で等変（genericBfs_map_comm より導出） -/
theorem groundingBfs_rotateCW (s : Shape)
        (allPos visited queue : List QuarterPos) (fuel : Nat) :
        groundingBfs s.rotateCW
            (allPos.map QuarterPos.rotateCW)
            (visited.map QuarterPos.rotateCW)
            (queue.map QuarterPos.rotateCW) fuel =
        (groundingBfs s allPos visited queue fuel).map QuarterPos.rotateCW := by
    simp only [groundingBfs_eq_generic]
    exact genericBfs_map_comm
        (groundingEdge s) (groundingEdge s.rotateCW) QuarterPos.rotateCW
        (fun a b => groundingEdge_rotateCW s a b)
        σ_rCW.quarterPos_beq allPos visited queue fuel

/-- allValid は rotateCW で不変 -/
theorem allValid_rotateCW (s : Shape) :
        QuarterPos.allValid s.rotateCW = QuarterPos.allValid s := by
    unfold QuarterPos.allValid; simp only [Shape.layerCount_rotateCW]

/-- groundedPositionsList の rotateCW 等変性 -/
theorem groundedPositionsList_rotateCW_mapped (s : Shape) :
        let allPos := QuarterPos.allValid s
        let seeds := allPos.filter fun p =>
            p.layer == 0 &&
            match p.getQuarter s with
            | some q => !q.isEmpty | none => false
        groundingBfs s.rotateCW
            (allPos.map QuarterPos.rotateCW)
            []
            (seeds.map QuarterPos.rotateCW)
            (s.layerCount * 4 * (s.layerCount * 4) + s.layerCount * 4) =
        (groundedPositionsList s).map QuarterPos.rotateCW := by
    unfold groundedPositionsList
    exact groundingBfs_rotateCW s (QuarterPos.allValid s) []
        ((QuarterPos.allValid s).filter fun p =>
            p.layer == 0 &&
            match p.getQuarter s with
            | some q => !q.isEmpty
            | none   => false)
        (s.layerCount * 4 * (s.layerCount * 4) + s.layerCount * 4)

/-- grounding seed の rotateCW 変換 -/
theorem grounding_seed_to_rotateCW (s : Shape) (seed : QuarterPos)
        (h_seed : seed ∈ (QuarterPos.allValid s).filter (fun q =>
            q.layer == 0 && match q.getQuarter s with
            | some q => !q.isEmpty | none => false)) :
        seed.rotateCW ∈ (QuarterPos.allValid s.rotateCW).filter (fun q =>
            q.layer == 0 && match q.getQuarter s.rotateCW with
            | some q => !q.isEmpty | none => false) := by
    rw [allValid_rotateCW]
    have ⟨h_allValid, h_pred⟩ := List.mem_filter.mp h_seed
    have h_layer : seed.layer < s.layerCount :=
        (allValid_any_iff_layer' s seed).mp
            (List.any_eq_true.mpr ⟨seed, h_allValid, BEq.rfl⟩)
    have h_cw_allValid : seed.rotateCW ∈ QuarterPos.allValid s := by
        have h_any := (allValid_any_iff_layer' s seed.rotateCW).mpr h_layer
        rw [List.any_eq_true] at h_any
        obtain ⟨y, hy, hye⟩ := h_any; exact eq_of_beq hye ▸ hy
    exact List.mem_filter.mpr ⟨h_cw_allValid, by
        simp only [QuarterPos.getQuarter_rotateCW]; exact h_pred⟩

/-- grounding seed の逆 rotateCW 変換 -/
theorem grounding_seed_from_rotateCW (s : Shape) (seed : QuarterPos)
        (h_seed : seed ∈ (QuarterPos.allValid s.rotateCW).filter (fun q =>
            q.layer == 0 && match q.getQuarter s.rotateCW with
            | some q => !q.isEmpty | none => false)) :
        seed.rotateCCW ∈ (QuarterPos.allValid s).filter (fun q =>
            q.layer == 0 && match q.getQuarter s with
            | some q => !q.isEmpty | none => false) := by
    rw [allValid_rotateCW] at h_seed
    have ⟨h_allValid, h_pred⟩ := List.mem_filter.mp h_seed
    have h_layer : seed.layer < s.layerCount :=
        (allValid_any_iff_layer' s seed).mp
            (List.any_eq_true.mpr ⟨seed, h_allValid, BEq.rfl⟩)
    have h_ccw_allValid : seed.rotateCCW ∈ QuarterPos.allValid s := by
        have h_any := (allValid_any_iff_layer' s seed.rotateCCW).mpr h_layer
        rw [List.any_eq_true] at h_any
        obtain ⟨y, hy, hye⟩ := h_any; exact eq_of_beq hye ▸ hy
    exact List.mem_filter.mpr ⟨h_ccw_allValid, by
        simp only [← QuarterPos.getQuarter_rotateCW_inv]; exact h_pred⟩

/-- 上方向接地接触到達可能性は rotateCW で保存される -/
theorem upwardGroundingReachable_rotateCW (s : Shape) (p q : QuarterPos)
        (h : GenericReachable (isUpwardGroundingContact s) p q) :
        GenericReachable (isUpwardGroundingContact s.rotateCW) p.rotateCW q.rotateCW := by
    induction h with
    | refl => exact .refl
    | step h_bond _ ih =>
        exact .step (isUpwardGroundingContact_rotateCW s _ _ ▸ h_bond) ih

/-- groundingEdge 到達可能性は rotateCW で保存される -/
theorem groundingEdgeReachable_rotateCW (s : Shape) (p q : QuarterPos)
        (h : GenericReachable (groundingEdge s) p q) :
        GenericReachable (groundingEdge s.rotateCW) p.rotateCW q.rotateCW := by
    induction h with
    | refl => exact .refl
    | step h_bond _ ih =>
        exact .step (groundingEdge_rotateCW s _ _ ▸ h_bond) ih

/-- 上方向接地接触到達可能性は rotateCW 逆方向でも保存される -/
theorem upwardGroundingReachable_from_rotateCW (s : Shape) (p q : QuarterPos)
        (h : GenericReachable (isUpwardGroundingContact s.rotateCW) p q) :
        GenericReachable (isUpwardGroundingContact s) p.rotateCCW q.rotateCCW := by
    induction h with
    | refl => exact .refl
    | @step a b c h_bond _ ih =>
        have : isUpwardGroundingContact s a.rotateCCW b.rotateCCW = true := by
            have h_eq := isUpwardGroundingContact_rotateCW s a.rotateCCW b.rotateCCW
            simp only [QuarterPos.rotateCCW_rotateCW] at h_eq
            rw [← h_eq]; exact h_bond
        exact .step this ih

/-- groundingEdge 到達可能性は rotateCW 逆方向でも保存される -/
theorem groundingEdgeReachable_from_rotateCW (s : Shape) (p q : QuarterPos)
        (h : GenericReachable (groundingEdge s.rotateCW) p q) :
        GenericReachable (groundingEdge s) p.rotateCCW q.rotateCCW := by
    induction h with
    | refl => exact .refl
    | @step a b c h_bond _ ih =>
        have : groundingEdge s a.rotateCCW b.rotateCCW = true := by
            have h_eq := groundingEdge_rotateCW s a.rotateCCW b.rotateCCW
            simp only [QuarterPos.rotateCCW_rotateCW] at h_eq
            rw [← h_eq]; exact h_bond
        exact .step this ih

/-- groundedPositions は rotateCW で等変（Finset レベル）。
    groundedPositions_σ の rotateCW インスタンス。 -/
theorem groundedPositions_rotateCW (s : Shape) :
        groundedPositions s.rotateCW =
        (groundedPositions s).image QuarterPos.rotateCW :=
    groundedPositions_σ s QuarterPos.rotateCW QuarterPos.rotateCCW s.rotateCW
        (groundingEdgeReachable_rotateCW s)
        (groundingEdgeReachable_from_rotateCW s)
        QuarterPos.rotateCCW_rotateCW
        (grounding_seed_to_rotateCW s)
        (grounding_seed_from_rotateCW s)

/-- groundedPositions のメンバーシップは rotateCW で保存される -/
theorem mem_groundedPositions_rotateCW (s : Shape) (p : QuarterPos) :
        p ∈ groundedPositions s ↔
        p.rotateCW ∈ groundedPositions s.rotateCW :=
    mem_groundedPositions_σ s p QuarterPos.rotateCW QuarterPos.rotateCCW s.rotateCW
        QuarterPos.rotateCW_rotateCCW (groundedPositions_rotateCW s)

/-- floatingUnits 非空ならば rotateCW でも非空 -/
theorem floatingUnits_nonempty_implies_rotateCW_nonempty (s : Shape)
        (h : (floatingUnits s).isEmpty = false) :
        (floatingUnits s.rotateCW).isEmpty = false :=
    floatingUnits_nonempty_implies_σ_nonempty s QuarterPos.rotateCW s.rotateCW
        (Shape.layerCount_rotateCW s) (fun _ => rfl) (fun _ => QuarterPos.getQuarter_rotateCW s _)
        (fun p => mem_groundedPositions_rotateCW s p) h

/-- floatingUnits の isEmpty は rotateCW で不変 -/
theorem floatingUnits_isEmpty_rotateCW (s : Shape) :
        (floatingUnits s).isEmpty = (floatingUnits s.rotateCW).isEmpty :=
    floatingUnits_isEmpty_σ s s.rotateCW
        (floatingUnits_nonempty_implies_rotateCW_nonempty s)
        (fun h => by
            have h1 := floatingUnits_nonempty_implies_rotateCW_nonempty s.rotateCW h
            have h2 := floatingUnits_nonempty_implies_rotateCW_nonempty s.rotateCW.rotateCW h1
            have h3 := floatingUnits_nonempty_implies_rotateCW_nonempty
                s.rotateCW.rotateCW.rotateCW h2
            rw [Shape.rotateCW_four] at h3; exact h3)

/-- isOccupied は rotate180 で等変 -/
theorem isOccupied_rotate180 (obs : List Layer) (layer : Nat) (d : Direction) :
        isOccupied (obs.map Layer.rotate180) layer (d.rotate180) =
        isOccupied obs layer d := by
    simp only [isOccupied, List.getElem?_map]
    cases obs[layer]? with
    | none => rfl
    | some l => simp only [Option.map_some, getDir_rotate180]

/-- landed 判定 (positions.any) は rotate180 で不変 -/
theorem landed_rotate180 (positions : List QuarterPos) (obs : List Layer) (d : Nat) :
        (positions.map QuarterPos.rotate180).any (fun p =>
            let newLayer := p.layer - d
            newLayer == 0 || isOccupied (obs.map Layer.rotate180) (newLayer - 1) p.dir) =
        positions.any (fun p =>
            let newLayer := p.layer - d
            newLayer == 0 || isOccupied obs (newLayer - 1) p.dir) := by
    induction positions with
    | nil => rfl
    | cons p rest ih =>
        simp only [List.map, List.any]
        rw [ih]
        congr 1
        simp only [QuarterPos.rotate180]
        congr 1
        exact isOccupied_rotate180 obs _ _

/-- landingDistance.check は rotate180 で不変 -/
theorem landingDistance_check_rotate180 (positions : List QuarterPos) (obs : List Layer)
        (maxDrop d fuel : Nat) :
        landingDistance.check (obs.map Layer.rotate180) (positions.map QuarterPos.rotate180) maxDrop d fuel =
        landingDistance.check obs positions maxDrop d fuel := by
    induction fuel generalizing d with
    | zero => rfl
    | succ n ih =>
        simp only [landingDistance.check]
        split
        · rfl
        · rw [landed_rotate180]
          split
          · rfl
          · exact ih (d + 1)

/-- landingDistance は rotate180 で不変 -/
theorem landingDistance_rotate180 (u : FallingUnit) (obs : List Layer) :
        landingDistance u.rotate180 (obs.map Layer.rotate180) = landingDistance u obs := by
    simp only [landingDistance]
    simp only [FallingUnit.minLayer_rotate180, FallingUnit.positions_rotate180]
    exact landingDistance_check_rotate180 u.positions obs u.minLayer 1 (u.minLayer + 1)

/-- setDir と rotate180 の可換性（一般版） -/
theorem setDir_rotate180 (l : Layer) (d : Direction) (q : Quarter) :
        (QuarterPos.setDir l d q).rotate180 =
        QuarterPos.setDir (l.rotate180) (d.rotate180) q := by
    cases d <;> rfl

/-- replicate Layer.empty の map rotate180 -/
theorem replicate_empty_rotate180 (n : Nat) :
        (List.replicate n Layer.empty).map Layer.rotate180 = List.replicate n Layer.empty := by
    induction n with
    | zero => rfl
    | succ n ih =>
        show Layer.empty.rotate180 :: (List.replicate n Layer.empty).map Layer.rotate180 =
             Layer.empty :: List.replicate n Layer.empty
        rw [ih]
        rfl

/-- placeQuarter は rotate180 で等変 -/
theorem placeQuarter_rotate180 (layers : List Layer) (lay : Nat) (d : Direction) (q : Quarter) :
        (placeQuarter layers lay d q).map Layer.rotate180 =
        placeQuarter (layers.map Layer.rotate180) lay (d.rotate180) q := by
    simp only [placeQuarter, List.length_map]
    -- if 分岐を場合分け
    if h : lay < layers.length then
        simp only [h, ↓reduceIte, List.getElem?_map]
        cases layers[lay]? with
        | none => rfl
        | some l => simp only [Option.map_some]; rw [List.map_set, setDir_rotate180]
    else
        simp only [h, ↓reduceIte]
        -- 拡張リストを ext とする
        have hext : List.map Layer.rotate180 layers ++ List.replicate (lay + 1 - layers.length) Layer.empty =
            (layers ++ List.replicate (lay + 1 - layers.length) Layer.empty).map Layer.rotate180 := by
            rw [List.map_append, replicate_empty_rotate180]
        rw [hext, List.getElem?_map]
        cases (layers ++ List.replicate (lay + 1 - layers.length) Layer.empty)[lay]? with
        | none => rfl
        | some l =>
            simp only [Option.map_some]
            rw [List.map_set, setDir_rotate180]

/-- placeFallingUnit は rotate180 で等変 -/
theorem placeFallingUnit_rotate180 (origShape : Shape) (obs : List Layer)
        (u : FallingUnit) (dropDist : Nat) :
        (placeFallingUnit origShape obs u dropDist).map Layer.rotate180 =
        placeFallingUnit origShape.rotate180 (obs.map Layer.rotate180) u.rotate180 dropDist := by
    simp only [placeFallingUnit, FallingUnit.positions_rotate180]
    -- u.positions について帰納法（acc を一般化）
    suffices h : ∀ (acc : List Layer),
        (u.positions.foldl (fun obs p =>
            match p.getQuarter origShape with
            | some q => placeQuarter obs (p.layer - dropDist) p.dir q
            | none => obs) acc).map Layer.rotate180 =
        (u.positions.map QuarterPos.rotate180).foldl (fun obs p =>
            match p.getQuarter origShape.rotate180 with
            | some q => placeQuarter obs (p.layer - dropDist) p.dir q
            | none => obs) (acc.map Layer.rotate180) from h obs
    intro acc
    induction u.positions generalizing acc with
    | nil => rfl
    | cons p rest ih =>
        simp only [List.foldl_cons, List.map_cons]
        -- step の等変性を示す
        have hstep : (match p.getQuarter origShape with
            | some q => placeQuarter acc (p.layer - dropDist) p.dir q
            | none => acc).map Layer.rotate180 =
            (match p.rotate180.getQuarter origShape.rotate180 with
            | some q => placeQuarter (acc.map Layer.rotate180)
                (p.rotate180.layer - dropDist) p.rotate180.dir q
            | none => acc.map Layer.rotate180) := by
            rw [getQuarter_rotate180]
            cases p.getQuarter origShape with
            | none => rfl
            | some q =>
                rw [QuarterPos.rotate180_layer, QuarterPos.rotate180_dir]
                exact placeQuarter_rotate180 ..
        rw [ih, hstep]

/-- flatMap + map の交換則 -/
theorem flatMap_map_rotate180 (units : List FallingUnit) :
        (units.map FallingUnit.rotate180).flatMap FallingUnit.positions =
        (units.flatMap FallingUnit.positions).map QuarterPos.rotate180 := by
    induction units with
    | nil => rfl
    | cons u rest ih =>
        simp only [List.map_cons, List.flatMap_cons, List.map_append]
        rw [FallingUnit.positions_rotate180, ih]

/-- sorted.foldl (placeFallingUnit + landingDistance) の rotate180 等変性 -/
theorem foldl_place_rotate180 (s : Shape) (sorted : List FallingUnit) (obs : List Layer) :
        (sorted.foldl (fun obs u =>
            let d := landingDistance u obs
            placeFallingUnit s obs u d
        ) obs).map Layer.rotate180 =
        (sorted.map FallingUnit.rotate180).foldl (fun obs u =>
            let d := landingDistance u obs
            placeFallingUnit s.rotate180 obs u d
        ) (obs.map Layer.rotate180) := by
    induction sorted generalizing obs with
    | nil => rfl
    | cons u rest ih =>
        simp only [List.foldl_cons, List.map_cons]
        rw [ih]
        congr 1
        rw [landingDistance_rotate180, placeFallingUnit_rotate180]

-- ============================================================
-- placeLDGroups の rotate180 等変性
-- ============================================================

/-- takeWhile と map の可換性（述語が f を通して対応する場合） -/
private theorem takeWhile_map_comm {f : α → β} {p : β → Bool} {q : α → Bool}
        (h : ∀ x, p (f x) = q x) (l : List α) :
        (l.map f).takeWhile p = (l.takeWhile q).map f := by
    induction l with
    | nil => rfl
    | cons a t ih =>
        simp only [List.map_cons, List.takeWhile_cons]; rw [h]; split <;> simp [ih]

/-- dropWhile と map の可換性（述語が f を通して対応する場合） -/
private theorem dropWhile_map_comm {f : α → β} {p : β → Bool} {q : α → Bool}
        (h : ∀ x, p (f x) = q x) (l : List α) :
        (l.map f).dropWhile p = (l.dropWhile q).map f := by
    induction l with
    | nil => rfl
    | cons a t ih =>
        simp only [List.map_cons, List.dropWhile_cons]; rw [h]; split <;> simp [ih]

/-- 固定着地距離 d での foldl placeFallingUnit の rotate180 等変性 -/
private theorem foldl_place_fixed_d_rotate180 (s : Shape) (group : List FallingUnit)
        (obs : List Layer) (d : Nat) :
        (group.foldl (fun acc fu => placeFallingUnit s acc fu d) obs).map Layer.rotate180 =
        (group.map FallingUnit.rotate180).foldl
            (fun acc fu => placeFallingUnit s.rotate180 acc fu d)
            (obs.map Layer.rotate180) := by
    induction group generalizing obs with
    | nil => rfl
    | cons u rest ih =>
        simp only [List.foldl_cons, List.map_cons]
        rw [ih]; congr 1; exact placeFallingUnit_rotate180 s obs u d

/-- placeLDGroups は rotate180 で等変である -/
theorem placeLDGroups_rotate180 (s : Shape) (sorted : List FallingUnit) (obs : List Layer) :
        (placeLDGroups s sorted obs).map Layer.rotate180 =
        placeLDGroups s.rotate180 (sorted.map FallingUnit.rotate180)
            (obs.map Layer.rotate180) := by
    suffices h : ∀ (n : Nat) (sorted : List FallingUnit) (obs : List Layer),
        sorted.length ≤ n →
        (placeLDGroups s sorted obs).map Layer.rotate180 =
        placeLDGroups s.rotate180 (sorted.map FallingUnit.rotate180)
            (obs.map Layer.rotate180) from
        h sorted.length sorted obs le_rfl
    intro n
    induction n with
    | zero =>
        intro sorted obs hlen
        have : sorted = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
        subst this; simp [placeLDGroups]
    | succ n ih =>
        intro sorted obs hlen
        match hsorted : sorted with
        | [] => simp [placeLDGroups]
        | first :: rest =>
            simp only [placeLDGroups, List.map_cons]
            have hld : landingDistance first.rotate180 (obs.map Layer.rotate180) =
                    landingDistance first obs :=
                landingDistance_rotate180 first obs
            conv_rhs =>
                rw [show first.rotate180 :: rest.map FallingUnit.rotate180 =
                    (first :: rest).map FallingUnit.rotate180 from rfl]
                rw [dropWhile_map_comm (fun u => by rw [landingDistance_rotate180, hld])]
                rw [takeWhile_map_comm (fun u => by rw [landingDistance_rotate180, hld])]
                rw [hld]
            rw [ih _ _ (by
                have : ((first :: rest).dropWhile
                    (fun u => landingDistance u obs == landingDistance first obs)).length <
                    (first :: rest).length := by
                    simp only [List.dropWhile_cons, beq_self_eq_true, ↓reduceIte,
                        List.length_cons]
                    exact Nat.lt_succ_of_le (List.dropWhile_suffix _).length_le
                omega)]
            congr 1
            exact foldl_place_fixed_d_rotate180 s _ obs _

-- floatingUnit_any_in_rotate180: per-FU .any 等価性
-- ============================================================

/-- List.map rotate180 後の .any と rotate180 の関係（Equivariance 内部用） -/
private theorem any_map_rotate180_beq_local (ps : List QuarterPos) (p : QuarterPos) :
        (ps.map QuarterPos.rotate180).any (· == p) =
        ps.any (· == p.rotate180) := by
    induction ps with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.map, List.any, ih]
        congr 1
        have : (x.rotate180 == p) = (x == p.rotate180) := by
            have h := σ_r180.quarterPos_beq x p.rotate180
            simp only [QuarterPos.rotate180_rotate180] at h; exact h
        exact this

/-- floatingUnits s の各クラスタに対し、floatingUnits s.rotate180 に
    .any 等価かつ型が一致するクラスタが存在する -/
private theorem floatingUnit_any_in_rotate180_cluster (s : Shape) (ps : List QuarterPos)
        (hu : FallingUnit.cluster ps ∈ floatingUnits s) :
        ∃ v ∈ floatingUnits s.rotate180,
            (∀ p, (FallingUnit.cluster ps).rotate180.positions.any (· == p) = v.positions.any (· == p))
            ∧ (FallingUnit.cluster ps).rotate180.typeOrd = v.typeOrd := by
    rw [floatingUnits_eq_append, List.mem_append] at hu
    cases hu with
    | inl h_cluster =>
        rw [List.mem_map] at h_cluster
        obtain ⟨ps', hps_filtered, h_eq⟩ := h_cluster
        have h_ps_eq : ps' = ps := FallingUnit.cluster.inj h_eq
        subst ps'
        rw [List.mem_filter] at hps_filtered
        obtain ⟨hps_mem, hps_floating⟩ := hps_filtered
        obtain ⟨pos, hps_eq, h_layer, h_bondable⟩ :=
            allStructuralClustersList_is_structuralClusterList s ps hps_mem
        -- pos.rotate180 は s.rotate180 で bondable
        have h_bond_r : match pos.rotate180.getQuarter s.rotate180 with
                | some q => q.canFormBond = true | none => False := by
            rw [QuarterPos.getQuarter_rotate180]
            obtain ⟨q, hq, hb⟩ := h_bondable; rw [hq]; exact hb
        have h_layer_r : pos.rotate180.layer < s.rotate180.layerCount := by
            rw [Shape.layerCount_rotate180]; exact h_layer
        have h_covers := allStructuralClustersList_covers s.rotate180 pos.rotate180
            h_layer_r h_bond_r
        rw [List.any_eq_true] at h_covers
        obtain ⟨c', hc'_mem, hc'_any⟩ := h_covers
        obtain ⟨pos', hc'_eq, _, _⟩ :=
            allStructuralClustersList_is_structuralClusterList s.rotate180 c' hc'_mem
        -- c' の .any と (ps.map rotate180) の .any は一致する
        have h_any_eq : ∀ (q : QuarterPos),
                c'.any (· == q) = (ps.map QuarterPos.rotate180).any (· == q) := by
            intro q
            have h_sc : ps.any (· == q.rotate180) =
                    (structuralClusterList s.rotate180 pos.rotate180).any (· == q) := by
                have h := mem_structuralCluster_rotate180 s pos q.rotate180
                simp only [QuarterPos.rotate180_rotate180, structuralCluster,
                    List.mem_toFinset] at h
                rw [hps_eq]
                exact Bool.eq_iff_iff.mpr
                    ((any_beq_iff_mem _ _).trans (h.trans (any_beq_iff_mem _ _).symm))
            rw [hc'_eq]
            rw [any_map_rotate180_beq_local]
            rw [h_sc]
            -- 同じ連結成分の一意性
            have h_pos_r_in_c' : (structuralClusterList s.rotate180 pos').any (· == pos.rotate180) = true := by
                rw [← hc'_eq]; exact hc'_any
            cases hq : (structuralClusterList s.rotate180 pos').any (· == q) with
            | true =>
                have h_q_reach := structuralClusterList_sound s.rotate180 pos' q hq
                have h_q_from_pos := GenericReachable.trans
                    ((structuralClusterList_sound s.rotate180 pos' pos.rotate180 h_pos_r_in_c').symm
                        (fun a b => isStructurallyBonded_symm s.rotate180 a b))
                    h_q_reach
                symm; exact structuralClusterList_complete s.rotate180 pos.rotate180 q
                    (by rw [Shape.layerCount_rotate180]; omega)
                    h_q_from_pos
            | false =>
                symm
                cases hq2 : (structuralClusterList s.rotate180 pos.rotate180).any (· == q) with
                | false => rfl
                | true =>
                    exfalso
                    have h_pos'_in_sc : (structuralClusterList s.rotate180 pos.rotate180).any (· == pos') = true :=
                        structuralClusterList_complete s.rotate180 pos.rotate180 pos'
                            (by rw [Shape.layerCount_rotate180]; omega)
                            ((structuralClusterList_sound s.rotate180 pos' pos.rotate180 h_pos_r_in_c').symm
                                (fun a b => isStructurallyBonded_symm s.rotate180 a b))
                    have := structuralClusterList_complete s.rotate180 pos' q
                        (by rw [Shape.layerCount_rotate180]; omega)
                        (GenericReachable.trans
                            ((structuralClusterList_sound s.rotate180 pos.rotate180 pos' h_pos'_in_sc).symm
                                (fun a b => isStructurallyBonded_symm s.rotate180 a b))
                            (structuralClusterList_sound s.rotate180 pos.rotate180 q hq2))
                    rw [hq] at this; exact Bool.noConfusion this
        -- c' が浮遊であることを示す
        have h_floating : c'.all (fun p => !((groundedPositionsList s.rotate180).any (· == p))) = true := by
            rw [List.all_eq_true]
            intro q hq_mem
            have hq_any : c'.any (· == q) = true :=
                List.any_eq_true.mpr ⟨q, hq_mem, beq_self_eq_true q⟩
            rw [h_any_eq] at hq_any
            rw [any_map_rotate180_beq_local] at hq_any
            rw [List.all_eq_true] at hps_floating
            have h_qr_in_ps : q.rotate180 ∈ ps := by
                rw [List.any_eq_true] at hq_any
                obtain ⟨x, hx_mem, hx_beq⟩ := hq_any
                exact eq_of_beq hx_beq ▸ hx_mem
            have h_ungrounded := hps_floating q.rotate180 h_qr_in_ps
            simp only [Bool.not_eq_true'] at h_ungrounded ⊢
            have h_gp : (groundedPositionsList s).any (· == q.rotate180) =
                    (groundedPositionsList s.rotate180).any (· == q) := by
                have h := mem_groundedPositions_rotate180 s q.rotate180
                simp only [QuarterPos.rotate180_rotate180, groundedPositions,
                    List.mem_toFinset] at h
                exact Bool.eq_iff_iff.mpr
                    ((any_beq_iff_mem _ _).trans (h.trans (any_beq_iff_mem _ _).symm))
            rw [← h_gp]; exact h_ungrounded
        have h_v_mem : FallingUnit.cluster c' ∈ floatingUnits s.rotate180 := by
            rw [floatingUnits_eq_append, List.mem_append]
            exact .inl (List.mem_map.mpr ⟨c', List.mem_filter.mpr ⟨hc'_mem, h_floating⟩, rfl⟩)
        exact ⟨.cluster c', h_v_mem, ⟨fun p => by
            simp only [FallingUnit.rotate180, FallingUnit.positions]
            exact (h_any_eq p).symm, rfl⟩⟩
    | inr h_pin =>
        rw [List.mem_map] at h_pin
        obtain ⟨_, _, h_eq⟩ := h_pin
        exact absurd h_eq (by intro h'; exact FallingUnit.noConfusion h')

/-- floatingUnits s の各ピンに対し、floatingUnits s.rotate180 に
    .any 等価かつ型が一致するピンユニットが存在する -/
private theorem floatingUnit_any_in_rotate180_pin (s : Shape) (p : QuarterPos)
        (hu : FallingUnit.pin p ∈ floatingUnits s) :
        ∃ v ∈ floatingUnits s.rotate180,
            (∀ q, (FallingUnit.pin p).rotate180.positions.any (· == q) = v.positions.any (· == q))
            ∧ (FallingUnit.pin p).rotate180.typeOrd = v.typeOrd := by
    rw [floatingUnits_eq_append, List.mem_append] at hu
    cases hu with
    | inl h_cluster =>
        rw [List.mem_map] at h_cluster
        obtain ⟨_, _, h_eq⟩ := h_cluster
        exact absurd h_eq (by intro h'; exact FallingUnit.noConfusion h')
    | inr h_pin =>
        rw [List.mem_map] at h_pin
        obtain ⟨p', hp_filtered, h_eq⟩ := h_pin
        have h_p_eq : p' = p := FallingUnit.pin.inj h_eq
        subst p'
        have hp_pins : p ∈ allIsolatedPins s :=
            List.mem_of_mem_filter hp_filtered
        have hp_floating_raw := (List.mem_filter.mp hp_filtered).2
        have hp_floating_bool : (groundedPositionsList s).any (· == p) = false := by
            simp only [Bool.not_eq_true', Bool.eq_false_iff] at hp_floating_raw ⊢
            exact hp_floating_raw
        have h_pin_r : p.rotate180 ∈ allIsolatedPins s.rotate180 := by
            unfold allIsolatedPins
            rw [CrystalBond.allValid_rotate180]
            rw [List.mem_filter]
            constructor
            · unfold allIsolatedPins at hp_pins
              have h_p_valid := (List.mem_filter.mp hp_pins).1
              have h_layer : p.layer < s.layerCount :=
                  (allValid_any_iff_layer' s p).mp
                      (List.any_eq_true.mpr ⟨p, h_p_valid, BEq.rfl⟩)
              have h_any := (allValid_any_iff_layer' s p.rotate180).mpr h_layer
              rw [List.any_eq_true] at h_any
              obtain ⟨y, hy, hye⟩ := h_any; exact eq_of_beq hye ▸ hy
            · rw [QuarterPos.getQuarter_rotate180]
              unfold allIsolatedPins at hp_pins
              exact (List.mem_filter.mp hp_pins).2
        have h_ungrounded_bool : (groundedPositionsList s.rotate180).any (· == p.rotate180) = false := by
            have h_gp : (groundedPositionsList s).any (· == p) =
                    (groundedPositionsList s.rotate180).any (· == p.rotate180) := by
                have h := mem_groundedPositions_rotate180 s p
                simp only [groundedPositions, List.mem_toFinset] at h
                exact Bool.eq_iff_iff.mpr
                    ((any_beq_iff_mem _ _).trans (h.trans (any_beq_iff_mem _ _).symm))
            rw [← h_gp]; exact hp_floating_bool
        have h_v_mem : FallingUnit.pin p.rotate180 ∈ floatingUnits s.rotate180 := by
            rw [floatingUnits_eq_append, List.mem_append]
            refine .inr (List.mem_map.mpr ⟨p.rotate180, ?_, rfl⟩)
            rw [List.mem_filter]
            refine ⟨h_pin_r, ?_⟩
            simp only [Bool.not_eq_true']
            exact h_ungrounded_bool
        exact ⟨.pin p.rotate180, h_v_mem, ⟨fun q => rfl, rfl⟩⟩

/-- floatingUnits s の各ユニットに対し、floatingUnits s.rotate180 に
    .any 等価かつ型が一致するユニットが存在する -/
theorem floatingUnit_any_in_rotate180 (s : Shape) (u : FallingUnit)
        (hu : u ∈ floatingUnits s) :
        ∃ v ∈ floatingUnits s.rotate180,
            (∀ p, u.rotate180.positions.any (· == p) = v.positions.any (· == p))
            ∧ u.rotate180.typeOrd = v.typeOrd := by
    cases u with
    | cluster ps =>
        simpa using floatingUnit_any_in_rotate180_cluster s ps hu
    | pin p =>
        simpa using floatingUnit_any_in_rotate180_pin s p hu

-- ============================================================
-- allValid の rotate180 Perm 補題（P5 基盤工事）
-- ============================================================
-- `allIsolatedPins_rotate180_perm` や `allStructuralClustersList_rotate180_perm`
-- を組み立てるための最低限の基盤。rotate180 は allValid の並び替え（Perm）に
-- 相当し、filter / flatMap の Perm 保存を経由して floatingUnits 全体の Perm に
-- 持ち上げる設計。

/-- `Direction.all` は `Direction.rotate180` で並び替えられてもリスト順列として等しい。
    rotate180 は ne↔sw, se↔nw を交換するため、`[ne,se,sw,nw]` と `[sw,nw,ne,se]` が
    Perm 関係にある。`allValid_rotate180_perm` の基礎。 -/
theorem Direction.all_rotate180_perm :
        Direction.all.Perm (Direction.all.map Direction.rotate180) := by
    unfold Direction.all Direction.rotate180
    decide

/-- `QuarterPos.allValid s` は `rotate180` map で並び替えても Perm として等しい。
    allValid は layer × direction の直積列挙であり、direction レベルで Perm が
    成立するため、全体としても Perm。`allIsolatedPins_rotate180_perm` などの基礎。 -/
theorem QuarterPos.allValid_rotate180_perm (s : Shape) :
        (QuarterPos.allValid s).Perm
        ((QuarterPos.allValid s).map QuarterPos.rotate180) := by
    unfold QuarterPos.allValid
    induction (List.range s.layerCount) with
    | nil => simp
    | cons h t ih =>
        simp only [List.flatMap_cons, List.map_append]
        refine List.Perm.append ?_ ih
        unfold QuarterPos.rotate180 Direction.all Direction.rotate180
        simp only [List.map_cons, List.map_nil]
        exact List.perm_append_comm
            (l₁ := [(⟨h, .ne⟩ : QuarterPos), ⟨h, .se⟩])
            (l₂ := [⟨h, .sw⟩, ⟨h, .nw⟩])

/-- waveStep は rotate180 で等変である。

    **現状（2026-04-20）**: 一時 axiom として導入。
    真定理であることは vanilla4/5/stress8 で計算検証済み（`#guard` 相当）。
    構成的証明は `docs/plans/gravity-proof-execution-plan.md` §2 S2 参照。

    **de-axiomatization 計画**:
    S3 (`waveStep_rotateCW_comm`) 同様に Perm 基盤を構築するか、
    S3 が解決された後に `Shape.rotate180_eq_rotateCW_rotateCW` + S3 を 2 回
    適用する 1 行導出に置換する（`crystallize_rotate180_comm` 等と同パターン）。 -/
axiom waveStep_rotate180_comm (s : Shape) :
        waveStep s.rotate180 = (waveStep s).rotate180

-- processWave_rotate180_comm は ProcessWave.lean に移設（2026-04-21）

end Gravity
