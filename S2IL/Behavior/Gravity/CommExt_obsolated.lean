-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Behavior.Gravity.Equivariance_obsolated

namespace Gravity

open _root_.QuarterPos (getQuarter_rotate180)
-- ============================================================
-- 浮遊位置の .any メンバーシップ等変性
-- ============================================================

/-- 非空・非接地・valid な位置は floatingUnits の位置に含まれる -/
theorem ungrounded_in_floatingUnits_positions (s : Shape) (p : QuarterPos)
        (h_valid : p.layer < s.layerCount)
        (h_ne : ∃ q, p.getQuarter s = some q ∧ !q.isEmpty = true)
        (h_ug : p ∉ groundedPositions s) :
        ((floatingUnits s).flatMap FallingUnit.positions).any (· == p) = true := by
    have h_ug_bool := (not_mem_groundedPositions_iff s p).mp h_ug
    obtain ⟨q, hq_some, hq_ne⟩ := h_ne
    have h_cases : q = .pin ∨ q.canFormBond = true := by
        cases q with
        | empty => simp only [Quarter.isEmpty, decide_true, Bool.not_true, Bool.false_eq_true] at hq_ne
        | pin => exact .inl rfl
        | crystal => exact .inr rfl
        | colored => exact .inr rfl
    have h_p_allValid : p ∈ QuarterPos.allValid s := by
        have h_any := (allValid_any_iff_layer' s p).mpr h_valid
        rw [List.any_eq_true] at h_any
        obtain ⟨x, hx, hxe⟩ := h_any; exact eq_of_beq hxe ▸ hx
    cases h_cases with
    | inl h_pin =>
        subst h_pin
        rw [List.any_eq_true]
        exact ⟨p, List.mem_flatMap.mpr ⟨.pin p, by
            unfold floatingUnits
            simp_rw [decide_not_mem_groundedPositions]
            apply List.mem_append_right
            exact List.mem_map.mpr ⟨p, List.mem_filter.mpr
                ⟨by unfold allIsolatedPins
                    exact List.mem_filter.mpr ⟨h_p_allValid, by rw [hq_some]⟩,
                 by simp only [h_ug_bool, Bool.not_false]⟩, rfl⟩,
            by simp only [FallingUnit.positions, List.mem_cons, List.not_mem_nil, or_false]⟩, BEq.rfl⟩
    | inr h_bond =>
        have h_bondable : match p.getQuarter s with
                | some qq => qq.canFormBond = true | none => False := by
            rw [hq_some]; exact h_bond
        have h_covers := allStructuralClustersList_covers s p h_valid h_bondable
        rw [List.any_eq_true] at h_covers
        obtain ⟨c, hc_mem, hc_has_p⟩ := h_covers
        obtain ⟨pos, hc_is_sc, _, _⟩ :=
            allStructuralClustersList_is_structuralClusterList s c hc_mem
        have h_all_ug : c.all
                (fun x => !((groundedPositionsList s).any (· == x))) = true := by
            rw [List.all_eq_true]; intro x hx
            cases h_x_ground : (groundedPositionsList s).any (· == x) with
            | false => rfl
            | true =>
                exfalso
                have h_x_in_sc : (structuralClusterList s pos).any (· == x) = true :=
                    hc_is_sc ▸ List.any_eq_true.mpr ⟨x, hx, BEq.rfl⟩
                have h_p_in_sc := hc_is_sc ▸ hc_has_p
                have h_reach_pos_x := structuralClusterList_sound s pos x h_x_in_sc
                have h_reach_pos_p := structuralClusterList_sound s pos p h_p_in_sc
                have h_reach_x_pos := genericReachable_reverse
                    (fun a b => isStructurallyBonded_symm s a b) h_reach_pos_x
                have h_reach_x_p :=
                    genericReachable_trans h_reach_x_pos h_reach_pos_p
                -- isStructurallyBonded ⊆ groundingEdge なので mono リフト
                have h_reach_ge := h_reach_x_p.mono
                    (fun _ _ h => groundingEdge_of_isStructurallyBonded h)
                -- x が groundedPositionsList に含まれ、groundingEdge で p に到達可能
                -- → groundedPositionsList_closed により p も含まれる → 矛盾
                have h_p_ground := groundedPositionsList_closed s x p
                    h_x_ground h_reach_ge
                rw [h_ug_bool] at h_p_ground
                exact absurd h_p_ground (by decide)
        rw [List.any_eq_true]
        have h_p_mem : p ∈ c := by
            rw [List.any_eq_true] at hc_has_p
            obtain ⟨y, hy, hye⟩ := hc_has_p; exact eq_of_beq hye ▸ hy
        exact ⟨p, List.mem_flatMap.mpr ⟨.cluster c, by
            unfold floatingUnits
            simp_rw [decide_not_mem_groundedPositions]
            apply List.mem_append_left
            exact List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc_mem, h_all_ug⟩, rfl⟩,
            h_p_mem⟩, BEq.rfl⟩

/-- floatingUnits の位置にある象限は非空である -/
theorem floatingUnits_positions_getQuarter (s : Shape) (p : QuarterPos)
        (h : ((floatingUnits s).flatMap FallingUnit.positions).any (· == p) = true) :
        p.layer < s.layerCount ∧
        (∃ q, p.getQuarter s = some q ∧ !q.isEmpty = true) ∧
        p ∉ groundedPositions s := by
    rw [List.any_eq_true] at h
    obtain ⟨q, hq_mem, hq_eq⟩ := h
    have := eq_of_beq hq_eq; subst this
    rw [List.mem_flatMap] at hq_mem
    obtain ⟨u, hu_mem, hq_in_u⟩ := hq_mem
    unfold floatingUnits at hu_mem
    simp_rw [decide_not_mem_groundedPositions] at hu_mem
    simp only [List.mem_append, List.mem_map] at hu_mem
    cases hu_mem with
    | inl h_cluster =>
        obtain ⟨c, hc_filt, hc_eq⟩ := h_cluster; subst hc_eq
        rw [List.mem_filter] at hc_filt
        obtain ⟨hc_in_all, hc_all_ug⟩ := hc_filt
        obtain ⟨pos, hc_is_sc, _, qq, hqq, h_bond⟩ :=
            allStructuralClustersList_is_structuralClusterList s c hc_in_all
        have h_q_in_sc : (structuralClusterList s pos).any (· == q) = true :=
            hc_is_sc ▸ List.any_eq_true.mpr ⟨q, hq_in_u, BEq.rfl⟩
        -- q は canFormBond (構造的到達可能性から)
        have h_reach := structuralClusterList_sound s pos q h_q_in_sc
        have h_q_bond := structuralReachable_canFormBond s pos q h_reach ⟨qq, hqq, h_bond⟩
        obtain ⟨w, hw, hwb⟩ := h_q_bond
        -- q.layer < s.layerCount: getQuarter が some → layer は範囲内
        have h_q_valid : q.layer < s.layerCount := by
            simp only [Shape.layerCount]
            have hq := hw; unfold QuarterPos.getQuarter at hq
            cases hl : s.layers[q.layer]? with
            | none => simp only [hl, reduceCtorEq] at hq
            | some _ => exact (List.getElem?_eq_some_iff.mp hl).1
        -- q は非接地
        have h_q_ug : (groundedPositionsList s).any (· == q) = false := by
            have := (List.all_eq_true.mp hc_all_ug) q hq_in_u
            revert this; cases (groundedPositionsList s).any (· == q) <;> simp only [Bool.not_false, imp_self, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false]
        -- q は非空
        have h_q_ne : ∃ qq', q.getQuarter s = some qq' ∧ !qq'.isEmpty = true :=
            ⟨w, hw, by cases w <;> simp only [Quarter.canFormBond, Bool.false_eq_true, Quarter.isEmpty, decide_false, Bool.not_false] at hwb ⊢⟩
        exact ⟨h_q_valid, h_q_ne, (not_mem_groundedPositions_iff s q).mpr h_q_ug⟩
    | inr h_pin =>
        obtain ⟨p0, hp0_filt, hp0_eq⟩ := h_pin; subst hp0_eq
        rw [List.mem_filter] at hp0_filt
        obtain ⟨hp0_iso, hp0_ug⟩ := hp0_filt
        simp only [FallingUnit.positions, List.mem_singleton] at hq_in_u; subst hq_in_u
        unfold allIsolatedPins at hp0_iso
        rw [List.mem_filter] at hp0_iso
        obtain ⟨hp0_allValid, hp0_is_pin⟩ := hp0_iso
        have h_valid : q.layer < s.layerCount :=
            (allValid_any_iff_layer' s q).mp
                (List.any_eq_true.mpr ⟨q, hp0_allValid, BEq.rfl⟩)
        have h_ne : ∃ qq', q.getQuarter s = some qq' ∧ !qq'.isEmpty = true := by
            cases hgq : q.getQuarter s with
            | none => simp only [hgq, Bool.false_eq_true] at hp0_is_pin
            | some v => cases v <;> simp_all only [BEq.rfl, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false, beq_iff_eq, Bool.false_eq_true, Option.some.injEq, Quarter.isEmpty, Bool.decide_eq_true, exists_eq_left']
        have h_ug : (groundedPositionsList s).any (· == q) = false := by
            revert hp0_ug; cases (groundedPositionsList s).any (· == q) <;> simp only [Bool.not_false, imp_self, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false]
        exact ⟨h_valid, h_ne, (not_mem_groundedPositions_iff s q).mpr h_ug⟩

/-- 浮遊単位の位置メンバーシップは rotate180 で保存される -/
theorem falling_positions_any_rotate180 (s : Shape) (p : QuarterPos) :
        ((floatingUnits s).flatMap FallingUnit.positions).any (· == p) =
        ((floatingUnits s.rotate180).flatMap FallingUnit.positions).any (· == p.rotate180) := by
    cases h : ((floatingUnits s).flatMap FallingUnit.positions).any (· == p) with
    | true =>
        symm
        -- p は valid, non-empty, non-grounded
        obtain ⟨h_valid, ⟨q, hq, hq_ne⟩, h_ug⟩ := floatingUnits_positions_getQuarter s p h
        -- p.r180 は s.r180 で valid, non-empty, non-grounded
        apply ungrounded_in_floatingUnits_positions s.rotate180 p.rotate180
        · rw [Shape.layerCount_rotate180]; exact h_valid
        · exact ⟨q, by rw [getQuarter_rotate180]; exact hq, hq_ne⟩
        · exact fun h => h_ug ((mem_groundedPositions_rotate180 s p).mpr h)
    | false =>
        symm
        cases h' : ((floatingUnits s.rotate180).flatMap FallingUnit.positions).any
                (· == p.rotate180) with
        | false => rfl
        | true =>
            exfalso
            obtain ⟨h_valid', ⟨q', hq', hq_ne'⟩, h_ug'⟩ :=
                floatingUnits_positions_getQuarter s.rotate180 p.rotate180 h'
            have h_should_be_true := ungrounded_in_floatingUnits_positions s p
                (by rw [← Shape.layerCount_rotate180]; exact h_valid')
                ⟨q', by rw [← getQuarter_rotate180]; exact hq', hq_ne'⟩
                (fun hp => h_ug' ((mem_groundedPositions_rotate180 s p).mp hp))
            rw [h] at h_should_be_true; exact absurd h_should_be_true (by decide)

/-- QuarterPos の BEq は rotate180 で交換可能: (x.r180 == p) = (x == p.r180) -/
theorem beq_rotate180_comm (x p : QuarterPos) :
        (x.rotate180 == p) = (x == p.rotate180) := by
    have h := σ_r180.quarterPos_beq x p.rotate180
    simp only [QuarterPos.rotate180_rotate180] at h
    exact h

/-- List.map QuarterPos.rotate180 後の .any と rotate180 の関係（公開版） -/
theorem any_map_rotate180_beq (ps : List QuarterPos) (p : QuarterPos) :
        (ps.map QuarterPos.rotate180).any (· == p) =
        ps.any (· == p.rotate180) := by
    induction ps with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.map, List.any, ih, beq_rotate180_comm]

-- ============================================================
-- settle_foldl_eq: foldl 等価性の証明基盤
-- ============================================================

/-- .any BEq メンバーシップ等価から任意述語の .any 等価を導く -/
theorem any_pred_ext {l1 l2 : List QuarterPos}
        (h : ∀ p, l1.any (· == p) = l2.any (· == p)) (f : QuarterPos → Bool) :
        l1.any f = l2.any f := by
    cases h1 : l1.any f with
    | true =>
        symm; rw [List.any_eq_true] at h1 ⊢
        obtain ⟨x, hx_mem, hfx⟩ := h1
        have : l1.any (· == x) = true := List.any_eq_true.mpr ⟨x, hx_mem, BEq.rfl⟩
        rw [h] at this
        obtain ⟨y, hy_mem, hy_beq⟩ := List.any_eq_true.mp this
        have hyx : y = x := eq_of_beq (show (y == x) = true from hy_beq)
        exact ⟨x, hyx ▸ hy_mem, hfx⟩
    | false =>
        symm; cases h2 : l2.any f with
        | false => rfl
        | true =>
            exfalso
            obtain ⟨x, hx_mem, hfx⟩ := List.any_eq_true.mp h2
            have : l2.any (· == x) = true := List.any_eq_true.mpr ⟨x, hx_mem, BEq.rfl⟩
            rw [← h] at this
            obtain ⟨y, hy_mem, hy_beq⟩ := List.any_eq_true.mp this
            have hyx : y = x := eq_of_beq (show (y == x) = true from hy_beq)
            have : l1.any f = true := List.any_eq_true.mpr ⟨x, hyx ▸ hy_mem, hfx⟩
            rw [h1] at this; exact Bool.false_ne_true this

/-- foldl min は初期値以下 -/
theorem foldl_min_le_init (l : List QuarterPos) (init : Nat) :
        l.foldl (fun acc q => min acc q.layer) init ≤ init := by
    induction l generalizing init with
    | nil => simp only [List.foldl, Std.le_refl]
    | cons x xs ih =>
        simp only [List.foldl]
        exact Nat.le_trans (ih (min init x.layer)) (Nat.min_le_left init x.layer)

/-- foldl min はリスト要素の layer 以下 -/
theorem foldl_min_le_elem (l : List QuarterPos) (init : Nat) (q : QuarterPos)
        (hq : q ∈ l) :
        l.foldl (fun acc p => min acc p.layer) init ≤ q.layer := by
    induction l generalizing init with
    | nil => nomatch hq
    | cons x xs ih =>
        simp only [List.foldl]
        cases hq with
        | head =>
            exact Nat.le_trans (foldl_min_le_init xs (min init q.layer))
                (Nat.min_le_right init q.layer)
        | tail _ hmem =>
            exact ih (min init x.layer) hmem

/-- cons リストの foldl min はどの要素の layer 以下 -/
theorem foldl_min_le_mem (p : QuarterPos) (rest : List QuarterPos) (x : QuarterPos)
        (hx : x ∈ p :: rest) :
        rest.foldl (fun acc q => min acc q.layer) p.layer ≤ x.layer := by
    cases hx with
    | head => exact foldl_min_le_init rest p.layer
    | tail _ hmem => exact foldl_min_le_elem rest p.layer x hmem

/-- foldl min の結果は init か、リスト要素の layer に等しい -/
theorem foldl_min_attained (l : List QuarterPos) (init : Nat) :
        l.foldl (fun acc q => min acc q.layer) init = init ∨
        ∃ q ∈ l, l.foldl (fun acc q => min acc q.layer) init = q.layer := by
    induction l generalizing init with
    | nil => exact Or.inl rfl
    | cons x xs ih =>
        simp only [List.foldl]
        cases ih (min init x.layer) with
        | inl heq =>
            by_cases hle : init ≤ x.layer
            · exact Or.inl (heq.trans (Nat.min_eq_left hle))
            · exact Or.inr ⟨x, .head xs, heq.trans (by omega)⟩
        | inr hexist =>
            obtain ⟨q, hq_mem, hq_eq⟩ := hexist
            exact Or.inr ⟨q, .tail x hq_mem, hq_eq⟩

/-- .any BEq 等価リストの逆方向メンバーシップ -/
theorem mem_of_any_beq_eq {l1 l2 : List QuarterPos}
        (h : ∀ p, l1.any (· == p) = l2.any (· == p))
        {x : QuarterPos} (hx : x ∈ l2) : x ∈ l1 := by
    have : l2.any (· == x) = true := List.any_eq_true.mpr ⟨x, hx, BEq.rfl⟩
    rw [← h] at this
    obtain ⟨y, hy_mem, hy_beq⟩ := List.any_eq_true.mp this
    have hyx : y = x := eq_of_beq hy_beq
    subst hyx; exact hy_mem

/-- positions の .any BEq 等価な FallingUnit は同じ minLayer を持つ -/
theorem minLayer_ext {u1 u2 : FallingUnit}
        (h : ∀ p, u1.positions.any (· == p) = u2.positions.any (· == p)) :
        u1.minLayer = u2.minLayer := by
    simp only [FallingUnit.minLayer]
    -- positions をローカル変数に一般化する
    generalize hl1 : u1.positions = l1
    generalize hl2 : u2.positions = l2
    rw [hl1, hl2] at h
    cases l1 with
    | nil =>
        simp only []
        cases l2 with
        | nil => rfl
        | cons p2 rest2 =>
            exfalso
            have : (p2 :: rest2).any (· == p2) = true :=
                List.any_eq_true.mpr ⟨p2, .head rest2, BEq.rfl⟩
            rw [← h] at this; exact Bool.false_ne_true this
    | cons p1 rest1 =>
        cases l2 with
        | nil =>
            simp only []
            exfalso
            have : (p1 :: rest1).any (· == p1) = true :=
                List.any_eq_true.mpr ⟨p1, .head rest1, BEq.rfl⟩
            rw [h] at this; exact Bool.false_ne_true this
        | cons p2 rest2 =>
            simp only []
            apply Nat.le_antisymm
            · -- rest1.foldl ... p1.layer ≤ rest2.foldl ... p2.layer
              cases foldl_min_attained rest2 p2.layer with
              | inl heq =>
                  rw [heq]
                  exact foldl_min_le_mem p1 rest1 p2
                      (mem_of_any_beq_eq h (.head rest2))
              | inr hexist =>
                  obtain ⟨q, hq_mem, hq_eq⟩ := hexist
                  rw [hq_eq]
                  exact foldl_min_le_mem p1 rest1 q
                      (mem_of_any_beq_eq h (.tail p2 hq_mem))
            · -- rest2.foldl ... p2.layer ≤ rest1.foldl ... p1.layer
              cases foldl_min_attained rest1 p1.layer with
              | inl heq =>
                  rw [heq]
                  exact foldl_min_le_mem p2 rest2 p1
                      (mem_of_any_beq_eq (fun p => (h p).symm) (.head rest1))
              | inr hexist =>
                  obtain ⟨q, hq_mem, hq_eq⟩ := hexist
                  rw [hq_eq]
                  exact foldl_min_le_mem p2 rest2 q
                      (mem_of_any_beq_eq (fun p => (h p).symm) (.tail p1 hq_mem))

/-- positions の .any 等価な FallingUnit は同じ landingDistance を持つ -/
theorem landingDistance_ext {u1 u2 : FallingUnit}
        (h : ∀ p, u1.positions.any (· == p) = u2.positions.any (· == p))
        (obs : List Layer) :
        landingDistance u1 obs = landingDistance u2 obs := by
    have h_ml : u1.minLayer = u2.minLayer := minLayer_ext h
    simp only [landingDistance]
    rw [h_ml]
    suffices ∀ d fuel, landingDistance.check obs u1.positions u2.minLayer d fuel =
                       landingDistance.check obs u2.positions u2.minLayer d fuel from
        this 1 (u2.minLayer + 1)
    intro d fuel
    induction fuel generalizing d with
    | zero => rfl
    | succ n ih =>
        simp only [landingDistance.check, any_pred_ext h, ih]

-- ============================================================
-- placeFallingUnit_ext / settle_foldl_eq の補助補題群
-- ============================================================

/-- setDir は異なる方角で可換 -/
theorem setDir_setDir_comm (l : Layer) {d1 d2 : Direction}
        (q1 q2 : Quarter) (h : d1 ≠ d2) :
        QuarterPos.setDir (QuarterPos.setDir l d1 q1) d2 q2 =
        QuarterPos.setDir (QuarterPos.setDir l d2 q2) d1 q1 := by
    cases d1 <;> cases d2 <;> simp_all only [ne_eq, not_true_eq_false, reduceCtorEq, not_false_eq_true, QuarterPos.setDir]

/-- setDir は同方角で上書き -/
theorem setDir_setDir_same (l : Layer) (d : Direction) (q1 q2 : Quarter) :
        QuarterPos.setDir (QuarterPos.setDir l d q1) d q2 =
        QuarterPos.setDir l d q2 := by
    cases d <;> rfl

/-- placeQuarter の完全な getElem? 特性 -/
theorem placeQuarter_getElem?_full (obs : List Layer) (lay i : Nat)
        (d : Direction) (q : Quarter) :
        (placeQuarter obs lay d q)[i]? =
        if i < max obs.length (lay + 1) then
          if i = lay then some (QuarterPos.setDir (obs.getD lay Layer.empty) d q)
          else some (obs.getD i Layer.empty)
        else none := by
    -- placeQuarter の let 束縛を場合分けで展開
    by_cases hlt : lay < obs.length
    · -- lay < obs.length の場合: extended = obs
      have hmax : max obs.length (lay + 1) = obs.length := by omega
      have hpq : placeQuarter obs lay d q =
          obs.set lay (QuarterPos.setDir (obs.getD lay Layer.empty) d q) := by
        unfold placeQuarter
        simp only [hlt, ite_true, List.getElem?_eq_getElem hlt]
        congr 1
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
        rfl
      rw [hpq, hmax]
      by_cases hi : i < obs.length
      · rw [if_pos hi]
        by_cases heq : i = lay
        · subst heq; rw [if_pos rfl]
          simp only [List.getD_eq_getElem?_getD, hi, getElem?_pos, Option.getD_some, List.length_set, List.getElem_set_self]
        · rw [if_neg heq]
          have hne : lay ≠ i := fun h => heq h.symm
          simp only [List.getD_eq_getElem?_getD, List.length_set, hi, getElem?_pos, ne_eq, hne, not_false_eq_true, List.getElem_set_ne, Option.getD_some]
      · rw [if_neg hi]
        rw [List.getElem?_eq_none_iff.mpr (by simp only [List.getD_eq_getElem?_getD, List.length_set]; omega)]
    · -- lay ≥ obs.length の場合: extended = obs ++ replicate ...
      have hmax : max obs.length (lay + 1) = lay + 1 := by omega
      have hext_len : (obs ++ List.replicate (lay + 1 - obs.length) Layer.empty).length =
          lay + 1 := by simp only [List.length_append, List.length_replicate]; omega
      have hlay : lay < (obs ++ List.replicate (lay + 1 - obs.length) Layer.empty).length := by
        rw [hext_len]; omega
      have hpq : placeQuarter obs lay d q =
          (obs ++ List.replicate (lay + 1 - obs.length) Layer.empty).set lay
          (QuarterPos.setDir Layer.empty d q) := by
        unfold placeQuarter
        simp only [show ¬(lay < obs.length) from by omega, ite_false,
            List.getElem?_eq_getElem hlay]
        congr 1
        rw [List.getElem_append_right (by omega)]
        simp only [List.getElem_replicate]
      have hgetD_lay : obs.getD lay Layer.empty = Layer.empty := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr (by omega)]
        rfl
      rw [hpq, hmax, hgetD_lay]
      by_cases hi : i < lay + 1
      · rw [if_pos hi]
        by_cases heq : i = lay
        · subst heq; rw [if_pos rfl]
          simp only [List.length_set, hext_len, Nat.lt_add_one, getElem?_pos, List.getElem_set_self]
        · rw [if_neg heq]
          have hne : lay ≠ i := fun h => heq h.symm
          simp only [List.getElem?_set, hne, ite_false, hext_len]
          rw [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append]
          split
          · rename_i hi2; rw [List.getElem?_eq_getElem hi2]; rfl
          · rename_i hi2
            simp only [List.getElem?_replicate]
            split
            · have : obs[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
              simp only [this, Option.getD_none]
            · omega
      · rw [if_neg hi]
        rw [List.getElem?_eq_none_iff.mpr (by simp only [List.length_set, hext_len]; omega)]

/-- placeQuarter の結果のリスト長 -/
theorem placeQuarter_length (obs : List Layer) (lay : Nat)
        (d : Direction) (q : Quarter) :
        (placeQuarter obs lay d q).length = max obs.length (lay + 1) := by
    apply Nat.le_antisymm
    · -- ≤: index = max では getElem? が none
      exact List.getElem?_eq_none_iff.mp (by
        have := placeQuarter_getElem?_full obs lay (max obs.length (lay + 1)) d q
        rw [if_neg (by omega)] at this; exact this)
    · -- ≥: length < max なら index = length で some が返り矛盾
      have : ¬((placeQuarter obs lay d q).length < max obs.length (lay + 1)) := by
        intro hlt
        have h := placeQuarter_getElem?_full obs lay (placeQuarter obs lay d q).length d q
        rw [List.getElem?_eq_none_iff.mpr (by omega), if_pos hlt] at h
        split at h <;> contradiction
      omega

/-- placeQuarter の getD 特性（範囲内） -/
theorem placeQuarter_getD (obs : List Layer) (lay i : Nat)
        (d : Direction) (q : Quarter)
        (hi : i < max obs.length (lay + 1)) :
        (placeQuarter obs lay d q).getD i Layer.empty =
        if i = lay then QuarterPos.setDir (obs.getD lay Layer.empty) d q
        else obs.getD i Layer.empty := by
    rw [List.getD_eq_getElem?_getD, placeQuarter_getElem?_full, if_pos hi]
    split <;> simp only [List.getD_eq_getElem?_getD, Option.getD_some]

/-- placeQuarter の getD 特性（i ≠ lay のとき境界条件不要） -/
theorem placeQuarter_getD_ne (obs : List Layer) (lay i : Nat)
        (d : Direction) (q : Quarter) (hne : i ≠ lay) :
        (placeQuarter obs lay d q).getD i Layer.empty = obs.getD i Layer.empty := by
    rw [List.getD_eq_getElem?_getD, placeQuarter_getElem?_full]
    by_cases hi : i < max obs.length (lay + 1)
    · rw [if_pos hi, if_neg hne]; simp only [List.getD_eq_getElem?_getD, Option.getD_some]
    · rw [if_neg hi]
      simp only [Option.getD_none, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none_iff.mpr (show obs.length ≤ i by omega)]

/-- placeQuarter は同引数で冪等 -/
theorem placeQuarter_idem (obs : List Layer) (lay : Nat)
        (d : Direction) (q : Quarter) :
        placeQuarter (placeQuarter obs lay d q) lay d q =
        placeQuarter obs lay d q := by
    apply List.ext_getElem?; intro i
    rw [placeQuarter_getElem?_full, placeQuarter_getElem?_full]
    simp only [placeQuarter_length,
        show max (max obs.length (lay + 1)) (lay + 1) = max obs.length (lay + 1) from by omega]
    split
    · rename_i hi
      split
      · rename_i heq; subst heq
        congr 1
        rw [placeQuarter_getD _ _ _ _ _ (by omega)]
        simp only [↓reduceIte, List.getD_eq_getElem?_getD, setDir_setDir_same]
      · rename_i hne; congr 1
        rw [placeQuarter_getD _ _ _ _ _ (by omega)]
        simp only [hne, ↓reduceIte, List.getD_eq_getElem?_getD]
    · rfl

/-- placeQuarter は異なる対象レイヤで可換 -/
theorem placeQuarter_comm_layer_ne (obs : List Layer)
        (l1 l2 : Nat) (d1 d2 : Direction) (q1 q2 : Quarter)
        (hne : l1 ≠ l2) :
        placeQuarter (placeQuarter obs l1 d1 q1) l2 d2 q2 =
        placeQuarter (placeQuarter obs l2 d2 q2) l1 d1 q1 := by
    apply List.ext_getElem?; intro i
    simp only [placeQuarter_getElem?_full, placeQuarter_length]
    have hmax : max (max obs.length (l1 + 1)) (l2 + 1) =
                max (max obs.length (l2 + 1)) (l1 + 1) := by omega
    rw [hmax]
    by_cases hi : i < max (max obs.length (l2 + 1)) (l1 + 1)
    · rw [if_pos hi, if_pos hi]
      by_cases hil2 : i = l2
      · subst hil2
        rw [if_pos rfl, if_neg (Ne.symm hne)]
        congr 1
        rw [placeQuarter_getD_ne _ _ _ _ _ (Ne.symm hne)]
        rw [placeQuarter_getD _ _ _ _ _ (by omega)]
        simp only [List.getD_eq_getElem?_getD, ↓reduceIte]
      · rw [if_neg hil2]
        by_cases hil1 : i = l1
        · subst hil1
          rw [if_pos rfl]
          congr 1
          rw [placeQuarter_getD _ _ _ _ _ (by omega)]
          rw [placeQuarter_getD_ne _ _ _ _ _ hne]
          simp only [↓reduceIte, List.getD_eq_getElem?_getD]
        · rw [if_neg hil1]
          congr 1
          rw [placeQuarter_getD_ne _ _ _ _ _ hil1]
          rw [placeQuarter_getD_ne _ _ _ _ _ hil2]
    · rw [if_neg hi, if_neg hi]

/-- placeQuarter は同レイヤ・異方角で可換 -/
theorem placeQuarter_comm_dir_ne (obs : List Layer)
        (lay : Nat) (d1 d2 : Direction) (q1 q2 : Quarter)
        (hne : d1 ≠ d2) :
        placeQuarter (placeQuarter obs lay d1 q1) lay d2 q2 =
        placeQuarter (placeQuarter obs lay d2 q2) lay d1 q1 := by
    apply List.ext_getElem?; intro i
    simp only [placeQuarter_getElem?_full, placeQuarter_length,
        show max (max obs.length (lay + 1)) (lay + 1) = max obs.length (lay + 1) from by omega]
    split
    · rename_i hi
      split
      · rename_i heq; subst heq
        congr 1
        rw [placeQuarter_getD _ _ _ _ _ (by omega)]
        rw [placeQuarter_getD _ _ _ _ _ (by omega)]
        simp only [↓reduceIte, List.getD_eq_getElem?_getD, setDir_setDir_comm _ _ _ hne]
      · rename_i hne2; congr 1
        rw [placeQuarter_getD _ _ _ _ _ (by omega)]
        rw [placeQuarter_getD _ _ _ _ _ (by omega)]
        simp only [hne2, ↓reduceIte, List.getD_eq_getElem?_getD]
    · rfl

/-- 可換・冪等な操作の foldl 吸収: x ∈ l のとき事前適用は吸収される
    可換性・冪等性は述語 S を満たす要素間でのみ要求される -/
theorem foldl_absorb {β : Type}
        (f : β → QuarterPos → β) (S : QuarterPos → Prop)
        (h_comm : ∀ p1 p2, S p1 → S p2 → p1 ≠ p2 → ∀ s, f (f s p1) p2 = f (f s p2) p1)
        (h_idem : ∀ p, S p → ∀ s, f (f s p) p = f s p)
        (x : QuarterPos) (hsx : S x)
        (l : List QuarterPos) (hl : ∀ y, y ∈ l → S y) (hx : x ∈ l)
        (init : β) :
        l.foldl f (f init x) = l.foldl f init := by
    induction l generalizing init with
    | nil => contradiction
    | cons y ys ih =>
        simp only [List.foldl_cons]
        have hsy : S y := hl y (.head ys)
        have hys : ∀ z, z ∈ ys → S z := fun z hz => hl z (.tail y hz)
        cases List.mem_cons.mp hx with
        | inl heq =>
            subst heq; rw [h_idem x hsx]
        | inr hx_ys =>
            by_cases hxy : x = y
            · subst hxy; rw [h_idem x hsx]
            · rw [h_comm x y hsx hsy hxy]; exact ih hys hx_ys _

/-- 可換・冪等な操作の foldl 抽出: x 要素を前に出せる
    可換性・冪等性は述語 S を満たす要素間でのみ要求される -/
theorem foldl_extract {β : Type}
        (f : β → QuarterPos → β) (S : QuarterPos → Prop)
        (h_comm : ∀ p1 p2, S p1 → S p2 → p1 ≠ p2 → ∀ s, f (f s p1) p2 = f (f s p2) p1)
        (h_idem : ∀ p, S p → ∀ s, f (f s p) p = f s p)
        (x : QuarterPos) (hsx : S x)
        (l : List QuarterPos) (hl : ∀ y, y ∈ l → S y) (hx : x ∈ l)
        (init : β) :
        l.foldl f init = (l.filter (! · == x)).foldl f (f init x) := by
    induction l generalizing init with
    | nil => contradiction
    | cons y ys ih =>
        simp only [List.foldl_cons, List.filter_cons]
        have hsy : S y := hl y (.head ys)
        have hys : ∀ z, z ∈ ys → S z := fun z hz => hl z (.tail y hz)
        cases List.mem_cons.mp hx with
        | inl heq =>
            subst heq
            simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            by_cases hxys : x ∈ ys
            · rw [foldl_absorb f S h_comm h_idem x hsx ys hys hxys]
              exact ih hys hxys _
            · congr 1; symm
              rw [List.filter_eq_self]
              intro a ha
              cases hab : (a == x) with
              | false => rfl
              | true => exact absurd (eq_of_beq hab ▸ ha) hxys
        | inr hx_ys =>
            by_cases hxy : y = x
            · -- subst hxy で x が y に置換される
              subst hxy
              simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              rw [foldl_absorb f S h_comm h_idem y hsy ys hys hx_ys]
              exact ih hys hx_ys _
            · have : (! (y == x)) = true := by simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq, hxy, not_false_eq_true]
              simp only [this, ↓reduceIte, List.foldl_cons]
              rw [h_comm x y hsx hsy (Ne.symm hxy)]
              exact ih hys hx_ys _

/-- .any BEq 等価なリストは可換・冪等な foldl で同一結果を生む
    可換性・冪等性は述語 S を満たす要素間でのみ要求される -/
theorem foldl_any_eq_of_comm_idem {β : Type}
        (f : β → QuarterPos → β) (S : QuarterPos → Prop)
        (h_comm : ∀ p1 p2, S p1 → S p2 → p1 ≠ p2 → ∀ s, f (f s p1) p2 = f (f s p2) p1)
        (h_idem : ∀ p, S p → ∀ s, f (f s p) p = f s p)
        (l1 l2 : List QuarterPos)
        (hl1 : ∀ y, y ∈ l1 → S y) (hl2 : ∀ y, y ∈ l2 → S y)
        (h : ∀ p, l1.any (· == p) = l2.any (· == p))
        (init : β) :
        l1.foldl f init = l2.foldl f init := by
    induction l1 generalizing l2 init with
    | nil =>
        cases l2 with
        | nil => rfl
        | cons y ys =>
            exfalso
            have : (y :: ys).any (· == y) = true :=
                List.any_eq_true.mpr ⟨y, .head ys, beq_self_eq_true y⟩
            rw [← h] at this
            exact Bool.false_ne_true this
    | cons x xs ih =>
        simp only [List.foldl_cons]
        have hsx : S x := hl1 x (.head xs)
        have hl1_xs : ∀ z, z ∈ xs → S z := fun z hz => hl1 z (.tail x hz)
        -- x ∈ l2
        have hx_l2 : x ∈ l2 := by
            have h1 : l2.any (· == x) = true := by
                rw [← h]
                exact List.any_eq_true.mpr ⟨x, .head xs, beq_self_eq_true x⟩
            obtain ⟨y, hy_mem, hy_beq⟩ := List.any_eq_true.mp h1
            exact eq_of_beq hy_beq ▸ hy_mem
        by_cases hx_xs : x ∈ xs
        · -- x ∈ xs: xs の .any は l1 の .any と同じ
          have h_any_xs : ∀ p, xs.any (· == p) = l2.any (· == p) := by
              intro p
              have hp := h p
              simp only [List.any_cons] at hp
              cases hbool : (x == p) with
              | true =>
                  simp only [hbool, Bool.true_or] at hp
                  have h_xs_true : xs.any (· == p) = true :=
                      List.any_eq_true.mpr ⟨x, hx_xs, hbool⟩
                  rw [h_xs_true]; exact hp
              | false =>
                  simp only [hbool, Bool.false_or] at hp
                  exact hp
          rw [foldl_absorb f S h_comm h_idem x hsx xs hl1_xs hx_xs]
          exact ih l2 hl1_xs hl2 h_any_xs _
        · -- x ∉ xs: filter で x を除去
          have hl2_filter : ∀ y, y ∈ l2.filter (! · == x) → S y :=
              fun y hy => hl2 y (List.mem_filter.mp hy).1
          have h_any_filter : ∀ p, xs.any (· == p) =
                  (l2.filter (! · == x)).any (· == p) := by
              intro p
              rw [List.any_filter]
              by_cases hpx : p = x
              · -- p = x case: rw で置換（subst を避ける）
                rw [hpx]
                have h_lhs : xs.any (· == x) = false := by
                    rw [Bool.eq_false_iff]
                    intro h_contra
                    have ⟨a, ha, hax⟩ := List.any_eq_true.mp h_contra
                    exact hx_xs (eq_of_beq hax ▸ ha)
                have h_rhs : l2.any (fun a => (! (a == x)) && (a == x)) = false := by
                    rw [Bool.eq_false_iff]
                    intro h_contra
                    have ⟨a, _, hax⟩ := List.any_eq_true.mp h_contra
                    simp only [Bool.not_and_self, Bool.false_eq_true] at hax
                rw [h_lhs, h_rhs]
              · have hne_comm : (! (x == p)) = true := by
                    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq]; exact Ne.symm hpx
                -- (fun a => (!(a == x)) && (a == p)) を (· == p) に簡約
                have h_filter_eq : (fun a : QuarterPos => (!(a == x)) && (a == p)) = (· == p) := by
                    funext a
                    cases hap : (a == p) with
                    | false => simp only [Bool.and_false]
                    | true =>
                        -- a = p なので !(a == x) = !(p == x) = true
                        have haeqp : a = p := eq_of_beq hap
                        rw [haeqp]
                        rw [show (p == x) = (x == p) from BEq.comm]
                        simp only [hne_comm, Bool.and_self]
                simp only [h_filter_eq]
                have hp := h p
                simp only [List.any_cons] at hp
                cases hbool : (x == p) with
                | true => exact absurd (eq_of_beq hbool) (Ne.symm hpx)
                | false => simp only [hbool, Bool.false_or] at hp; exact hp
          rw [foldl_extract f S h_comm h_idem x hsx l2 hl2 hx_l2]
          exact ih _ hl1_xs hl2_filter h_any_filter _

/-- minLayer 以下の d に対し、positions 内の全要素の layer ≥ d -/
theorem minLayer_le_layer {u : FallingUnit} {p : QuarterPos}
        (hp : p ∈ u.positions) (d : Nat) (hd : d ≤ u.minLayer) :
        d ≤ p.layer := by
    suffices h : u.minLayer ≤ p.layer by omega
    unfold FallingUnit.minLayer
    cases u with
    | cluster ps =>
        match ps, hp with
        | p' :: rest, hmem => exact foldl_min_le_mem p' rest p hmem
    | pin q =>
        simp only [FallingUnit.positions, List.mem_singleton] at hp
        subst hp
        simp only [FallingUnit.positions, List.foldl_nil, Std.le_refl]

/-- positions の .any 等価な FallingUnit は同じ placeFallingUnit 結果を持つ
    （dropDist が minLayer 以下であることが前提条件） -/
theorem placeFallingUnit_ext {u1 u2 : FallingUnit}
        (h : ∀ p, u1.positions.any (· == p) = u2.positions.any (· == p))
        (s : Shape) (obs : List Layer) (d : Nat)
        (hd : d ≤ u1.minLayer) :
        placeFallingUnit s obs u1 d = placeFallingUnit s obs u2 d := by
    simp only [placeFallingUnit]
    -- step 関数の定義
    let step : List Layer → QuarterPos → List Layer := fun obs p =>
        match p.getQuarter s with
        | some q => placeQuarter obs (p.layer - d) p.dir q
        | none => obs
    -- 述語 S: d ≤ p.layer を満たす要素
    let S : QuarterPos → Prop := fun p => d ≤ p.layer
    have h_ml : u1.minLayer = u2.minLayer := minLayer_ext h
    -- l1, l2 の全要素が S を満たす
    have hl1 : ∀ y, y ∈ u1.positions → S y :=
        fun y hy => minLayer_le_layer hy d hd
    have hl2 : ∀ y, y ∈ u2.positions → S y :=
        fun y hy => minLayer_le_layer hy d (h_ml ▸ hd)
    -- step の可換性（S を満たす異なる要素間）
    have h_step_comm : ∀ p1 p2, S p1 → S p2 → p1 ≠ p2 →
            ∀ acc, step (step acc p1) p2 = step (step acc p2) p1 := by
        intro p1 p2 hs1 hs2 hne acc
        simp only [step]
        cases hgq1 : p1.getQuarter s <;> cases hgq2 : p2.getQuarter s
        · rfl
        · simp only
        · simp only
        · rename_i q1 q2
          -- d ≤ p.layer → p.layer - d は忠実 → 異なるセルへの書き込み
          by_cases hl : p1.layer - d = p2.layer - d
          · have hleq : p1.layer = p2.layer := by omega
            have hdeq : p1.dir ≠ p2.dir := by
                intro hd_eq
                exact hne (by cases p1; cases p2; simp_all only [ne_eq, QuarterPos.mk.injEq, not_and])
            rw [hl]; exact placeQuarter_comm_dir_ne _ _ _ _ _ _ hdeq
          · exact placeQuarter_comm_layer_ne _ _ _ _ _ _ _ hl
    -- step の冪等性（S を満たす要素）
    have h_step_idem : ∀ p, S p → ∀ acc, step (step acc p) p = step acc p := by
        intro p _ acc
        simp only [step]
        cases p.getQuarter s with
        | none => rfl
        | some q => exact placeQuarter_idem _ _ _ _
    exact foldl_any_eq_of_comm_idem step S h_step_comm h_step_idem
        _ _ hl1 hl2 h _

/-- landingDistance.check は常に maxDrop 以下を返す -/
theorem landingDistance_check_le (obs : List Layer) (positions : List QuarterPos)
        (maxDrop d fuel : Nat) (hd : d ≤ maxDrop + 1) (hf : d + fuel = maxDrop + 2) :
        landingDistance.check obs positions maxDrop d fuel ≤ maxDrop := by
    induction fuel generalizing d with
    | zero => omega
    | succ n ih =>
        simp only [landingDistance.check]
        split
        · -- d > maxDrop → maxDrop ≤ maxDrop
          omega
        · -- ¬(d > maxDrop) → d ≤ maxDrop
          split
          · -- landed → d ≤ maxDrop
            omega
          · -- ¬landed → 再帰
            exact ih (d + 1) (by omega) (by omega)

/-- landingDistance は minLayer 以下 -/
theorem landingDistance_le_minLayer (u : FallingUnit) (obs : List Layer) :
        landingDistance u obs ≤ u.minLayer := by
    simp only [landingDistance]
    exact landingDistance_check_le obs u.positions u.minLayer 1 (u.minLayer + 1)
        (by omega) (by omega)

/-- landingDistance.check は d ≥ 1 かつ maxDrop ≥ 1 なら結果 ≥ 1 -/
private theorem landingDistance_check_ge_one (obs : List Layer) (positions : List QuarterPos)
        (maxDrop d fuel : Nat) (hd : d ≥ 1) (hm : maxDrop ≥ 1) :
        landingDistance.check obs positions maxDrop d fuel ≥ 1 := by
    induction fuel generalizing d with
    | zero => simp only [landingDistance.check]; omega
    | succ n ih =>
        simp only [landingDistance.check]
        split
        · omega
        · split
          · omega
          · exact ih (d + 1) (by omega)

/-- landingDistance は minLayer ≥ 1 なら結果 ≥ 1 -/
theorem landingDistance_ge_one (u : FallingUnit) (obs : List Layer)
        (h : u.minLayer ≥ 1) :
        landingDistance u obs ≥ 1 := by
    simp only [landingDistance]
    exact landingDistance_check_ge_one obs u.positions u.minLayer 1 (u.minLayer + 1)
        (by omega) h

/-- FallingUnit の positions 内に minLayer と等しい layer を持つ要素が存在する -/
theorem minLayer_witness (u : FallingUnit) (h : u.positions ≠ []) :
        ∃ p ∈ u.positions, p.layer = u.minLayer := by
    cases u with
    | cluster ps =>
        simp only [FallingUnit.positions] at h ⊢
        cases ps with
        | nil => simp only [ne_eq, not_true_eq_false] at h
        | cons p rest =>
            simp only [FallingUnit.minLayer, FallingUnit.positions]
            cases foldl_min_attained rest p.layer with
            | inl heq => exact ⟨p, .head _, heq.symm⟩
            | inr h =>
                obtain ⟨q, hq_mem, hq_eq⟩ := h
                exact ⟨q, .tail _ hq_mem, hq_eq.symm⟩
    | pin q =>
        simp only [FallingUnit.minLayer, FallingUnit.positions, List.foldl_nil]
        exact ⟨q, .head _, rfl⟩

/-- p.layer ≤ d なら floor contact で landed 条件が成立する -/
private theorem any_landed_of_le (positions : List QuarterPos) (d : Nat)
        (obs : List Layer) (h : ∃ p ∈ positions, p.layer ≤ d) :
        positions.any (fun p =>
            (p.layer - d == 0) || isOccupied obs (p.layer - d - 1) p.dir
        ) = true := by
    obtain ⟨p, hp_mem, hp_le⟩ := h
    exact List.any_eq_true.mpr ⟨p, hp_mem, by
        simp only [Bool.or_eq_true, beq_iff_eq]; left; omega⟩

/-- landingDistance.check が返す d では着地条件（floor contact か obstacle contact）が成立する -/
theorem landingDistance_check_landed (obs : List Layer) (positions : List QuarterPos)
        (maxDrop d fuel : Nat) (hd : d ≤ maxDrop + 1) (hf : d + fuel = maxDrop + 2)
        (h_min : ∃ p ∈ positions, p.layer ≤ maxDrop) :
        positions.any (fun p =>
            (p.layer - landingDistance.check obs positions maxDrop d fuel == 0) ||
            isOccupied obs
                (p.layer - landingDistance.check obs positions maxDrop d fuel - 1) p.dir
        ) = true := by
    induction fuel generalizing d with
    | zero =>
        simp only [landingDistance.check]
        exact any_landed_of_le positions d obs (by
            obtain ⟨p, hp, hle⟩ := h_min; exact ⟨p, hp, by omega⟩)
    | succ n ih =>
        simp only [landingDistance.check]
        split
        · -- d > maxDrop → 返り値は maxDrop
          exact any_landed_of_le positions maxDrop obs h_min
        · split
          · -- landed = true → 返り値は d。landed がそのまま証明
            rename_i h_not_gt h_landed; exact h_landed
          · -- landed = false → 再帰呼び出し
            exact ih (d + 1) (by omega) (by omega)

/-- landingDistance が返す距離では着地条件（floor contact か obstacle contact）が成立する -/
theorem landingDistance_landed (u : FallingUnit) (obs : List Layer)
        (h_ne : u.positions ≠ []) :
        u.positions.any (fun p =>
            (p.layer - landingDistance u obs == 0) ||
            isOccupied obs (p.layer - landingDistance u obs - 1) p.dir
        ) = true := by
    simp only [landingDistance]
    apply landingDistance_check_landed obs u.positions u.minLayer 1 (u.minLayer + 1)
        (by omega) (by omega)
    exact minLayer_witness u h_ne |>.elim fun p hp => ⟨p, hp.1, le_of_eq hp.2⟩

/-- check(d, fuel) = result かつ d' < result なら d' では landed = false
    （result より前の全 d' で着地条件が不成立だったことの証明） -/
theorem landingDistance_check_not_landed_before
    (obs : List Layer) (positions : List QuarterPos)
    (maxDrop d fuel : Nat) (hd : d ≤ maxDrop + 1) (hf : d + fuel = maxDrop + 2)
    (d' : Nat) (hd'_ge : d' ≥ d)
    (hd'_lt : d' < landingDistance.check obs positions maxDrop d fuel) :
    positions.any (fun p =>
        (p.layer - d' == 0) || isOccupied obs (p.layer - d' - 1) p.dir
    ) = false := by
  induction fuel generalizing d with
  | zero =>
    -- fuel = 0: result = d. d' < d かつ d' ≥ d は矛盾
    simp only [landingDistance.check] at hd'_lt
    omega
  | succ n ih =>
    simp only [landingDistance.check] at hd'_lt
    split at hd'_lt
    · -- d > maxDrop → result = maxDrop. d' < maxDrop かつ d' ≥ d → d' ≥ d > maxDrop → 矛盾
      omega
    · split at hd'_lt
      · -- landed = true → result = d. d' < d かつ d' ≥ d → 矛盾
        omega
      · -- landed = false → result = check (d+1) fuel
        -- d' = d の場合: landed = false から直接
        rename_i h_not_gt h_not_landed
        by_cases heq : d' = d
        · subst heq; rw [Bool.not_eq_true] at h_not_landed; exact h_not_landed
        · -- d' > d → d' ≥ d + 1 → IH
          exact ih (d + 1) (by omega) (by omega) (by omega) (by omega)

/-- 着地位置は obstacle で占有されていない（no-overwrite 基盤）
    landingDistance ≥ 2 の場合、全 position の (p.layer - d, p.dir) は obstacle で空 -/
theorem landingDistance_not_occupied_at_landing
    (u : FallingUnit) (obs : List Layer)
    (_h_ne : u.positions ≠ [])
    (h_min : u.minLayer ≥ 1)
    (hd_gt1 : landingDistance u obs ≥ 2) :
    ∀ p ∈ u.positions,
        isOccupied obs (p.layer - landingDistance u obs) p.dir = false := by
  intro p hp
  -- landingDistance の展開を明示
  have h_unfold : landingDistance u obs =
      landingDistance.check obs u.positions u.minLayer 1 (u.minLayer + 1) := rfl
  -- d ≥ 2 → d-1 ≥ 1 → d-1 check returned false
  have h_result := landingDistance_check_not_landed_before
      obs u.positions u.minLayer 1 (u.minLayer + 1)
      (by omega) (by omega)
      (landingDistance u obs - 1) (by omega) (by rw [h_unfold]; omega)
  -- not_landed at (d-1): for all q, check at d-1 is false
  have h_false := (List.any_eq_false.mp h_result) p hp
  rw [Bool.not_eq_true] at h_false
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h_false
  -- h_false.1 : p.layer - (d-1) ≠ 0 → p.layer ≥ d
  -- h_false.2 : isOccupied obs (p.layer - (d-1) - 1) p.dir = false
  -- p.layer - (d-1) - 1 = p.layer - d (since p.layer ≥ d from h_false.1)
  have : p.layer - (landingDistance u obs - 1) - 1 = p.layer - landingDistance u obs := by omega
  rw [this] at h_false
  exact h_false.2

/-- placeFallingUnit は着地位置以外の getDir を保存する。
    位置 (l, dir) が FU の着地位置のいずれでもない場合、
    getDir ((placeFallingUnit s obs u d).getD l .empty) dir = getDir (obs.getD l .empty) dir -/
theorem foldl_placeQuarter_getDir_preserved
    (s : Shape) (obs : List Layer) (positions : List QuarterPos) (dropDist : Nat)
    (l : Nat) (dir : Direction)
    (h_not : ∀ p ∈ positions, ¬(p.layer - dropDist = l ∧ p.dir = dir)) :
    QuarterPos.getDir ((positions.foldl (fun obs p =>
        match p.getQuarter s with
        | some q => placeQuarter obs (p.layer - dropDist) p.dir q
        | none => obs) obs).getD l Layer.empty) dir =
    QuarterPos.getDir (obs.getD l Layer.empty) dir := by
  induction positions generalizing obs with
  | nil => rfl
  | cons hd tl ih =>
    have h_hd : ¬(hd.layer - dropDist = l ∧ hd.dir = dir) :=
      h_not hd (.head _)
    have h_tl : ∀ p ∈ tl, ¬(p.layer - dropDist = l ∧ p.dir = dir) :=
      fun p hp => h_not p (.tail _ hp)
    simp only [List.foldl]
    cases hq : hd.getQuarter s with
    | none => exact ih obs h_tl
    | some q =>
      suffices h_step : QuarterPos.getDir ((placeQuarter obs (hd.layer - dropDist) hd.dir q).getD l Layer.empty) dir =
          QuarterPos.getDir (obs.getD l Layer.empty) dir by
        rw [show (match some q with | some q => placeQuarter obs (hd.layer - dropDist) hd.dir q | none => obs) =
            placeQuarter obs (hd.layer - dropDist) hd.dir q from rfl]
        exact (ih _ h_tl).trans h_step
      push Not at h_hd
      by_cases h_lay : hd.layer - dropDist = l
      · -- 同層・異方角
        rw [placeQuarter_getD _ _ _ _ _ (show l < max obs.length (hd.layer - dropDist + 1) by omega),
            show l = hd.layer - dropDist from h_lay.symm, if_pos rfl,
            QuarterPos.getDir_setDir_ne _ _ _ _ (h_hd h_lay), h_lay]
      · -- 異層
        rw [placeQuarter_getD_ne _ _ _ _ _ (Ne.symm h_lay)]

/-- 一意な着地位置に対して placeFallingUnit が正しいクォーターを配置する。
    positions 内の位置 q に対し、q.getQuarter s = some qv ならば、
    foldl 後の (q.layer - dropDist, q.dir) の getDir は qv に等しい。
    前提: positions が Nodup かつ着地位置が一意（異なる位置が同じ着地位置を持たない） -/
theorem foldl_placeQuarter_getDir_at_target
    (s : Shape) (obs : List Layer) (positions : List QuarterPos) (dropDist : Nat)
    (q : QuarterPos) (h_mem : q ∈ positions)
    (h_nodup : positions.Nodup)
    (h_unique : ∀ p ∈ positions, p ≠ q → ¬(p.layer - dropDist = q.layer - dropDist ∧ p.dir = q.dir))
    (qv : Quarter) (hq : QuarterPos.getQuarter s q = some qv) :
    QuarterPos.getDir ((positions.foldl (fun obs p =>
        match QuarterPos.getQuarter s p with
        | some r => placeQuarter obs (p.layer - dropDist) p.dir r
        | none => obs) obs).getD (q.layer - dropDist) Layer.empty) q.dir = qv := by
  induction positions generalizing obs with
  | nil => simp only [List.not_mem_nil] at h_mem
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have h_nd_tl := (List.nodup_cons.mp h_nodup).2
    by_cases h_eq : hd = q
    · -- hd = q: placeQuarter で配置後、残り tl は位置を保存
      have h_not_mem_tl : hd ∉ tl := (List.nodup_cons.mp h_nodup).1
      rw [h_eq] at h_not_mem_tl
      rw [h_eq]; simp only [hq]
      have h_tl_not : ∀ p ∈ tl, ¬(p.layer - dropDist = q.layer - dropDist ∧ p.dir = q.dir) := by
        intro p hp h_and
        have h_ne : p ≠ q := fun heq => h_not_mem_tl (heq ▸ hp)
        exact h_unique p (List.mem_cons.mpr (Or.inr hp)) h_ne h_and
      have h_preserved := foldl_placeQuarter_getDir_preserved s
        (placeQuarter obs (q.layer - dropDist) q.dir qv) tl dropDist
        (q.layer - dropDist) q.dir h_tl_not
      have h_base : QuarterPos.getDir ((placeQuarter obs (q.layer - dropDist) q.dir qv).getD
          (q.layer - dropDist) Layer.empty) q.dir = qv := by
        rw [placeQuarter_getD _ _ _ _ _ (by omega), if_pos rfl, QuarterPos.getDir_setDir_same]
      exact h_preserved.trans h_base
    · -- hd ≠ q: q ∈ tl、IH 適用
      have h_tl_mem : q ∈ tl := by
        cases h_mem with
        | head => exact absurd rfl h_eq
        | tail _ h => exact h
      exact ih _ h_tl_mem h_nd_tl
        (fun p hp hne => h_unique p (List.mem_cons.mpr (Or.inr hp)) hne)

/-- foldl 配置で書き込まれた位置には canFormBond の象限が存在する。
    全位置が canFormBond を持つ場合、foldl 後の任意の書き込み先で
    canFormBond を持つ象限値が保証される。Nodup 不要。 -/
theorem foldl_placeQuarter_written_canFormBond
    (s : Shape) (obs : List Layer) (positions : List QuarterPos) (dropDist : Nat)
    (lay : Nat) (dir : Direction)
    (h_written : ∃ p ∈ positions, p.layer - dropDist = lay ∧ p.dir = dir)
    (h_bond : ∀ p ∈ positions, ∃ qv, p.getQuarter s = some qv ∧ qv.canFormBond = true)
    : ∃ qv, QuarterPos.getDir ((positions.foldl (fun obs p =>
        match p.getQuarter s with
        | some r => placeQuarter obs (p.layer - dropDist) p.dir r
        | none => obs) obs).getD lay Layer.empty) dir = qv ∧ qv.canFormBond = true := by
  induction positions generalizing obs with
  | nil => obtain ⟨p, hp, _, _⟩ := h_written; simp only [List.not_mem_nil] at hp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    set obs' := (match hd.getQuarter s with
        | some r => placeQuarter obs (hd.layer - dropDist) hd.dir r
        | none => obs) with h_obs'_def
    by_cases h_tl_has : ∃ p ∈ tl, p.layer - dropDist = lay ∧ p.dir = dir
    · exact ih obs' h_tl_has (fun p hp => h_bond p (List.mem_cons.mpr (Or.inr hp)))
    · obtain ⟨p, h_p_mem, h_p_lay, h_p_dir⟩ := h_written
      cases h_p_mem with
      | head =>
        obtain ⟨qv, hqv, hqv_bond⟩ := h_bond hd (List.mem_cons.mpr (Or.inl rfl))
        have h_obs'_eq : obs' = placeQuarter obs (hd.layer - dropDist) hd.dir qv := by
          simp only [h_obs'_def, hqv]
        have h_tl_not : ∀ p ∈ tl, ¬(p.layer - dropDist = lay ∧ p.dir = dir) := by
          intro p hp hc; exact h_tl_has ⟨p, hp, hc.1, hc.2⟩
        have h_pres := foldl_placeQuarter_getDir_preserved s obs' tl dropDist lay dir h_tl_not
        have h_base : QuarterPos.getDir (obs'.getD lay Layer.empty) dir = qv := by
          subst h_p_lay; subst h_p_dir
          rw [h_obs'_eq, placeQuarter_getD _ _ _ _ _ (by omega), if_pos rfl,
              QuarterPos.getDir_setDir_same]
        exact ⟨qv, h_pres.trans h_base, hqv_bond⟩
      | tail _ h => exact absurd ⟨p, h, h_p_lay, h_p_dir⟩ h_tl_has

/-- positions .any BEq 等価リストペアの同一インデックスにある要素対は同じ foldl 結果を生む -/
theorem foldl_pointwise_ext (s : Shape)
        (l1 l2 : List FallingUnit) (obs : List Layer)
        (h_len : l1.length = l2.length)
        (h_any : ∀ (i : Nat) (hi : i < l1.length) (p : QuarterPos),
            (l1[i]'hi).positions.any (· == p) =
            (l2[i]'(h_len ▸ hi)).positions.any (· == p)) :
        l1.foldl (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs =
        l2.foldl (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs := by
    induction l1 generalizing l2 obs with
    | nil =>
        cases l2 with
        | nil => rfl
        | cons _ _ => simp only [List.length_nil, List.length_cons, Nat.right_eq_add, Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero, and_false] at h_len
    | cons u1 rest1 ih =>
        cases l2 with
        | nil => simp only [List.length_cons, List.length_nil, Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero, and_false] at h_len
        | cons u2 rest2 =>
            simp only [List.foldl_cons]
            -- u1 と u2 は .any 等価 (i=0 のケース)
            have h_any_head : ∀ p, u1.positions.any (· == p) = u2.positions.any (· == p) :=
                fun p => h_any 0 (by simp only [List.length_cons, Nat.zero_lt_succ]) p
            -- landingDistance が一致
            have h_ld : landingDistance u1 obs = landingDistance u2 obs :=
                landingDistance_ext h_any_head obs
            -- placeFallingUnit が一致
            have h_d_le : landingDistance u1 obs ≤ u1.minLayer :=
                landingDistance_le_minLayer u1 obs
            have h_pfu : placeFallingUnit s obs u1 (landingDistance u1 obs) =
                         placeFallingUnit s obs u2 (landingDistance u2 obs) := by
                rw [h_ld]
                exact placeFallingUnit_ext h_any_head s obs (landingDistance u2 obs)
                    (h_ld ▸ h_d_le)
            rw [h_pfu]
            -- 残りのリストに対して帰納法仮定を適用
            exact ih rest2 _ (by simpa using h_len)
                (fun i hi p => h_any (i + 1) (by simp only [List.length_cons, Nat.add_lt_add_iff_right]; omega) p)

/-- getDir は setDir の異なる方角で不変 -/
theorem getDir_setDir_ne (l : Layer) (d d' : Direction) (q : Quarter)
        (hne : d ≠ d') :
        QuarterPos.getDir (QuarterPos.setDir l d q) d' = QuarterPos.getDir l d' := by
    cases d <;> cases d' <;> simp_all only [ne_eq, not_true_eq_false, reduceCtorEq, not_false_eq_true, QuarterPos.getDir, QuarterPos.setDir]

/-- isOccupied は placeQuarter の異なる方角で不変 -/
theorem isOccupied_placeQuarter_ne_dir (obs : List Layer) (lay lay' : Nat)
        (d d' : Direction) (q : Quarter) (hne : d ≠ d') :
        isOccupied (placeQuarter obs lay d q) lay' d' = isOccupied obs lay' d' := by
    show (match (placeQuarter obs lay d q)[lay']? with
          | some l => !(QuarterPos.getDir l d').isEmpty
          | none   => false) =
         (match obs[lay']? with
          | some l => !(QuarterPos.getDir l d').isEmpty
          | none   => false)
    rw [placeQuarter_getElem?_full]
    by_cases h1 : lay' < max obs.length (lay + 1)
    · simp only [if_pos h1]
      by_cases h2 : lay' = lay
      · subst h2; simp only [ite_true]
        -- ゴール: !(QuarterPos.getDir (QuarterPos.setDir (obs.getD lay' Layer.empty) d q) d').isEmpty
        --       = match obs[lay']? with | some l => !(QuarterPos.getDir l d').isEmpty | none => false
        rw [getDir_setDir_ne _ _ _ _ hne, List.getD_eq_getElem?_getD]
        cases obs[lay']? with
        | some => rfl
        | none => cases d' <;> rfl
      · simp only [if_neg h2]
        rw [List.getD_eq_getElem?_getD]
        cases obs[lay']? with
        | some => rfl
        | none => cases d' <;> rfl
    · simp only [if_neg h1]
      have hge : obs.length ≤ lay' := by omega
      rw [List.getElem?_eq_none_iff.mpr hge]

/-- isOccupied は placeFallingUnit の、positions と方角が素な場合に不変 -/
theorem isOccupied_placeFallingUnit_ne_dir (s : Shape) (obs : List Layer)
        (u : FallingUnit) (d : Nat) (lay : Nat) (dir : Direction)
        (h_no_dir : u.positions.any (fun p => p.dir == dir) = false) :
        isOccupied (placeFallingUnit s obs u d) lay dir = isOccupied obs lay dir := by
    unfold placeFallingUnit
    suffices h : ∀ (ps : List QuarterPos) (acc : List Layer),
        ps.any (fun p => p.dir == dir) = false →
        isOccupied (ps.foldl (fun obs p =>
            match p.getQuarter s with
            | some q => placeQuarter obs (p.layer - d) p.dir q
            | none => obs) acc) lay dir = isOccupied acc lay dir by
      exact h u.positions obs h_no_dir
    intro ps
    induction ps with
    | nil => intro _ _; rfl
    | cons p rest ih =>
      intro acc hany
      simp only [List.any_cons] at hany
      have hne : p.dir ≠ dir := by
        intro heq; simp only [heq, BEq.rfl, Bool.true_or, Bool.true_eq_false] at hany
      have hrest : rest.any (fun p => p.dir == dir) = false := by
        cases hp : (p.dir == dir) with
        | false => simpa [hp] using hany
        | true => exact absurd (beq_iff_eq.mp hp) hne
      simp only [List.foldl_cons]
      rw [ih _ hrest]
      split
      · next q _ =>
        exact isOccupied_placeQuarter_ne_dir acc _ lay p.dir dir q hne
      · rfl

/-- 着地判定は placeFallingUnit の方角素なユニットで不変 -/
theorem landed_placeFallingUnit_ne_dir (s : Shape) (obs : List Layer)
        (u : FallingUnit) (drop : Nat) (positions : List QuarterPos) (d : Nat)
        (h_no_dir : ∀ p, p ∈ positions → u.positions.any (fun q => q.dir == p.dir) = false) :
        positions.any (fun p =>
            let newLayer := p.layer - d
            newLayer == 0 || isOccupied (placeFallingUnit s obs u drop) (newLayer - 1) p.dir) =
        positions.any (fun p =>
            let newLayer := p.layer - d
            newLayer == 0 || isOccupied obs (newLayer - 1) p.dir) := by
    induction positions with
    | nil => rfl
    | cons p rest ih =>
        simp only [List.any_cons]
        rw [ih (fun q hq => h_no_dir q (.tail p hq))]
        congr 1
        have h_p := h_no_dir p (.head rest)
        congr 1
        exact isOccupied_placeFallingUnit_ne_dir s obs u drop _ _ h_p

/-- landingDistance.check は方角素な placeFallingUnit で不変 -/
theorem landingDistance_check_placeFallingUnit_ne_dir (s : Shape) (obs : List Layer)
        (u : FallingUnit) (drop : Nat) (positions : List QuarterPos)
        (maxDrop d fuel : Nat)
        (h_no_dir : ∀ p, p ∈ positions → u.positions.any (fun q => q.dir == p.dir) = false) :
        landingDistance.check (placeFallingUnit s obs u drop) positions maxDrop d fuel =
        landingDistance.check obs positions maxDrop d fuel := by
    induction fuel generalizing d with
    | zero => rfl
    | succ n ih =>
        simp only [landingDistance.check]
        split
        · rfl
        · rw [landed_placeFallingUnit_ne_dir s obs u drop positions d h_no_dir]
          split
          · rfl
          · exact ih (d + 1)

/-- landingDistance は方角素な placeFallingUnit で不変 -/
theorem landingDistance_placeFallingUnit_ne_dir (s : Shape) (obs : List Layer)
        (u v : FallingUnit) (d : Nat)
        (h_no_dir : ∀ p, p ∈ v.positions →
            u.positions.any (fun q => q.dir == p.dir) = false) :
        landingDistance v (placeFallingUnit s obs u d) = landingDistance v obs := by
    simp only [landingDistance]
    exact landingDistance_check_placeFallingUnit_ne_dir s obs u d v.positions
        v.minLayer 1 (v.minLayer + 1) h_no_dir

/-- placeQuarter は方角が異なれば（任意のレイヤで）可換 -/
theorem placeQuarter_comm_of_dir_ne (obs : List Layer)
        (lay1 lay2 : Nat) (d1 d2 : Direction) (q1 q2 : Quarter)
        (hne : d1 ≠ d2) :
        placeQuarter (placeQuarter obs lay1 d1 q1) lay2 d2 q2 =
        placeQuarter (placeQuarter obs lay2 d2 q2) lay1 d1 q1 := by
    by_cases hl : lay1 = lay2
    · subst hl; exact placeQuarter_comm_dir_ne obs lay1 d1 d2 q1 q2 hne
    · exact placeQuarter_comm_layer_ne obs lay1 lay2 d1 d2 q1 q2 hl

/-- 単一 placeQuarter は方角素な foldl-step 列を通過する -/
theorem foldl_placeQuarter_comm_ne_dir (s : Shape)
        (ups : List QuarterPos) (drop : Nat) (acc : List Layer)
        (lay : Nat) (d : Direction) (q : Quarter)
        (h_ne : ∀ r, r ∈ ups → r.dir ≠ d) :
        ups.foldl (fun obs r =>
            match r.getQuarter s with
            | some q' => placeQuarter obs (r.layer - drop) r.dir q'
            | none => obs
        ) (placeQuarter acc lay d q) =
        placeQuarter (ups.foldl (fun obs r =>
            match r.getQuarter s with
            | some q' => placeQuarter obs (r.layer - drop) r.dir q'
            | none => obs
        ) acc) lay d q := by
    induction ups generalizing acc with
    | nil => rfl
    | cons r rest ih =>
        simp only [List.foldl_cons]
        have hr_ne : r.dir ≠ d := h_ne r (.head rest)
        have hrest : ∀ r', r' ∈ rest → r'.dir ≠ d :=
            fun r' hr' => h_ne r' (.tail r hr')
        -- r.getQuarter s で場合分け
        match hgq : QuarterPos.getQuarter s r with
        | some q' =>
            -- placeQuarter の可換性で通過
            simp only [placeQuarter_comm_of_dir_ne acc lay (r.layer - drop)
                d r.dir q q' (Ne.symm hr_ne)]
            exact ih (placeQuarter acc (r.layer - drop) r.dir q') hrest
        | none =>
            exact ih acc hrest

/-- 方角素なリストの foldl-step は可換 -/
theorem foldl_comm_ne_dir (s : Shape)
        (ups vps : List QuarterPos) (du dv : Nat) (obs : List Layer)
        (h_vu : ∀ p, p ∈ vps →
            ups.any (fun q => q.dir == p.dir) = false) :
        vps.foldl (fun obs p =>
            match p.getQuarter s with
            | some q => placeQuarter obs (p.layer - dv) p.dir q
            | none => obs)
          (ups.foldl (fun obs p =>
            match p.getQuarter s with
            | some q => placeQuarter obs (p.layer - du) p.dir q
            | none => obs) obs) =
        ups.foldl (fun obs p =>
            match p.getQuarter s with
            | some q => placeQuarter obs (p.layer - du) p.dir q
            | none => obs)
          (vps.foldl (fun obs p =>
            match p.getQuarter s with
            | some q => placeQuarter obs (p.layer - dv) p.dir q
            | none => obs) obs) := by
    induction vps generalizing obs with
    | nil => rfl
    | cons p rest ih =>
        dsimp only [List.foldl_cons]
        -- p の方角は ups の全要素と異なる
        have hp : ups.any (fun q => q.dir == p.dir) = false :=
            h_vu p (.head rest)
        have hrest : ∀ q, q ∈ rest →
            ups.any (fun r => r.dir == q.dir) = false :=
            fun q hq => h_vu q (.tail p hq)
        -- ups 内の全要素 r について r.dir ≠ p.dir を導出
        have h_ne : ∀ r, r ∈ ups → r.dir ≠ p.dir := by
            intro r hr heq
            have : ups.any (fun q => q.dir == p.dir) = true :=
                List.any_eq_true.mpr ⟨r, hr, by simp only [heq, BEq.rfl]⟩
            simp_all only [List.mem_cons, or_true, implies_true, forall_const, List.any_eq_false, beq_iff_eq, forall_eq_or_imp, Bool.true_eq_false]
        -- p.getQuarter s で場合分け
        match hgq : QuarterPos.getQuarter s p with
        | some q' =>
            -- placeQuarter を ups.foldl の内側に通す
            -- NOTE: simp only [hgq] は linter 上は unused だが rw のために必要
            set_option linter.unusedSimpArgs false in
            simp only [hgq]
            rw [← foldl_placeQuarter_comm_ne_dir s ups du obs
                (p.layer - dv) p.dir q' h_ne]
            exact ih (placeQuarter obs (p.layer - dv) p.dir q') hrest
        | none =>
            -- none ケースは恒等変換なので IH をそのまま適用
            set_option linter.unusedSimpArgs false in
            simp only [hgq]
            exact ih obs hrest

/-- placeFallingUnit は方角素なユニットペアで可換 -/
theorem placeFallingUnit_comm_ne_dir (s : Shape) (obs : List Layer)
        (u v : FallingUnit) (du dv : Nat)
        (_h_uv : ∀ p, p ∈ u.positions →
            v.positions.any (fun q => q.dir == p.dir) = false)
        (h_vu : ∀ p, p ∈ v.positions →
            u.positions.any (fun q => q.dir == p.dir) = false) :
        placeFallingUnit s (placeFallingUnit s obs u du) v dv =
        placeFallingUnit s (placeFallingUnit s obs v dv) u du := by
    simp only [placeFallingUnit]
    exact foldl_comm_ne_dir s u.positions v.positions du dv obs h_vu

/-- 方角素なユニットの settle step は可換 -/
theorem settleStep_comm_ne_dir (s : Shape) (obs : List Layer)
        (u v : FallingUnit)
        (h_uv : ∀ p, p ∈ u.positions →
            v.positions.any (fun q => q.dir == p.dir) = false)
        (h_vu : ∀ p, p ∈ v.positions →
            u.positions.any (fun q => q.dir == p.dir) = false) :
        placeFallingUnit s
            (placeFallingUnit s obs u (landingDistance u obs))
            v (landingDistance v (placeFallingUnit s obs u (landingDistance u obs))) =
        placeFallingUnit s
            (placeFallingUnit s obs v (landingDistance v obs))
            u (landingDistance u (placeFallingUnit s obs v (landingDistance v obs))) := by
    -- landingDistance は方角素な placeFallingUnit で不変
    rw [landingDistance_placeFallingUnit_ne_dir s obs u v (landingDistance u obs) h_vu]
    rw [landingDistance_placeFallingUnit_ne_dir s obs v u (landingDistance v obs) h_uv]
    -- placeFallingUnit は方角素なペアで可換
    exact placeFallingUnit_comm_ne_dir s obs u v
        (landingDistance u obs) (landingDistance v obs) h_uv h_vu

-- ============================================================
-- 方角共有・レイヤ差 ≥ 2 の場合の可換性
-- ============================================================

/-- isOccupied は placeQuarter の異なるレイヤで不変 -/
theorem isOccupied_placeQuarter_ne_layer (obs : List Layer) (lay lay' : Nat)
        (d : Direction) (q : Quarter) (hne : lay ≠ lay') (d' : Direction) :
        isOccupied (placeQuarter obs lay d q) lay' d' = isOccupied obs lay' d' := by
    show (match (placeQuarter obs lay d q)[lay']? with
          | some l => !(QuarterPos.getDir l d').isEmpty
          | none   => false) =
         (match obs[lay']? with
          | some l => !(QuarterPos.getDir l d').isEmpty
          | none   => false)
    rw [placeQuarter_getElem?_full]
    by_cases h1 : lay' < max obs.length (lay + 1)
    · simp only [if_pos h1, if_neg (Ne.symm hne), List.getD_eq_getElem?_getD]
      cases obs[lay']? with
      | some => rfl
      | none => cases d' <;> rfl
    · simp only [if_neg h1]
      rw [List.getElem?_eq_none_iff.mpr (by omega)]

/-- isOccupied は placeFallingUnit で不変（各位置の配置レイヤが query レイヤと異なるか方角が異なる場合） -/
theorem isOccupied_placeFU_of_ne (s : Shape) (obs : List Layer) (u : FallingUnit)
        (drop : Nat) (lay : Nat) (dir : Direction)
        (h : ∀ p ∈ u.positions, p.dir = dir → p.layer - drop ≠ lay) :
        isOccupied (placeFallingUnit s obs u drop) lay dir = isOccupied obs lay dir := by
    unfold placeFallingUnit
    suffices hsuff : ∀ (ps : List QuarterPos) (acc : List Layer),
        (∀ p ∈ ps, p.dir = dir → p.layer - drop ≠ lay) →
        isOccupied (ps.foldl (fun obs p =>
            match p.getQuarter s with
            | some q => placeQuarter obs (p.layer - drop) p.dir q
            | none => obs) acc) lay dir = isOccupied acc lay dir by
      exact hsuff u.positions obs h
    intro ps
    induction ps with
    | nil => intro _ _; rfl
    | cons p rest ih =>
        intro acc hne
        simp only [List.foldl_cons]
        rw [ih _ (fun q hq => hne q (.tail p hq))]
        split
        · next q _ =>
            by_cases hd : p.dir = dir
            · exact hd ▸
                isOccupied_placeQuarter_ne_layer acc _ lay p.dir q (hne p (.head rest) hd) _
            · exact isOccupied_placeQuarter_ne_dir acc _ lay p.dir dir q hd
        · rfl

/-- landed 判定は placeFallingUnit で不変（各位置の配置レイヤが着地チェックレイヤと重ならない場合）。
    floor contact (newLayer = 0) の場合は isOccupied に関わらず結果が同じ -/
private theorem landed_placeFU_of_ne (s : Shape) (obs : List Layer) (u : FallingUnit)
        (drop : Nat) (positions : List QuarterPos) (d : Nat)
        (h : ∀ q ∈ positions, q.layer > d →
            ∀ p ∈ u.positions, q.dir = p.dir → p.layer - drop ≠ q.layer - d - 1) :
        positions.any (fun q =>
            let newLayer := q.layer - d
            newLayer == 0 || isOccupied (placeFallingUnit s obs u drop) (newLayer - 1) q.dir) =
        positions.any (fun q =>
            let newLayer := q.layer - d
            newLayer == 0 || isOccupied obs (newLayer - 1) q.dir) := by
    induction positions with
    | nil => rfl
    | cons q rest ih =>
        simp only [List.any_cons]
        rw [ih (fun r hr hgt => h r (.tail q hr) hgt)]
        congr 1
        by_cases hnl : q.layer ≤ d
        · -- floor contact: newLayer = q.layer - d = 0 → true || _ = true
          show (q.layer - d == 0 || _) = (q.layer - d == 0 || _)
          rw [show q.layer - d = 0 from Nat.sub_eq_zero_of_le hnl]
          simp only [BEq.rfl, Nat.zero_le, Nat.sub_eq_zero_of_le, Bool.true_or]
        · -- newLayer > 0: isOccupied の不変性を使用
          show (q.layer - d == 0 || isOccupied (placeFallingUnit s obs u drop) (q.layer - d - 1) q.dir) =
               (q.layer - d == 0 || isOccupied obs (q.layer - d - 1) q.dir)
          congr 1
          exact isOccupied_placeFU_of_ne s obs u drop (q.layer - d - 1) q.dir
            (fun p hp hdir => h q (.head rest) (by omega) p hp hdir.symm)

/-- landingDistance は placeFallingUnit で不変
    （方角共有位置のレイヤ差 ≥ 2 + minLayer ≤ 2 の場合）。
    minLayer ≤ 2 + gap ≥ 2 の制約により、d=1 のチェックは placeFU で不変、
    d=minLayer では floor contact が支配する -/
theorem landingDistance_placeFU_gap (s : Shape) (obs : List Layer) (u v : FallingUnit)
        (drop : Nat)
        (h_gap : ∀ p ∈ u.positions, ∀ q ∈ v.positions,
            p.dir = q.dir → p.layer ≠ q.layer ∧
              ¬(LayerIndex.verticallyAdjacent p.layer q.layer = true))
        (h_ml : v.minLayer ≤ 2)
        (h_drop : drop ≤ u.minLayer) (h_ml_u : u.minLayer ≤ 2)
        (h_drop_pos : v.minLayer ≥ 2 → drop ≥ 1) :
        landingDistance v (placeFallingUnit s obs u drop) = landingDistance v obs := by
    -- minLayer ≤ 2 で場合分け（0, 1, 2）
    have h_cases : v.minLayer = 0 ∨ v.minLayer = 1 ∨ v.minLayer = 2 := by omega
    simp only [landingDistance]
    rcases h_cases with hml | hml | hml <;> rw [hml]
    · -- minLayer = 0: check 1 1 → d=1 > 0 → return 0
      simp only [landingDistance.check, show 1 > 0 from by omega, ↓reduceIte]
    · -- minLayer = 1: check 1 2 → if landed(1) then 1 else 1 = 1
      simp only [landingDistance.check, show ¬(1 > 1) from by omega, ↓reduceIte,
        show 2 > 1 from by omega, ite_self]
    · -- minLayer = 2: d=1 check は placeFU で不変、d=2 は floor contact
      -- check 1 3 を 2 回展開
      show landingDistance.check (placeFallingUnit s obs u drop) v.positions 2 1 3 =
           landingDistance.check obs v.positions 2 1 3
      simp only [landingDistance.check, show ¬(1 > 2) from by omega, ↓reduceIte,
        show ¬(2 > 2) from by omega, show 3 > 2 from by omega]
      -- d=1 の landed check は placeFU で不変
      rw [landed_placeFU_of_ne s obs u drop v.positions 1]
      · -- 結果が同じなら分岐も同じ
        split
        · rfl
        · -- d=2: if landed(2) then 2 else 2 = if landed(2) then 2 else 2
          -- 1+1 = 2 で正規化してから ite_self
          simp only [show (1:Nat) + 1 = 2 from rfl, ite_self]
      · -- d=1 のチェックレイヤが u の配置レイヤと重ならない
        intro q hq hqd p hp hdir
        have ⟨hne_layer, h_not_adj⟩ := h_gap p hp q hq hdir.symm
        simp only [LayerIndex.verticallyAdjacent, Bool.or_eq_true, beq_iff_eq] at h_not_adj
        push Not at h_not_adj
        have hp_ge : drop ≤ p.layer :=
            le_trans h_drop (minLayer_le_layer hp u.minLayer (le_refl u.minLayer))
        have h_drp := h_drop_pos (by omega)
        omega

/-- placeFallingUnit は配置レイヤが方角ごとに素なら可換 -/
theorem placeFallingUnit_comm_of_layer_disjoint (s : Shape) (obs : List Layer)
        (u v : FallingUnit) (du dv : Nat)
        (h : ∀ p ∈ u.positions, ∀ q ∈ v.positions,
            p.dir = q.dir → p.layer - du ≠ q.layer - dv) :
        placeFallingUnit s (placeFallingUnit s obs u du) v dv =
        placeFallingUnit s (placeFallingUnit s obs v dv) u du := by
    simp only [placeFallingUnit]
    -- u.positions と v.positions の foldl が全ペアで可換であることを示す
    -- 各ペア (p, q) に対して placeQuarter が可換:
    --   p.dir ≠ q.dir → placeQuarter_comm_of_dir_ne
    --   p.dir = q.dir → p.layer - du ≠ q.layer - dv → placeQuarter_comm_layer_ne
    have h_comm_single : ∀ (p : QuarterPos) (hp : p ∈ u.positions)
            (q : QuarterPos) (hq : q ∈ v.positions)
            (qp : Quarter) (qq : Quarter) (acc : List Layer),
        placeQuarter (placeQuarter acc (p.layer - du) p.dir qp) (q.layer - dv) q.dir qq =
        placeQuarter (placeQuarter acc (q.layer - dv) q.dir qq) (p.layer - du) p.dir qp := by
      intro p hp q hq qp qq acc
      by_cases hd : p.dir = q.dir
      · exact placeQuarter_comm_layer_ne acc _ _ p.dir q.dir qp qq (h p hp q hq hd)
      · exact placeQuarter_comm_of_dir_ne acc _ _ p.dir q.dir qp qq hd
    -- foldl_comm_ne_dir の一般化版（方角素に限らない可換性）
    -- 帰納法で証明
    suffices hsuff : ∀ (vps : List QuarterPos) (hvps : ∀ q ∈ vps, q ∈ v.positions)
            (acc : List Layer),
        vps.foldl (fun obs q => match q.getQuarter s with
            | some qq => placeQuarter obs (q.layer - dv) q.dir qq | none => obs)
          (u.positions.foldl (fun obs p => match p.getQuarter s with
            | some qp => placeQuarter obs (p.layer - du) p.dir qp | none => obs) acc) =
        u.positions.foldl (fun obs p => match p.getQuarter s with
            | some qp => placeQuarter obs (p.layer - du) p.dir qp | none => obs)
          (vps.foldl (fun obs q => match q.getQuarter s with
            | some qq => placeQuarter obs (q.layer - dv) q.dir qq | none => obs) acc) by
      exact hsuff v.positions (fun q hq => hq) obs
    intro vps hvps
    induction vps with
    | nil => intro _; rfl
    | cons q rest ih =>
        intro acc
        simp only [List.foldl_cons]
        -- q.getQuarter s で場合分け
        split
        · next qq _ =>
          -- some case: placeQuarter を u.positions.foldl の内外で交換
          have hq := hvps q (.head rest)
          suffices hswap : ∀ (ups : List QuarterPos) (hups : ∀ p ∈ ups, p ∈ u.positions)
                  (base : List Layer),
              ups.foldl (fun obs p => match p.getQuarter s with
                  | some qp => placeQuarter obs (p.layer - du) p.dir qp | none => obs)
                (placeQuarter base (q.layer - dv) q.dir qq) =
              placeQuarter
                (ups.foldl (fun obs p => match p.getQuarter s with
                    | some qp => placeQuarter obs (p.layer - du) p.dir qp | none => obs) base)
                (q.layer - dv) q.dir qq by
            rw [← hswap u.positions (fun p hp => hp) acc]
            exact ih (fun r hr => hvps r (.tail q hr)) _
          intro ups hups
          induction ups with
          | nil => intro _; rfl
          | cons p prest pih =>
              intro base
              simp only [List.foldl_cons]
              split
              · next qp _ =>
                  rw [(h_comm_single p (hups p (.head prest)) q hq qp qq base).symm]
                  exact pih (fun r hr => hups r (.tail p hr)) _
              · exact pih (fun r hr => hups r (.tail p hr)) _
        · -- none case: F(base, q) = base → ih を直接適用
          exact ih (fun r hr => hvps r (.tail q hr)) acc

/-- ギャップ条件から配置レイヤ差を導出する境界補題。
        minLayer=0 ケースと minLayer≥1 ケースを分離して扱う。 -/
private theorem placedLayer_ne_of_gap
                (obs : List Layer) (u v : FallingUnit) (p q : QuarterPos)
    (h_ml_u : u.minLayer ≤ 2)
                (h_same_ml : u.minLayer = v.minLayer)
                (hne_layer : p.layer ≠ q.layer)
                (h_not_adj : p.layer + 1 ≠ q.layer ∧ q.layer + 1 ≠ p.layer)
                (h_drop_u : landingDistance u obs ≤ u.minLayer)
                (h_drop_v : landingDistance v obs ≤ v.minLayer)
                (hp_ge : landingDistance u obs ≤ p.layer)
                (hq_ge : landingDistance v obs ≤ q.layer) :
                p.layer - landingDistance u obs ≠ q.layer - landingDistance v obs := by
        by_cases hml0 : u.minLayer = 0
        case pos =>
                have hdu0 : landingDistance u obs = 0 := by omega
                have hdv0 : landingDistance v obs = 0 := by omega
                rw [hdu0, hdv0]
                omega
        case neg =>
                have hml_pos : u.minLayer ≥ 1 := by omega
                have hdu_ge := landingDistance_ge_one u obs hml_pos
                have hdv_ge := landingDistance_ge_one v obs (by omega)
                omega

/-- settle step は方角共有・レイヤ差 ≥ 2 + minLayer ≤ 2 + 同一 minLayer で可換 -/
theorem settleStep_comm_dir_gap (s : Shape) (obs : List Layer) (u v : FallingUnit)
        (h_gap : ∀ p ∈ u.positions, ∀ q ∈ v.positions,
            p.dir = q.dir → p.layer ≠ q.layer ∧
              ¬(LayerIndex.verticallyAdjacent p.layer q.layer = true))
        (h_ml_u : u.minLayer ≤ 2) (h_ml_v : v.minLayer ≤ 2)
        (h_same_ml : u.minLayer = v.minLayer) :
        placeFallingUnit s
            (placeFallingUnit s obs u (landingDistance u obs))
            v (landingDistance v (placeFallingUnit s obs u (landingDistance u obs))) =
        placeFallingUnit s
            (placeFallingUnit s obs v (landingDistance v obs))
            u (landingDistance u (placeFallingUnit s obs v (landingDistance v obs))) := by
    -- landingDistance の独立性
    have h_drop_u := landingDistance_le_minLayer u obs
    have h_drop_v := landingDistance_le_minLayer v obs
    rw [landingDistance_placeFU_gap s obs u v (landingDistance u obs)
        h_gap h_ml_v h_drop_u h_ml_u
        (fun hv => landingDistance_ge_one u obs (by omega))]
    rw [landingDistance_placeFU_gap s obs v u (landingDistance v obs)
        (fun p hp q hq hd => let ⟨a, b⟩ := h_gap q hq p hp hd.symm
          ⟨a.symm, by rw [LayerIndex.verticallyAdjacent_symm]; exact b⟩)
        h_ml_u h_drop_v h_ml_v
        (fun hu => landingDistance_ge_one v obs (by omega))]
    -- placeFallingUnit の可換性（配置レイヤの素性から）
    apply placeFallingUnit_comm_of_layer_disjoint
    intro p hp q hq hdir
    have ⟨hne_layer, h_not_adj⟩ := h_gap p hp q hq hdir
    simp only [LayerIndex.verticallyAdjacent, Bool.or_eq_true, beq_iff_eq] at h_not_adj
    push Not at h_not_adj
    have hp_ge : landingDistance u obs ≤ p.layer :=
        le_trans h_drop_u (minLayer_le_layer hp u.minLayer (le_refl u.minLayer))
    have hq_ge : landingDistance v obs ≤ q.layer :=
        le_trans h_drop_v (minLayer_le_layer hq v.minLayer (le_refl v.minLayer))
    exact placedLayer_ne_of_gap obs u v p q h_ml_u h_same_ml hne_layer h_not_adj
        h_drop_u h_drop_v hp_ge hq_ge

-- ============================================================
-- tied 要素の方角非共有性と foldl 可換性
-- ============================================================

/-- foldl-min-option の補助関数（定義の一致問題を回避するため独立定義） -/
def foldMinOption : Option Nat → Nat → Option Nat :=
    fun acc l => some (match acc with | some a => min a l | none => l)

/-- foldMinOption (some init) rest = some v → v = init ∨ v ∈ rest -/
theorem foldMinOption_some_mem (rest : List Nat) (init v : Nat)
        (h : rest.foldl foldMinOption (some init) = some v) :
        v = init ∨ v ∈ rest := by
    induction rest generalizing init with
    | nil => simp only [List.foldl, Option.some.injEq] at h; exact .inl h.symm
    | cons b tail ih =>
        simp only [List.foldl_cons, foldMinOption] at h
        cases ih (min init b) h with
        | inl heq =>
            cases Nat.le_total init b with
            | inl hle => rw [Nat.min_eq_left hle] at heq; exact .inl heq
            | inr hle => rw [Nat.min_eq_right hle] at heq; exact .inr (heq ▸ .head tail)
        | inr hmem => exact .inr (.tail b hmem)

/-- foldMinOption none layers = some v → v ∈ layers -/
theorem foldMinOption_none_mem (layers : List Nat) (v : Nat)
        (h : layers.foldl foldMinOption none = some v) :
        v ∈ layers := by
    cases layers with
    | nil => simp only [List.foldl, reduceCtorEq] at h
    | cons a rest =>
        simp only [List.foldl_cons, foldMinOption] at h
        cases foldMinOption_some_mem rest a v h with
        | inl heq => exact heq ▸ .head rest
        | inr hmem => exact .tail a hmem

/-- foldMinOption (some init) rest は常に some を返す -/
theorem foldMinOption_some_isSome (rest : List Nat) (init : Nat) :
        ∃ v, rest.foldl foldMinOption (some init) = some v := by
    induction rest generalizing init with
    | nil => exact ⟨init, rfl⟩
    | cons y ys ih => simp only [List.foldl_cons, foldMinOption]; exact ih (min init y)

/-- foldMinOption (some init) rest = some v → v ≤ init -/
theorem foldMinOption_some_le_init (rest : List Nat) (init v : Nat)
        (h : rest.foldl foldMinOption (some init) = some v) :
        v ≤ init := by
    induction rest generalizing init with
    | nil =>
        simp only [List.foldl, Option.some.injEq] at h
        omega
    | cons y ys ih =>
        simp only [List.foldl_cons, foldMinOption] at h
        exact Nat.le_trans (ih (min init y) h) (Nat.min_le_left init y)

/-- foldMinOption (some init) rest = some v → 任意の m ∈ rest に対して v ≤ m -/
theorem foldMinOption_some_le_mem (rest : List Nat) (init v : Nat)
        (h : rest.foldl foldMinOption (some init) = some v) (m : Nat) (hm : m ∈ rest) :
        v ≤ m := by
    induction rest generalizing init with
    | nil => nomatch hm
    | cons y ys ih =>
        simp only [List.foldl_cons, foldMinOption] at h
        cases hm with
        | head _ =>
            exact Nat.le_trans (foldMinOption_some_le_init ys (min init m) v h)
                (Nat.min_le_right init m)
        | tail _ hm_ys =>
            exact ih (min init y) h hm_ys

/-- foldMinOption none layers = some v → 任意の m ∈ layers に対して v ≤ m -/
theorem foldMinOption_none_le (layers : List Nat) (v : Nat)
        (h : layers.foldl foldMinOption none = some v) (m : Nat) (hm : m ∈ layers) :
        v ≤ m := by
    cases layers with
    | nil => nomatch hm
    | cons y ys =>
        simp only [List.foldl_cons, foldMinOption] at h
        cases hm with
        | head _ => exact foldMinOption_some_le_init ys m v h
        | tail _ hm_ys => exact foldMinOption_some_le_mem ys y v h m hm_ys

/-- minLayerAtDir が some を返すなら、その方角・レイヤの位置が実在する -/
theorem minLayerAtDir_some_witness (u : FallingUnit) (dir : Direction) (l : Nat)
        (h : u.minLayerAtDir dir = some l) :
        ∃ p, p ∈ u.positions ∧ p.dir = dir ∧ p.layer = l := by
    simp only [FallingUnit.minLayerAtDir] at h
    change (u.positions.filterMap fun p =>
        if p.dir == dir then some p.layer else none).foldl foldMinOption none = some l at h
    have h_layers := foldMinOption_none_mem _ l h
    rw [List.mem_filterMap] at h_layers
    obtain ⟨p, hp_mem, hp_eq⟩ := h_layers
    by_cases hd : (p.dir == dir) = true
    · simp only [hd, ite_true] at hp_eq
      exact ⟨p, hp_mem, eq_of_beq hd, Option.some.inj hp_eq⟩
    · simp only [hd, ite_false, reduceCtorEq] at hp_eq

/-- 指定方角の位置が存在するなら minLayerAtDir は some -/
theorem minLayerAtDir_some_of_mem (u : FallingUnit) (dir : Direction) (p : QuarterPos)
        (hp : p ∈ u.positions) (hd : p.dir = dir) :
        ∃ l, u.minLayerAtDir dir = some l := by
    simp only [FallingUnit.minLayerAtDir]
    change ∃ l, (u.positions.filterMap fun q =>
        if q.dir == dir then some q.layer else none).foldl foldMinOption none = some l
    have h_ne : (u.positions.filterMap fun q =>
            if q.dir == dir then some q.layer else none) ≠ [] := by
        intro h_empty
        have : p.layer ∈ (u.positions.filterMap fun q =>
                if q.dir == dir then some q.layer else none) :=
            List.mem_filterMap.mpr ⟨p, hp, by simp only [hd, BEq.rfl, ↓reduceIte]⟩
        rw [h_empty] at this; exact absurd this List.not_mem_nil
    -- 非空リスト: 先頭を取得して foldl が some を返すことを示す
    have ⟨a, rest, hl⟩ : ∃ a rest, (u.positions.filterMap fun q =>
            if q.dir == dir then some q.layer else none) = a :: rest := by
        cases h_list : (u.positions.filterMap fun q =>
            if q.dir == dir then some q.layer else none) with
        | nil => exact absurd h_list h_ne
        | cons a rest => exact ⟨a, rest, rfl⟩
    rw [hl]
    simp only [List.foldl_cons]
    change ∃ l, rest.foldl foldMinOption (foldMinOption none a) = some l
    simp only [foldMinOption]
    exact foldMinOption_some_isSome rest a

/-- shouldProcessBefore u v = false のとき、共有方角の minLayerAtDir で u ≥ v -/
theorem shouldProcessBefore_false_minLayerAtDir_ge (u v : FallingUnit) (dir : Direction)
        (h : shouldProcessBefore u v = false)
        (lu lv : Nat)
        (hu : u.minLayerAtDir dir = some lu)
        (hv : v.minLayerAtDir dir = some lv) :
        lu ≥ lv := by
    -- shouldProcessBefore u v = false → Direction.all.any (fun dir => ...) = false
    -- 展開して dir ケース分析
    simp only [shouldProcessBefore, Direction.all, List.any_cons, List.any_nil, Bool.or_false] at h
    -- h は4方角の or = false。各方角でケース分け。
    rcases dir with _ | _ | _ | _ <;> simp_all only [FallingUnit.minLayerAtDir, beq_iff_eq, Bool.or_eq_false_iff, ge_iff_le, decide_eq_false_iff_not, not_lt]

/-- shouldProcessBefore 双方向 false + 位置非共有 → 方角列非共有
    （tied 要素は列を共有しない） -/
theorem tied_no_shared_dir (u v : FallingUnit)
        (h_tied_uv : shouldProcessBefore u v = false)
        (h_tied_vu : shouldProcessBefore v u = false)
        (h_disj : ∀ p, p ∈ u.positions → v.positions.any (· == p) = false) :
        ∀ p, p ∈ u.positions → v.positions.any (fun q => q.dir == p.dir) = false := by
    intro p hp
    -- v.positions.any (dir == p.dir) が true だと仮定して矛盾を導く
    -- Bool は Decidable なので cases で分場合分け
    cases h_any : v.positions.any (fun q => q.dir == p.dir) with
    | false => rfl
    | true =>
        -- v に p.dir を持つ位置 q が存在する
        obtain ⟨q, hq_mem, hq_dir⟩ := List.any_eq_true.mp h_any
        have hd : q.dir = p.dir := eq_of_beq hq_dir
        -- minLayerAtDir が some であることを示す
        obtain ⟨lu, hlu⟩ := minLayerAtDir_some_of_mem u p.dir p hp rfl
        obtain ⟨lv, hlv⟩ := minLayerAtDir_some_of_mem v p.dir q hq_mem hd
        -- shouldProcessBefore 双方 false → lu ≥ lv ∧ lv ≥ lu → lu = lv
        have h_ge := shouldProcessBefore_false_minLayerAtDir_ge u v p.dir h_tied_uv lu lv hlu hlv
        have h_le := shouldProcessBefore_false_minLayerAtDir_ge v u p.dir h_tied_vu lv lu hlv hlu
        have h_eq : lu = lv := by omega
        -- minLayerAtDir_some_witness: v に (lv, p.dir) の位置が存在
        obtain ⟨q', hq'_mem, hq'_dir, hq'_layer⟩ := minLayerAtDir_some_witness v p.dir lv hlv
        -- u に (lu, p.dir) の位置が存在
        obtain ⟨p', hp'_mem, hp'_dir, hp'_layer⟩ := minLayerAtDir_some_witness u p.dir lu hlu
        -- p' と q' は同じ (layer, dir) → q' = p'
        have h_qp : q' = p' := by
            have hl : q'.layer = p'.layer := by rw [hq'_layer, hp'_layer, h_eq]
            have hd' : q'.dir = p'.dir := by rw [hq'_dir, hp'_dir]
            exact match q', p', hl, hd' with
            | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl
        -- h_disj p' hp'_mem : v.positions.any (· == p') = false
        have h_p'_disj := h_disj p' hp'_mem
        -- だが q' ∈ v.positions で q' = p' → v.positions.any (· == p') = true
        have : v.positions.any (· == p') = true := by
            apply List.any_eq_true.mpr
            exact ⟨q', hq'_mem, h_qp ▸ beq_self_eq_true q'⟩
        rw [this] at h_p'_disj
        exact absurd h_p'_disj (by decide)

/-- tied + 位置非共有の逆方向版 -/
theorem tied_no_shared_dir_rev (u v : FallingUnit)
        (h_tied_uv : shouldProcessBefore u v = false)
        (h_tied_vu : shouldProcessBefore v u = false)
        (h_disj : ∀ p, p ∈ v.positions → u.positions.any (· == p) = false) :
        ∀ p, p ∈ v.positions → u.positions.any (fun q => q.dir == p.dir) = false :=
    tied_no_shared_dir v u h_tied_vu h_tied_uv h_disj

/-- 先頭 2 要素が方角素なら foldl 結果はスワップで不変 -/
theorem foldl_settle_head_swap (s : Shape) (u v : FallingUnit)
        (rest : List FallingUnit) (obs : List Layer)
        (h_uv : ∀ p, p ∈ u.positions → v.positions.any (fun q => q.dir == p.dir) = false)
        (h_vu : ∀ p, p ∈ v.positions → u.positions.any (fun q => q.dir == p.dir) = false) :
        (u :: v :: rest).foldl (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs =
        (v :: u :: rest).foldl (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs := by
    simp only [List.foldl_cons]
    congr 1
    exact settleStep_comm_ne_dir s obs u v h_uv h_vu

-- ============================================================
-- positions .any 拡張性（ext）補題群
-- ============================================================

/-- minLayerAtDir は positions .any にのみ依存する -/
theorem minLayerAtDir_ext {u1 u2 : FallingUnit}
        (h : ∀ p, u1.positions.any (· == p) = u2.positions.any (· == p))
        (dir : Direction) :
        u1.minLayerAtDir dir = u2.minLayerAtDir dir := by
    cases h1 : u1.minLayerAtDir dir with
    | none =>
        -- u1 に dir 方角の位置がない → u2 にもない
        cases h2 : u2.minLayerAtDir dir with
        | none => rfl
        | some l2 =>
            exfalso
            obtain ⟨p2, hp2_mem, hp2_dir, _⟩ := minLayerAtDir_some_witness u2 dir l2 h2
            -- p2 ∈ u2.positions → p2 ∈ u1.positions (by .any 等価)
            have hp2_in_u1 : p2 ∈ u1.positions :=
                mem_of_any_beq_eq h hp2_mem
            -- u1 に dir を持つ位置が存在 → minLayerAtDir ≠ none
            obtain ⟨l, hl⟩ := minLayerAtDir_some_of_mem u1 dir p2 hp2_in_u1 hp2_dir
            rw [hl] at h1; exact absurd h1 (by simp only [reduceCtorEq, not_false_eq_true])
    | some l1 =>
        cases h2 : u2.minLayerAtDir dir with
        | none =>
            exfalso
            obtain ⟨p1, hp1_mem, hp1_dir, _⟩ := minLayerAtDir_some_witness u1 dir l1 h1
            have hp1_in_u2 : p1 ∈ u2.positions :=
                mem_of_any_beq_eq (fun p => (h p).symm) hp1_mem
            obtain ⟨l, hl⟩ := minLayerAtDir_some_of_mem u2 dir p1 hp1_in_u2 hp1_dir
            rw [hl] at h2; exact absurd h2 (by simp only [reduceCtorEq, not_false_eq_true])
        | some l2 =>
            -- 両方 some → l1 = l2
            congr 1
            apply Nat.le_antisymm
            · -- l1 ≤ l2: l2 の witness p2 が u1 にも属し、l1 ≤ p2.layer
              obtain ⟨p2, hp2_mem, hp2_dir, hp2_layer⟩ :=
                  minLayerAtDir_some_witness u2 dir l2 h2
              have hp2_in_u1 : p2 ∈ u1.positions :=
                  mem_of_any_beq_eq h hp2_mem
              -- minLayerAtDir は dir フィルタ後の最小値 → l1 ≤ p2.layer
              -- p2 ∈ u1.positions ∧ p2.dir = dir → u1.minLayerAtDir dir ≤ p2.layer
              simp only [FallingUnit.minLayerAtDir] at h1
              change (u1.positions.filterMap fun p =>
                  if p.dir == dir then some p.layer else none).foldl
                  foldMinOption none = some l1 at h1
              have : p2.layer ∈ (u1.positions.filterMap fun p =>
                  if p.dir == dir then some p.layer else none) := by
                  rw [List.mem_filterMap]
                  exact ⟨p2, hp2_in_u1, by simp only [show (p2.dir == dir) = true from by
                      rw [hp2_dir]; exact BEq.rfl, ↓reduceIte]⟩
              rw [← hp2_layer]
              exact foldMinOption_none_le _ l1 h1 p2.layer this
            · obtain ⟨p1, hp1_mem, hp1_dir, hp1_layer⟩ :=
                  minLayerAtDir_some_witness u1 dir l1 h1
              have hp1_in_u2 : p1 ∈ u2.positions :=
                  mem_of_any_beq_eq (fun p => (h p).symm) hp1_mem
              simp only [FallingUnit.minLayerAtDir] at h2
              change (u2.positions.filterMap fun p =>
                  if p.dir == dir then some p.layer else none).foldl
                  foldMinOption none = some l2 at h2
              have : p1.layer ∈ (u2.positions.filterMap fun p =>
                  if p.dir == dir then some p.layer else none) := by
                  rw [List.mem_filterMap]
                  exact ⟨p1, hp1_in_u2, by simp only [show (p1.dir == dir) = true from by
                      rw [hp1_dir]; exact BEq.rfl, ↓reduceIte]⟩
              rw [← hp1_layer]
              exact foldMinOption_none_le _ l2 h2 p1.layer this

/-- shouldProcessBefore は positions .any にのみ依存する -/
theorem shouldProcessBefore_ext {u1 u2 v1 v2 : FallingUnit}
        (hu : ∀ p, u1.positions.any (· == p) = u2.positions.any (· == p))
        (hv : ∀ p, v1.positions.any (· == p) = v2.positions.any (· == p)) :
        shouldProcessBefore u1 v1 = shouldProcessBefore u2 v2 := by
    simp only [shouldProcessBefore]
    congr 1
    funext dir
    rw [minLayerAtDir_ext hu dir, minLayerAtDir_ext hv dir]

-- ============================================================
-- insertSorted / sortFallingUnits の pointwise .any 等価保存
-- ============================================================

/-- insertSorted の結果の長さ -/
theorem insertSorted_length (u : FallingUnit) (sorted : List FallingUnit) (fuel : Nat) :
        (insertSorted u sorted fuel).length = sorted.length + 1 := by
    induction fuel generalizing sorted with
    | zero => simp only [insertSorted, List.length_cons]
    | succ n ih =>
        cases sorted with
        | nil => simp only [insertSorted, List.length_cons, List.length_nil, Nat.zero_add]
        | cons v rest =>
            simp only [insertSorted]
            split
            · simp only [List.length_cons]
            · simp only [List.length_cons, ih rest]

/-- sortFallingUnits の結果の長さ -/
theorem sortFallingUnits_length (units : List FallingUnit) :
        (sortFallingUnits units).length = units.length := by
    exact (sortFallingUnits_perm units).length_eq

/-- positions .any 等価な要素を pointwise .any 等価なソート済みリストに挿入すると、
    結果も pointwise .any 等価になる -/
theorem insertSorted_pointwise_ext
        {u1 u2 : FallingUnit}
        (hu : ∀ p, u1.positions.any (· == p) = u2.positions.any (· == p))
        {sorted1 sorted2 : List FallingUnit}
        (h_len : sorted1.length = sorted2.length)
        (h_pw : ∀ (i : Nat) (hi : i < sorted1.length) (p : QuarterPos),
            (sorted1[i]'hi).positions.any (· == p) =
            (sorted2[i]'(h_len ▸ hi)).positions.any (· == p))
        (fuel : Nat) :
        (insertSorted u1 sorted1 fuel).length = (insertSorted u2 sorted2 fuel).length ∧
        ∀ (i : Nat) (hi : i < (insertSorted u1 sorted1 fuel).length) (p : QuarterPos),
            ((insertSorted u1 sorted1 fuel)[i]'hi).positions.any (· == p) =
            ((insertSorted u2 sorted2 fuel)[i]'(by
                rw [insertSorted_length] at hi ⊢
                rw [h_len] at hi; exact hi)).positions.any (· == p) := by
    induction fuel generalizing sorted1 sorted2 with
    | zero =>
        -- fuel = 0: insertSorted u sorted 0 = u :: sorted
        simp only [insertSorted]
        constructor
        · simp only [List.length_cons, h_len]
        · intro i hi p
          cases i with
          | zero => exact hu p
          | succ j => exact h_pw j (by simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi; omega) p
    | succ n ih =>
        cases sorted1 with
        | nil =>
            -- sorted1 = [] → sorted2 = []
            have : sorted2 = [] := by
                cases sorted2 with
                | nil => rfl
                | cons _ _ => simp only [List.length_nil, List.length_cons, Nat.right_eq_add, Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero, and_false] at h_len
            subst this
            simp only [insertSorted]
            exact ⟨rfl, fun i hi p => by cases i with | zero => exact hu p | succ j => simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_one_iff, Nat.add_eq_zero_iff, one_ne_zero, and_false] at hi⟩
        | cons v1 rest1 =>
            -- sorted1 = v1 :: rest1 → sorted2 = v2 :: rest2
            cases sorted2 with
            | nil => simp only [List.length_cons, List.length_nil, Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero, and_false] at h_len
            | cons v2 rest2 =>
                -- v1 と v2 は .any 等価 (i=0)
                have h_v : ∀ p, v1.positions.any (· == p) = v2.positions.any (· == p) :=
                    fun p => h_pw 0 (by simp only [List.length_cons, Nat.zero_lt_succ]) p
                -- rest1 と rest2 は pointwise .any 等価
                have h_rest_len : rest1.length = rest2.length := by simp only [List.length_cons, Nat.add_right_cancel_iff] at h_len; exact h_len
                have h_rest_pw : ∀ (i : Nat) (hi : i < rest1.length) (p : QuarterPos),
                        (rest1[i]'hi).positions.any (· == p) =
                        (rest2[i]'(h_rest_len ▸ hi)).positions.any (· == p) :=
                    fun i hi p => h_pw (i + 1) (by simp only [List.length_cons, Nat.add_lt_add_iff_right]; omega) p
                -- shouldProcessBefore の等価性
                have h_spb_uv : shouldProcessBefore u1 v1 = shouldProcessBefore u2 v2 :=
                    shouldProcessBefore_ext hu h_v
                -- 条件分岐: by_cases で分岐
                by_cases h1 : shouldProcessBefore u1 v1
                · -- shouldProcessBefore u1 v1 = true → shouldProcessBefore u2 v2 = true
                  have h1' : shouldProcessBefore u2 v2 = true := h_spb_uv ▸ h1
                  have lhs : insertSorted u1 (v1 :: rest1) (n + 1) = u1 :: v1 :: rest1 := by
                      show (if shouldProcessBefore u1 v1 then u1 :: v1 :: rest1
                          else v1 :: insertSorted u1 rest1 n) = _
                      simp only [h1, ↓reduceIte]
                  have rhs : insertSorted u2 (v2 :: rest2) (n + 1) = u2 :: v2 :: rest2 := by
                      show (if shouldProcessBefore u2 v2 then u2 :: v2 :: rest2
                          else _) = _
                      simp only [h1', ↓reduceIte]
                  simp only [lhs, rhs]
                  constructor
                  · simp only [List.length_cons, h_len]
                  · intro i hi p
                    cases i with
                    | zero => exact hu p
                    | succ j =>
                        cases j with
                        | zero => exact h_v p
                        | succ k =>
                            simp only [List.getElem_cons_succ]
                            exact h_pw (k + 1) (by simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi ⊢ ⊢; omega) p
                · -- shouldProcessBefore u1 v1 = false → スキップして再帰
                  simp only [Bool.not_eq_true] at h1
                  have h1' : shouldProcessBefore u2 v2 = false := h_spb_uv ▸ h1
                  have lhs : insertSorted u1 (v1 :: rest1) (n + 1) =
                      v1 :: insertSorted u1 rest1 n := by
                      show (if shouldProcessBefore u1 v1 then u1 :: v1 :: rest1
                          else v1 :: insertSorted u1 rest1 n) = _
                      simp only [h1, Bool.false_eq_true, ↓reduceIte]
                  have rhs : insertSorted u2 (v2 :: rest2) (n + 1) =
                      v2 :: insertSorted u2 rest2 n := by
                      show (if shouldProcessBefore u2 v2 then _
                          else v2 :: insertSorted u2 rest2 n) = _
                      simp only [h1', Bool.false_eq_true, ↓reduceIte]
                  simp only [lhs, rhs]
                  have ih_result := ih h_rest_len h_rest_pw
                  constructor
                  · simp only [List.length_cons, ih_result.1]
                  · intro i hi p
                    cases i with
                    | zero => exact h_v p
                    | succ j => exact ih_result.2 j (by simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi; exact hi) p

/-- sortFallingUnits は pointwise .any 等価な入力に対して pointwise .any 等価な出力を生む -/
theorem sortFallingUnits_pointwise_ext
        {l1 l2 : List FallingUnit}
        (h_len : l1.length = l2.length)
        (h_pw : ∀ (i : Nat) (hi : i < l1.length) (p : QuarterPos),
            (l1[i]'hi).positions.any (· == p) =
            (l2[i]'(h_len ▸ hi)).positions.any (· == p)) :
        (sortFallingUnits l1).length = (sortFallingUnits l2).length ∧
        ∀ (i : Nat) (hi : i < (sortFallingUnits l1).length) (p : QuarterPos),
            ((sortFallingUnits l1)[i]'hi).positions.any (· == p) =
            ((sortFallingUnits l2)[i]'(by
                rw [sortFallingUnits_length] at hi ⊢
                rw [h_len] at hi; exact hi)).positions.any (· == p) := by
    -- foldl の帰納法で pointwise 等価を保存する補助定理
    -- sortFallingUnits = foldl (fun sorted u => insertSorted u sorted (sorted.length + 1)) []
    -- l1, l2 に対する帰納法で acc1, acc2 を保持
    have key : ∀ (l1' l2' : List FallingUnit)
        (h_len' : l1'.length = l2'.length)
        (h_pw' : ∀ (i : Nat) (hi : i < l1'.length) (p : QuarterPos),
            (l1'[i]'hi).positions.any (· == p) =
            (l2'[i]'(h_len' ▸ hi)).positions.any (· == p))
        (acc1 acc2 : List FallingUnit)
        (ha_len : acc1.length = acc2.length)
        (ha_pw : ∀ (i : Nat) (hi : i < acc1.length) (p : QuarterPos),
            (acc1[i]'hi).positions.any (· == p) =
            (acc2[i]'(ha_len ▸ hi)).positions.any (· == p)),
        let res1 := l1'.foldl (fun sorted u => insertSorted u sorted (sorted.length + 1)) acc1
        let res2 := l2'.foldl (fun sorted u => insertSorted u sorted (sorted.length + 1)) acc2
        res1.length = res2.length ∧
        ∀ (i : Nat) (hi1 : i < res1.length) (hi2 : i < res2.length) (p : QuarterPos),
            (res1[i]'hi1).positions.any (· == p) =
            (res2[i]'hi2).positions.any (· == p) := by
      intro l1' l2' h_len' h_pw'
      induction l1' generalizing l2' with
      | nil =>
          have : l2' = [] := by cases l2' with | nil => rfl | cons _ _ => simp only [List.length_nil, List.length_cons, Nat.right_eq_add, Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero, and_false] at h_len'
          subst this
          intro acc1 acc2 ha_len ha_pw
          simp only [List.foldl]
          exact ⟨ha_len, fun i hi1 _hi2 p => ha_pw i hi1 p⟩
      | cons u1 rest1 ih =>
          cases l2' with
          | nil => simp only [List.length_cons, List.length_nil, Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero, and_false] at h_len'
          | cons u2 rest2 =>
              have h_rest_len : rest1.length = rest2.length := by simp only [List.length_cons, Nat.add_right_cancel_iff] at h_len'; exact h_len'
              have h_u : ∀ p, u1.positions.any (· == p) = u2.positions.any (· == p) :=
                  fun p => h_pw' 0 (by simp only [List.length_cons, Nat.zero_lt_succ]) p
              have h_rest_pw : ∀ (i : Nat) (hi : i < rest1.length) (p : QuarterPos),
                      (rest1[i]'hi).positions.any (· == p) =
                      (rest2[i]'(h_rest_len ▸ hi)).positions.any (· == p) :=
                  fun i hi p => h_pw' (i + 1) (by simp only [List.length_cons, Nat.add_lt_add_iff_right]; omega) p
              intro acc1 acc2 ha_len ha_pw
              simp only [List.foldl]
              have h_ins := insertSorted_pointwise_ext h_u ha_len ha_pw (acc1.length + 1)
              -- fuel の正規化: acc2.length + 1 = acc1.length + 1
              have h_rw : insertSorted u2 acc2 (acc2.length + 1) = insertSorted u2 acc2 (acc1.length + 1) :=
                  congrArg (insertSorted u2 acc2) (by omega)
              simp only [h_rw]
              exact ih rest2 h_rest_len h_rest_pw
                  (insertSorted u1 acc1 (acc1.length + 1))
                  (insertSorted u2 acc2 (acc1.length + 1))
                  h_ins.1 h_ins.2
    -- key を sortFallingUnits に適用
    simp only [sortFallingUnits]
    have result := key l1 l2 h_len h_pw [] [] rfl (fun _ hi => absurd hi (by simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true]))
    constructor
    · exact result.1
    · intro i hi p
      exact result.2 i hi _ p


end Gravity

