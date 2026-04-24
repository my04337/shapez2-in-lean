-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity.CommExt.Arith
import S2IL.Operations.Gravity.Equivariance.Clusters

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

/-- S1 Sub-lemma 3e (前半): floatingUnits の位置にある非接地・非空象限の ngsWeight は
    `layer + 1` に等しい。`nonGroundedLayerSum_clear_add` の右辺を settling 位置の
    純粋な layer 合計へ書き換えるための橋渡し補題。 -/
theorem ngsWeight_eq_layer_succ_of_mem_floatingUnits_positions
        (s : Shape) (p : QuarterPos)
        (h : ((floatingUnits s).flatMap FallingUnit.positions).any (· == p) = true) :
        ngsWeight s p = p.layer + 1 := by
    obtain ⟨_, ⟨q, hq, hq_ne⟩, h_ug⟩ := floatingUnits_positions_getQuarter s p h
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hq_ne
    simp [ngsWeight, hq, hq_ne, h_ug]

/-- S1 Sub-lemma 3e (後半): floatingUnits 位置の部分リスト上で `ngsWeight s` と
    `(·.layer + 1)` は同じ map を与える。`nonGroundedLayerSum_clear_add` の
    Σ を純粋な layer 合計に書き換える際に使用。 -/
theorem map_ngsWeight_eq_map_layer_succ_of_subset_floatingUnits_positions
        (s : Shape) (ps : List QuarterPos)
        (h : ∀ p ∈ ps,
            ((floatingUnits s).flatMap FallingUnit.positions).any (· == p) = true) :
        ps.map (ngsWeight s) = ps.map (fun p => p.layer + 1) :=
    List.map_congr_left (fun p hp =>
        ngsWeight_eq_layer_succ_of_mem_floatingUnits_positions s p (h p hp))

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

-- ============================================================
-- S1 Sub-lemma #8 基盤: 着地位置の単射性
-- ============================================================

/-- 着地写像 `p ↦ ⟨p.layer - d, p.dir⟩` は、
    全要素が `p.layer ≥ d` を満たす位置リスト上で単射。
    下方向シフトは境界 `d` を下回らなければ layer を一意に復元できるため。

    `List.Nodup.map_on` と組み合わせると、Nodup 位置リストの
    landing map が Nodup であることが従う（`landing_map_nodup_of_layer_ge`）。-/
theorem landing_shift_injective_of_layer_ge {d : Nat}
        {p q : QuarterPos} (hp : d ≤ p.layer) (hq : d ≤ q.layer)
        (h_l : p.layer - d = q.layer - d) (h_dir : p.dir = q.dir) :
        p = q := by
    have h_layer : p.layer = q.layer := by omega
    cases p; cases q; simp_all

/-- 全要素が `p.layer ≥ d` を満たす Nodup 位置リストに対し、
    landing map 後も Nodup を保つ。
    S1 Sub-lemma #8 (`landing_positions_injective`) の基盤補題。-/
theorem landing_map_nodup_of_layer_ge
        (l : List QuarterPos) (d : Nat)
        (h_ge : ∀ p ∈ l, d ≤ p.layer) (h_nd : l.Nodup) :
        (l.map (fun p => (p.layer - d, p.dir))).Nodup := by
    refine List.Nodup.map_on ?_ h_nd
    intro p hp q hq h_eq
    obtain ⟨h_l, h_dir⟩ := Prod.mk.inj h_eq
    exact landing_shift_injective_of_layer_ge (h_ge p hp) (h_ge q hq) h_l h_dir

/-- 単一 FU に対する landing 単射性。`minLayer_le_layer` と組み合わせた便利版。
    `d ≤ u.minLayer` なら、`u.positions` 上で landing map は単射。-/
theorem landing_shift_injective_on_fu
        {u : FallingUnit} {d : Nat} (hd : d ≤ u.minLayer)
        {p q : QuarterPos} (hp : p ∈ u.positions) (hq : q ∈ u.positions)
        (h_l : p.layer - d = q.layer - d) (h_dir : p.dir = q.dir) :
        p = q :=
    landing_shift_injective_of_layer_ge
        (minLayer_le_layer hp d hd) (minLayer_le_layer hq d hd) h_l h_dir

/-- 単一 FU の Nodup 位置に対し、landing map 後も Nodup を保つ。
    `d ≤ u.minLayer` が前提。 -/
theorem landing_map_nodup_on_fu
        (u : FallingUnit) (d : Nat) (hd : d ≤ u.minLayer)
        (h_nd : u.positions.Nodup) :
        (u.positions.map (fun p => (p.layer - d, p.dir))).Nodup :=
    landing_map_nodup_of_layer_ge u.positions d
        (fun _ hp => minLayer_le_layer hp d hd) h_nd

/-- Pin の `positions` は常に Nodup（単一要素リスト）。 -/
theorem pin_positions_nodup (p : QuarterPos) :
        (FallingUnit.pin p).positions.Nodup := by
    simp [FallingUnit.positions]

/-- `structuralClusterList` は Nodup（BFS が重複を排除するため）。
    `structuralBfs_eq_generic` で `genericBfs` に還元し、`genericBfs_nodup` を適用。 -/
theorem structuralClusterList_nodup (s : Shape) (pos : QuarterPos) :
        (structuralClusterList s pos).Nodup := by
    unfold structuralClusterList
    rw [structuralBfs_eq_generic]
    exact genericBfs_nodup _ _ _ _ _ List.nodup_nil

-- ============================================================
-- S1 Sub-lemma #8e: floatingUnits 位置の交差性なし
-- ============================================================

/-- `allStructuralClustersList` は List.Disjoint で Pairwise。
    既存の index 版 `allStructuralClustersList_disjoint` を Pairwise 形に変換。 -/
theorem allStructuralClustersList_pairwise_disjoint (s : Shape) :
        (allStructuralClustersList s).Pairwise List.Disjoint := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij p hp_i hp_j
    have h_any_i : ((allStructuralClustersList s)[i]).any (· == p) = true :=
        List.any_eq_true.mpr ⟨p, hp_i, BEq.rfl⟩
    have h_any_j_false :
            ((allStructuralClustersList s)[j]).any (· == p) = false :=
        allStructuralClustersList_disjoint s i j hi hj (Nat.ne_of_lt hij) p h_any_i
    have h_any_j_true : ((allStructuralClustersList s)[j]).any (· == p) = true :=
        List.any_eq_true.mpr ⟨p, hp_j, BEq.rfl⟩
    rw [h_any_j_true] at h_any_j_false
    exact absurd h_any_j_false (by decide)

/-- cluster 位置は canFormBond（bondable seed + 構造的到達可能性による保存）。 -/
theorem cluster_position_bondable (s : Shape) {c : List QuarterPos}
        (hc : c ∈ allStructuralClustersList s) {p : QuarterPos} (hp : p ∈ c) :
        ∃ w, p.getQuarter s = some w ∧ w.canFormBond = true := by
    obtain ⟨pos, hc_eq, _, qq, hqq, h_bond⟩ :=
        allStructuralClustersList_is_structuralClusterList s c hc
    have h_any : (structuralClusterList s pos).any (· == p) = true :=
        hc_eq ▸ List.any_eq_true.mpr ⟨p, hp, BEq.rfl⟩
    have h_reach := structuralClusterList_sound s pos p h_any
    exact structuralReachable_canFormBond s pos p h_reach ⟨qq, hqq, h_bond⟩

/-- `allIsolatedPins` の要素は `getQuarter = some .pin`。定義のフィルタから直接。 -/
private theorem pin_position_getQuarter (s : Shape) {p : QuarterPos}
        (hp : p ∈ allIsolatedPins s) :
        p.getQuarter s = some Quarter.pin := by
    unfold allIsolatedPins at hp
    rw [List.mem_filter] at hp
    obtain ⟨_, h⟩ := hp
    match hq : p.getQuarter s with
    | some .pin => rfl
    | some .empty => rw [hq] at h; simp at h
    | some (.crystal _) => rw [hq] at h; simp at h
    | some (.colored _ _) => rw [hq] at h; simp at h
    | none => rw [hq] at h; simp at h

/-- Sub-lemma #8e: `floatingUnits` の異なる FU は positions が互いに素。

    3 ケース分解:
    - cluster × cluster: `allStructuralClustersList_pairwise_disjoint` 経由
    - pin × pin: `allValid_nodup` からの singleton 一意性
    - cluster × pin: cluster 位置は canFormBond=true, pin 位置は getQuarter=.pin (false) -/
theorem floatingUnits_positions_pairwise_disjoint (s : Shape) :
        (floatingUnits s).Pairwise
            (fun u v => List.Disjoint u.positions v.positions) := by
    unfold floatingUnits
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · -- clusters: Pairwise Disjoint on filtered allStructuralClustersList
      rw [List.pairwise_map]
      have h_pw := (allStructuralClustersList_pairwise_disjoint s).filter
          (p := fun cluster => cluster.all fun p => decide (p ∉ groundedPositions s))
      refine h_pw.imp (fun {a b} h => ?_)
      simp only [FallingUnit.positions]; exact h
    · -- pins: distinct pins → distinct singleton positions
      rw [List.pairwise_map]
      have h_nd : ((QuarterPos.allValid s).filter (fun p =>
              match p.getQuarter s with | some .pin => true | _ => false)).filter
            (fun p => decide (p ∉ groundedPositions s)) |>.Nodup :=
          ((allValid_nodup s).filter _).filter _
      have h_pw_ne : List.Pairwise (· ≠ ·) _ := h_nd
      refine h_pw_ne.imp (fun {a b} h p hpa hpb => ?_)
      simp only [FallingUnit.positions, List.mem_singleton] at hpa hpb
      exact h (hpa ▸ hpb)
    · -- cross: cluster vs pin
      intro uc huc up hup
      rw [List.mem_map] at huc hup
      obtain ⟨c, hc_mem, rfl⟩ := huc
      obtain ⟨pp, hp_mem, rfl⟩ := hup
      rw [List.mem_filter] at hc_mem hp_mem
      obtain ⟨hc_in_all, _⟩ := hc_mem
      obtain ⟨hp_in_pins, _⟩ := hp_mem
      intro q hq hq_eq
      simp only [FallingUnit.positions, List.mem_singleton] at hq_eq
      subst hq_eq
      obtain ⟨w, hw, hwb⟩ := cluster_position_bondable s hc_in_all hq
      have h_pin := pin_position_getQuarter s hp_in_pins
      rw [h_pin] at hw
      have : w = .pin := (Option.some.inj hw).symm
      subst this
      exact absurd hwb (by decide)

/-- Sub-lemma #8 本体: `floatingUnits` 全体の位置 flatMap が Nodup。

    `List.nodup_flatMap` 経由で per-FU Nodup + Pairwise Disjoint に分解。
    Landing map の単射性（`landing_map_nodup_of_layer_ge`）と組み合わせることで
    settling FU 全位置上の landing 結果が Nodup になる保証が得られる。 -/
theorem floatingUnits_flatMap_positions_nodup (s : Shape) :
        ((floatingUnits s).flatMap FallingUnit.positions).Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun u hu => ?_, floatingUnits_positions_pairwise_disjoint s⟩
    unfold floatingUnits at hu
    rw [List.mem_append, List.mem_map, List.mem_map] at hu
    rcases hu with ⟨c, hc, rfl⟩ | ⟨p, _, rfl⟩
    · rw [List.mem_filter] at hc
      obtain ⟨pos, rfl, _⟩ :=
          allStructuralClustersList_is_structuralClusterList s c hc.1
      exact structuralClusterList_nodup s pos
    · exact pin_positions_nodup p

-- ============================================================
--  FallingUnit リスト上の foldl min (per-FU 版)
--  minLayer を最小化するヘルパー群。
--  `waveStep_grounding_mono` の前提抽出で settling FU の minLayer = minML
--  および任意 FU の minLayer ≥ minML を導くために使う。
-- ============================================================

/-- foldl min は init と比較して単調減少（FallingUnit 版）。 -/
theorem foldl_min_fu_le_init (l : List FallingUnit) (init : Nat) :
        l.foldl (fun acc u => min acc u.minLayer) init ≤ init := by
    induction l generalizing init with
    | nil => exact le_refl _
    | cons x xs ih =>
        simp only [List.foldl_cons]
        exact le_trans (ih (min init x.minLayer)) (by simp)

/-- foldl min は l の各要素以下（FallingUnit 版）。 -/
theorem foldl_min_fu_le_mem (l : List FallingUnit) (init : Nat)
        {u : FallingUnit} (hu : u ∈ l) :
        l.foldl (fun acc v => min acc v.minLayer) init ≤ u.minLayer := by
    induction l generalizing init with
    | nil => exact absurd hu (by simp)
    | cons x xs ih =>
        simp only [List.foldl_cons]
        rcases List.mem_cons.mp hu with heq | hxs
        · exact le_trans (foldl_min_fu_le_init xs (min init x.minLayer))
            (heq ▸ by simp)
        · exact ih _ hxs

end Gravity
