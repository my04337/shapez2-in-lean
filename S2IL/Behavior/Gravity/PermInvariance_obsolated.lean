-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Behavior.Gravity.CommExt_obsolated

namespace Gravity

open _root_.QuarterPos (getQuarter_rotate180)
-- ============================================================
-- settle_foldl_eq: ソート後 foldl の等価性
-- ============================================================

-- ============================================================
-- 浮遊単位の位置素性
-- ============================================================

/-- QuarterPos.allValid s は重複なし (NoDup)。
    allValid s = (range lc).flatMap (fun li => Direction.all.map (fun d => ⟨li, d⟩))
    において、各内部リストは NoDup（Direction.all が 4 要素で重複なし）、
    異なる li の内部リストは disjoint（.layer が異なる）ため。 -/
theorem allValid_nodup (s : Shape) : (QuarterPos.allValid s).Nodup := by
    unfold QuarterPos.allValid
    rw [List.nodup_flatMap]
    refine ⟨fun li _ => ?_, ?_⟩
    · -- (Direction.all.map fun d => ⟨li, d⟩).Nodup
      -- Direction.all は 4 要素で重複なし、map は layer 固定で injective
      have h_dir : Direction.all.Nodup := by unfold Direction.all; decide
      exact h_dir.map fun {_ _} h => congr_arg QuarterPos.dir h
    · -- Pairwise (Disjoint on f) (range s.layerCount)
      -- 異なる layer index → 構築される QuarterPos の .layer が異なる → disjoint
      exact (@List.nodup_range s.layerCount).imp fun {li₁ li₂} h_ne x h₁ h₂ => by
        rw [List.mem_map] at h₁ h₂
        obtain ⟨_, _, rfl⟩ := h₁
        obtain ⟨_, _, h_eq⟩ := h₂
        exact h_ne (congr_arg QuarterPos.layer h_eq).symm

/-- allStructuralClustersList の各クラスタの全位置は bondable (canFormBond = true)。
    allStructuralClustersList_is_structuralClusterList + structuralClusterList_sound
    + structuralReachable_canFormBond から従う。 -/
theorem allStructuralClustersList_all_bondable (s : Shape)
        (c : List QuarterPos) (hc : c ∈ allStructuralClustersList s)
        (p : QuarterPos) (hp : c.any (· == p) = true) :
        ∃ v, p.getQuarter s = some v ∧ v.canFormBond = true := by
    have ⟨pos, h_eq, _, h_bond⟩ := allStructuralClustersList_is_structuralClusterList s c hc
    rw [h_eq] at hp
    exact structuralReachable_canFormBond s pos p (structuralClusterList_sound s pos p hp) h_bond

/-- allIsolatedPins に .any で含まれる位置のシェイプ上の象限は .pin である -/
theorem allIsolatedPins_is_pin (s : Shape) (p : QuarterPos)
        (hp : (allIsolatedPins s).any (· == p) = true) :
        p.getQuarter s = some .pin := by
    have h_mem : p ∈ allIsolatedPins s := by
        rw [List.any_eq_true] at hp
        obtain ⟨q, hq_mem, hq_beq⟩ := hp
        exact eq_of_beq hq_beq ▸ hq_mem
    unfold allIsolatedPins at h_mem
    rw [List.mem_filter] at h_mem
    have h_pred := h_mem.2
    -- h_pred : (match p.getQuarter s with | some .pin => true | _ => false) = true
    generalize h_gq : QuarterPos.getQuarter s p = gq at h_pred
    cases gq with
    | none => exact absurd h_pred (by decide)
    | some q' =>
        cases q' with
        | pin => exact h_gq ▸ rfl
        | empty => simp only [Bool.false_eq_true] at h_pred
        | crystal _ => simp only [Bool.false_eq_true] at h_pred
        | colored _ _ => simp only [Bool.false_eq_true] at h_pred

/-- floatingUnits をコンポーネントに展開するための等式 -/
theorem floatingUnits_eq_append (s : Shape) :
        floatingUnits s =
            ((allStructuralClustersList s).filter fun c =>
                c.all fun p => !((groundedPositionsList s).any (· == p))).map .cluster ++
            ((allIsolatedPins s).filter fun p =>
                !((groundedPositionsList s).any (· == p))).map .pin := by
    unfold floatingUnits
    simp_rw [decide_not_mem_groundedPositions]

/-- allStructuralClustersList は重複なし (Nodup)。
    各クラスタは seed 位置を含み（非空）、異なるインデックスのクラスタは
    位置素 (allStructuralClustersList_disjoint) であるため、
    等しいクラスタが2つ存在すると seed が共有され矛盾する。 -/
theorem allStructuralClustersList_nodup (s : Shape) :
        (allStructuralClustersList s).Nodup :=
    List.pairwise_iff_getElem.mpr fun i j hi hj h_lt => by
    intro h_eq
    -- cluster_i は seed pos_i を含む
    have ⟨pos_i, h_ci_eq, h_layer_i, _⟩ :=
        allStructuralClustersList_is_structuralClusterList s _ (List.getElem_mem hi)
    have h_has_seed : ((allStructuralClustersList s)[i]).any (· == pos_i) = true := by
        rw [h_ci_eq]
        exact structuralClusterList_complete s pos_i pos_i (by omega) GenericReachable.refl
    -- i < j → i ≠ j → disjoint → cluster_j に pos_i は含まれない
    have h_disj := allStructuralClustersList_disjoint s i j hi hj (by omega) pos_i h_has_seed
    -- しかし c_j = c_i なので pos_i を含むはず → 矛盾
    rw [← h_eq] at h_disj
    rw [h_has_seed] at h_disj
    exact Bool.noConfusion h_disj

/-- floatingUnits は重複なし (Nodup)。
    fc.map .cluster ++ fp.map .pin の形式で、
    fc は allStructuralClustersList の filter（Nodup保存）、.cluster は injective、
    fp は allIsolatedPins の filter（allValid の filter → Nodup）、.pin は injective、
    .cluster ≠ .pin → disjoint。 -/
theorem floatingUnits_nodup (s : Shape) : (floatingUnits s).Nodup := by
    rw [floatingUnits_eq_append, List.nodup_append']
    refine ⟨?_, ?_, ?_⟩
    · -- (fc.map .cluster).Nodup
      exact ((allStructuralClustersList_nodup s).filter _).map
        fun {_ _} h => FallingUnit.cluster.inj h
    · -- (fp.map .pin).Nodup
      have h_iso : (allIsolatedPins s).Nodup := by
          unfold allIsolatedPins; exact (allValid_nodup s).filter _
      exact (h_iso.filter _).map fun {_ _} h => FallingUnit.pin.inj h
    · -- Disjoint (.cluster vs .pin)
      intro x h₁ h₂
      rw [List.mem_map] at h₁ h₂
      obtain ⟨_, _, rfl⟩ := h₁
      obtain ⟨_, _, h_eq⟩ := h₂
      exact FallingUnit.noConfusion h_eq

/-- floatingUnits に含まれるクラスタ要素は allStructuralClustersList の要素である -/
private theorem cluster_mem_of_floatingUnit_mem (s : Shape) (ps : List QuarterPos)
        (h_mem : FallingUnit.cluster ps ∈ floatingUnits s) :
        ps ∈ allStructuralClustersList s := by
    rw [floatingUnits_eq_append, List.mem_append] at h_mem
    cases h_mem with
    | inl h =>
        rw [List.mem_map] at h
        obtain ⟨c, hc, h_eq⟩ := h
        exact FallingUnit.cluster.inj h_eq ▸ (List.mem_filter.mp hc).1
    | inr h =>
        rw [List.mem_map] at h
        obtain ⟨_, _, h_eq⟩ := h
        exact absurd h_eq (by intro h'; exact FallingUnit.noConfusion h')

/-- floatingUnits に含まれるピン要素は allIsolatedPins の要素である -/
private theorem pin_mem_of_floatingUnit_mem (s : Shape) (q : QuarterPos)
        (h_mem : FallingUnit.pin q ∈ floatingUnits s) :
        q ∈ allIsolatedPins s := by
    rw [floatingUnits_eq_append, List.mem_append] at h_mem
    cases h_mem with
    | inl h =>
        rw [List.mem_map] at h
        obtain ⟨_, _, h_eq⟩ := h
        exact absurd h_eq (by intro h'; exact FallingUnit.noConfusion h')
    | inr h =>
        rw [List.mem_map] at h
        obtain ⟨q', hq, h_eq⟩ := h
        exact FallingUnit.pin.inj h_eq ▸ (List.mem_filter.mp hq).1

/-- [q].any (· == p) = true なら q = p -/
private theorem singleton_any_eq_true_implies_eq (q p : QuarterPos)
        (h_any : [q].any (· == p) = true) : q = p := by
    rw [List.any_cons, List.any_nil, Bool.or_false] at h_any
    exact eq_of_beq h_any

/-- allStructuralClustersList の2クラスタが同じ位置 p を共有するならクラスタは等しい -/
private theorem cluster_positions_eq_of_shared_pos (s : Shape)
        (ps_i ps_j : List QuarterPos) (p : QuarterPos)
        (h_psi_mem : ps_i ∈ allStructuralClustersList s)
        (h_psj_mem : ps_j ∈ allStructuralClustersList s)
        (hp_i : ps_i.any (· == p) = true)
        (hp_j : ps_j.any (· == p) = true) :
        ps_i = ps_j := by
    have ⟨k_i, hk_i, hk_i_eq⟩ := List.mem_iff_getElem.mp h_psi_mem
    have ⟨k_j, hk_j, hk_j_eq⟩ := List.mem_iff_getElem.mp h_psj_mem
    have h_k_eq : k_i = k_j := by
        by_contra h_k_ne
        have h_disj := allStructuralClustersList_disjoint s k_i k_j hk_i hk_j h_k_ne p
            (hk_i_eq ▸ hp_i)
        rw [hk_j_eq] at h_disj
        exact absurd hp_j (by rw [h_disj]; exact Bool.noConfusion)
    subst h_k_eq
    exact hk_i_eq.symm.trans hk_j_eq

/-- floatingUnits の要素は pairwise で positions が素（各位置は最大1つの浮遊単位に属する）
    allStructuralClustersList は foldl + dedup で構築されるため、異なるクラスタは異なる
    連結成分に属し、位置を共有しない。孤立ピンは canFormBond=false のため
    クラスタに含まれず、互いに異なる位置を持つ。 -/
theorem floatingUnits_pairwise_disjoint (s : Shape) :
        ∀ (i j : Nat) (hi : i < (floatingUnits s).length)
            (hj : j < (floatingUnits s).length), i ≠ j →
        ∀ (p : QuarterPos),
            ((floatingUnits s)[i]'hi).positions.any (· == p) = true →
            ((floatingUnits s)[j]'hj).positions.any (· == p) = false := by
    intro i j hi hj h_ne p hp_i
    -- 矛盾法: j の unit にも p が属すると仮定して矛盾を導く
    cases hp_j : ((floatingUnits s)[j]'hj).positions.any (· == p)
    case false => rfl
    case true =>
    exfalso
    -- p は unit_i と unit_j の両方に含まれる。unit_i, unit_j の型（クラスタ/ピン）で場合分け
    cases h_ui : (floatingUnits s)[i]'hi with
    | cluster ps_i =>
        have hp_i' : ps_i.any (· == p) = true := by
            simp only [h_ui, FallingUnit.positions] at hp_i; exact hp_i
        -- ps_i ∈ allStructuralClustersList s を示す
        have h_psi_mem : ps_i ∈ allStructuralClustersList s := by
            exact cluster_mem_of_floatingUnit_mem s ps_i (h_ui ▸ List.getElem_mem hi)
        -- p は bondable（クラスタ由来）
        have h_bond := allStructuralClustersList_all_bondable s ps_i h_psi_mem p hp_i'
        obtain ⟨v, hv_eq, hv_bond⟩ := h_bond
        cases h_uj : (floatingUnits s)[j]'hj with
        | cluster ps_j =>
            -- CC case: 両方クラスタ
            have hp_j' : ps_j.any (· == p) = true := by
                simp only [h_uj, FallingUnit.positions] at hp_j; exact hp_j
            have h_psj_mem : ps_j ∈ allStructuralClustersList s := by
                exact cluster_mem_of_floatingUnit_mem s ps_j (h_uj ▸ List.getElem_mem hj)
            -- ps_i と ps_j は共に p を含む allStructuralClustersList の要素
            -- allStructuralClustersList_disjoint の対偶: 異なるインデックスなら位置を共有しない
            -- → 同一インデックス → ps_i = ps_j
            have h_ps_eq : ps_i = ps_j :=
                cluster_positions_eq_of_shared_pos s ps_i ps_j p h_psi_mem h_psj_mem hp_i' hp_j'
            have h_fu_eq : (floatingUnits s)[i]'hi = (floatingUnits s)[j]'hj :=
                h_ui.trans ((congr_arg FallingUnit.cluster h_ps_eq).trans h_uj.symm)
            exact absurd ((floatingUnits_nodup s).getElem_inj_iff.mp h_fu_eq) h_ne
        | pin q_j =>
            -- CP case: i はクラスタ（bondable）, j はピン（not bondable）
            have hp_j' : [q_j].any (· == p) = true := by
                simp only [h_uj, FallingUnit.positions] at hp_j; exact hp_j
            have h_eq_j : q_j = p := singleton_any_eq_true_implies_eq q_j p hp_j'
            -- q_j ∈ allIsolatedPins s
            have h_qj_mem : q_j ∈ allIsolatedPins s := by
                exact pin_mem_of_floatingUnit_mem s q_j (h_uj ▸ List.getElem_mem hj)
            -- q_j.getQuarter s = some .pin
            have h_pin := allIsolatedPins_is_pin s q_j
                (List.any_eq_true.mpr ⟨q_j, h_qj_mem, beq_self_eq_true q_j⟩)
            -- p = q_j → p.getQuarter s = some .pin → .pin.canFormBond = false
            rw [h_eq_j] at h_pin
            rw [h_pin] at hv_eq
            cases hv_eq
            -- v = .pin → v.canFormBond = false ≠ true
            exact absurd hv_bond (by decide)
    | pin q_i =>
        have hp_i' : [q_i].any (· == p) = true := by
            simp only [h_ui, FallingUnit.positions] at hp_i; exact hp_i
        have h_eq_i : q_i = p := singleton_any_eq_true_implies_eq q_i p hp_i'
        -- q_i ∈ allIsolatedPins s
        have h_qi_mem : q_i ∈ allIsolatedPins s := by
            exact pin_mem_of_floatingUnit_mem s q_i (h_ui ▸ List.getElem_mem hi)
        have h_pin_i := allIsolatedPins_is_pin s q_i
            (List.any_eq_true.mpr ⟨q_i, h_qi_mem, beq_self_eq_true q_i⟩)
        cases h_uj : (floatingUnits s)[j]'hj with
        | cluster ps_j =>
            -- PC case: i はピン, j はクラスタ（CP の対称）
            have hp_j' : ps_j.any (· == p) = true := by
                simp only [h_uj, FallingUnit.positions] at hp_j; exact hp_j
            have h_psj_mem : ps_j ∈ allStructuralClustersList s := by
                exact cluster_mem_of_floatingUnit_mem s ps_j (h_uj ▸ List.getElem_mem hj)
            have h_bond := allStructuralClustersList_all_bondable s ps_j h_psj_mem p hp_j'
            obtain ⟨v, hv_eq, hv_bond⟩ := h_bond
            -- q_i = p → p.getQuarter s = some .pin → contradiction with bondable
            rw [h_eq_i] at h_pin_i
            rw [h_pin_i] at hv_eq; cases hv_eq
            exact absurd hv_bond (by decide)
        | pin q_j =>
            -- PP case: 両方ピン → q_i = p = q_j
            have hp_j' : [q_j].any (· == p) = true := by
                simp only [h_uj, FallingUnit.positions] at hp_j; exact hp_j
            have h_eq_j : q_j = p := singleton_any_eq_true_implies_eq q_j p hp_j'
            -- q_i = p = q_j → floatingUnits[i] = .pin p = floatingUnits[j]
            -- NoDup → i = j → h_ne に矛盾
            have h_fu_eq : (floatingUnits s)[i]'hi = (floatingUnits s)[j]'hj :=
                h_ui.trans ((congr_arg FallingUnit.pin
                    (h_eq_i.trans h_eq_j.symm)).trans h_uj.symm)
            exact absurd ((floatingUnits_nodup s).getElem_inj_iff.mp h_fu_eq) h_ne

/-- map FU.rotate180 は位置素性を保存する -/
theorem map_rotate180_pairwise_disjoint (l : List FallingUnit)
        (h_disj : ∀ (i j : Nat) (hi : i < l.length) (hj : j < l.length), i ≠ j →
            ∀ p, (l[i]'hi).positions.any (· == p) = true →
                (l[j]'hj).positions.any (· == p) = false) :
        ∀ (i j : Nat) (hi : i < (l.map FallingUnit.rotate180).length)
            (hj : j < (l.map FallingUnit.rotate180).length), i ≠ j →
        ∀ p, ((l.map FallingUnit.rotate180)[i]'hi).positions.any (· == p) = true →
            ((l.map FallingUnit.rotate180)[j]'hj).positions.any (· == p) = false := by
    intro i j hi hj h_ne p h_any
    simp only [List.length_map] at hi hj
    simp only [List.getElem_map] at h_any ⊢
    rw [FallingUnit.positions_rotate180] at h_any ⊢
    rw [any_map_rotate180_beq] at h_any ⊢
    exact h_disj i j hi hj h_ne p.rotate180 h_any

-- ============================================================
-- settle_foldl_eq: ソート済み foldl の等価性
-- ============================================================

/-- リスト prefix ++ [u, v] ++ suffix の foldl は、u と v が方角素なら
    prefix ++ [v, u] ++ suffix の foldl と等しい -/
theorem foldl_settle_swap_at (s : Shape) (prefix_ : List FallingUnit)
        (u v : FallingUnit) (suffix : List FallingUnit) (obs : List Layer)
        (h_uv : ∀ p, p ∈ u.positions → v.positions.any (fun q => q.dir == p.dir) = false)
        (h_vu : ∀ p, p ∈ v.positions → u.positions.any (fun q => q.dir == p.dir) = false) :
        (prefix_ ++ u :: v :: suffix).foldl
            (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs =
        (prefix_ ++ v :: u :: suffix).foldl
            (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs := by
    rw [List.foldl_append, List.foldl_append]
    exact foldl_settle_head_swap s u v suffix _ h_uv h_vu

/-- floatingUnits s の各ユニットに対し、floatingUnits s.rotate180 に
    .any 等価かつ型が一致するクラスタユニットが存在する -/
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
        have h_bond_r180 : match pos.rotate180.getQuarter s.rotate180 with
                | some q => q.canFormBond = true | none => False := by
            rw [getQuarter_rotate180]
            obtain ⟨q, hq, hb⟩ := h_bondable; rw [hq]; exact hb
        have h_layer_r180 : pos.rotate180.layer < s.rotate180.layerCount := by
            rw [Shape.layerCount_rotate180, QuarterPos.rotate180_layer]; exact h_layer
        have h_covers := allStructuralClustersList_covers s.rotate180 pos.rotate180
            h_layer_r180 h_bond_r180
        rw [List.any_eq_true] at h_covers
        obtain ⟨c', hc'_mem, hc'_any⟩ := h_covers
        obtain ⟨pos', hc'_eq, _, _⟩ :=
            allStructuralClustersList_is_structuralClusterList s.rotate180 c' hc'_mem
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
            have h_sc_pos_r180 : (structuralClusterList s.rotate180 pos.rotate180).any (· == pos.rotate180) = true :=
                structuralClusterList_complete s.rotate180 pos.rotate180 pos.rotate180
                    (by rw [Shape.layerCount_rotate180]; omega)
                    GenericReachable.refl
            rw [hc'_eq]
            rw [any_map_rotate180_beq]
            rw [h_sc]
            have h_pos_r180_in_c' : (structuralClusterList s.rotate180 pos').any (· == pos.rotate180) = true := by
                rw [← hc'_eq]; exact hc'_any
            have h_reach_pos' : GenericReachable (isStructurallyBonded s.rotate180) pos.rotate180 pos' := by
                have h_pos_reach := structuralClusterList_sound s.rotate180 pos' pos.rotate180 h_pos_r180_in_c'
                exact h_pos_reach.symm (fun a b => isStructurallyBonded_symm s.rotate180 a b)
            have h_pos'_in_sc : (structuralClusterList s.rotate180 pos.rotate180).any (· == pos') = true :=
                structuralClusterList_complete s.rotate180 pos.rotate180 pos'
                    (by rw [Shape.layerCount_rotate180]; omega)
                    h_reach_pos'
            cases hq : (structuralClusterList s.rotate180 pos').any (· == q) with
            | true =>
                have h_q_reach := structuralClusterList_sound s.rotate180 pos' q hq
                have h_q_from_pos := GenericReachable.trans
                    ((structuralClusterList_sound s.rotate180 pos' pos.rotate180 h_pos_r180_in_c').symm
                        (fun a b => isStructurallyBonded_symm s.rotate180 a b))
                    h_q_reach
                symm; exact structuralClusterList_complete s.rotate180 pos.rotate180 q
                    (by rw [Shape.layerCount_rotate180]; omega)
                    h_q_from_pos
            | false =>
                -- q ∉ sc(s.r180, pos') → q ∉ sc(s.r180, pos.r180) も示す
                symm
                cases hq2 : (structuralClusterList s.rotate180 pos.rotate180).any (· == q) with
                | false => rfl
                | true =>
                    exfalso
                    have := structuralClusterList_complete s.rotate180 pos' q
                        (by rw [Shape.layerCount_rotate180]; omega)
                        (GenericReachable.trans
                            ((structuralClusterList_sound s.rotate180 pos.rotate180 pos' h_pos'_in_sc).symm
                                (fun a b => isStructurallyBonded_symm s.rotate180 a b))
                            (structuralClusterList_sound s.rotate180 pos.rotate180 q hq2))
                    rw [hq] at this; exact Bool.noConfusion this
        have h_floating : c'.all (fun p => !((groundedPositionsList s.rotate180).any (· == p))) = true := by
            rw [List.all_eq_true]
            intro q hq_mem
            have hq_any : c'.any (· == q) = true :=
                List.any_eq_true.mpr ⟨q, hq_mem, beq_self_eq_true q⟩
            rw [h_any_eq] at hq_any
            rw [any_map_rotate180_beq] at hq_any
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

/-- floatingUnits s の各ユニットに対し、floatingUnits s.rotate180 に
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
        have h_pin_r180 : p.rotate180 ∈ allIsolatedPins s.rotate180 := by
            unfold allIsolatedPins
            rw [CrystalBond.allValid_rotate180]
            rw [List.mem_filter]
            constructor
            ·
              unfold allIsolatedPins at hp_pins
              have h_p_valid := (List.mem_filter.mp hp_pins).1
              have h_layer : p.layer < s.layerCount :=
                  (allValid_any_iff_layer' s p).mp
                      (List.any_eq_true.mpr ⟨p, h_p_valid, BEq.rfl⟩)
              have h_any := (allValid_any_iff_layer' s (p.rotate180)).mpr h_layer
              rw [List.any_eq_true] at h_any
              obtain ⟨y, hy, hye⟩ := h_any
              have h_eq : y = p.rotate180 := eq_of_beq hye
              exact h_eq ▸ hy
            ·
              rw [getQuarter_rotate180]
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
            refine ⟨h_pin_r180, ?_⟩
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

/-- floatingUnits の各要素は少なくとも 1 つの位置を持つ -/
theorem floatingUnit_positions_nonempty (s : Shape) (u : FallingUnit)
        (hu : u ∈ floatingUnits s) :
        ∃ p, p ∈ u.positions := by
    rw [floatingUnits_eq_append, List.mem_append] at hu
    cases hu with
    | inl h_cluster =>
        rw [List.mem_map] at h_cluster
        obtain ⟨ps, hps_filtered, rfl⟩ := h_cluster
        -- ps ∈ allStructuralClustersList s → ps は structuralClusterList s pos
        -- structuralClusterList は seed を含む → 非空
        rw [List.mem_filter] at hps_filtered
        obtain ⟨pos, hps_eq, h_layer, _⟩ :=
            allStructuralClustersList_is_structuralClusterList s ps hps_filtered.1
        -- seed pos ∈ ps
        have h_seed : ps.any (· == pos) = true := by
            rw [hps_eq]
            exact structuralClusterList_complete s pos pos (by omega) GenericReachable.refl
        rw [List.any_eq_true] at h_seed
        obtain ⟨q, hq, _⟩ := h_seed
        exact ⟨q, hq⟩
    | inr h_pin =>
        rw [List.mem_map] at h_pin
        obtain ⟨p, _, rfl⟩ := h_pin
        -- .pin p の positions は [p]
        exact ⟨p, by simp only [FallingUnit.positions, List.mem_cons, List.not_mem_nil, or_false]⟩

/-- floatingUnits の異なる要素は位置が素であるため fallingUnitOrd の反対称性が成立する。
    位置が素 → canonicalKey に含まれる encodeQuarterPos が異なる → canonicalKey が不一致
    → listNatLe a.ck b.ck ∧ listNatLe b.ck a.ck が成立しない → fallingUnitOrd が反対称 -/
theorem fallingUnitOrd_antisymm_of_floatingUnits_impl (s : Shape)
        (a b : FallingUnit)
        (ha : a ∈ floatingUnits s) (hb : b ∈ floatingUnits s)
        (h_ab : fallingUnitOrd a b = true) (h_ba : fallingUnitOrd b a = true) :
        a = b := by
    by_contra h_ne
    -- fallingUnitOrd の定義展開
    unfold fallingUnitOrd at h_ab h_ba
    -- 分岐: 大半は false = true か矛盾する < 条件で閉じる
    split_ifs at h_ab h_ba <;>
        (first | exact absurd h_ab (by decide) | exact absurd h_ba (by decide) |
                 (exfalso; omega) | skip)
    -- 残: h_ab : listNatLe a.ck b.ck = true, h_ba : listNatLe b.ck a.ck = true
    have h_ck_eq := listNatLe_antisymm h_ab h_ba
    -- a, b は fU(s) の異なる要素 → 位置が素 (disjoint)
    obtain ⟨ia, hia, h_eq_ia⟩ := List.mem_iff_getElem.mp ha
    obtain ⟨ib, hib, h_eq_ib⟩ := List.mem_iff_getElem.mp hb
    have h_ne_idx : ia ≠ ib := by
        intro h_eq; subst h_eq; exact h_ne (h_eq_ia ▸ h_eq_ib ▸ rfl)
    -- subst せず h_eq_ia/h_eq_ib を rw で使う（subst すると a, b が消える）
    have ⟨p, hp⟩ := floatingUnit_positions_nonempty s a ha
    have hp_i : ((floatingUnits s)[ia]).positions.any (· == p) = true := by
        rw [h_eq_ia]; exact List.any_eq_true.mpr ⟨p, hp, BEq.rfl⟩
    have h_disj := floatingUnits_pairwise_disjoint s ia ib hia hib h_ne_idx p hp_i
    -- h_disj : ((floatingUnits s)[ib]).positions.any (· == p) = false
    -- → b にも p が属さない
    have h_not_in_b : ¬(p ∈ b.positions) := by
        intro h_mem
        have h_any : b.positions.any (· == p) = true :=
            List.any_eq_true.mpr ⟨p, h_mem, BEq.rfl⟩
        rw [← h_eq_ib] at h_any
        rw [h_any] at h_disj; exact absurd h_disj (by decide)
    -- canonicalKey 等価 → Finset 等価 → 矛盾
    unfold FallingUnit.canonicalKey at h_ck_eq
    have h_mem_a : encodeQuarterPos p ∈ (a.positions.map encodeQuarterPos).toFinset := by
        simp only [List.mem_toFinset, List.mem_map]
        exact ⟨p, hp, rfl⟩
    have h_not_mem_b : encodeQuarterPos p ∉ (b.positions.map encodeQuarterPos).toFinset := by
        simp only [List.mem_toFinset, List.mem_map]
        intro ⟨q, hq, h_enc⟩
        exact h_not_in_b (encodeQuarterPos_injective h_enc ▸ hq)
    have h_fs_eq : (a.positions.map encodeQuarterPos).toFinset =
            (b.positions.map encodeQuarterPos).toFinset := by
        have := congrArg List.toFinset h_ck_eq
        simp only [Finset.sort_toFinset] at this
        exact this
    rw [h_fs_eq] at h_mem_a
    exact absurd h_mem_a h_not_mem_b

/-- rotate180 後の positions の .any は元の .any と等価 -/
theorem any_positions_rotate180 (u : FallingUnit) (p : QuarterPos) :
        u.rotate180.positions.any (· == p.rotate180) = u.positions.any (· == p) := by
    rw [FallingUnit.positions_rotate180, any_map_rotate180_beq,
        QuarterPos.rotate180_rotate180]

/-- NoDup リスト間の注射的対応があれば長さ以下 -/
theorem length_le_of_injection {α β : Type} [DecidableEq β]
        (l1 : List α) (l2 : List β)
        (f : α → β)
        (h_mem : ∀ a ∈ l1, f a ∈ l2)
        (h_inj : ∀ a₁ ∈ l1, ∀ a₂ ∈ l1, f a₁ = f a₂ → a₁ = a₂)
        (h_nodup1 : l1.Nodup)
        (_h_nodup2 : l2.Nodup) :
        l1.length ≤ l2.length := by
    have h_map_nodup : (l1.map f).Nodup :=
        (List.nodup_map_iff_inj_on h_nodup1).mpr h_inj
    have h_map_sub : l1.map f ⊆ l2 := by
        intro x hx; rw [List.mem_map] at hx
        obtain ⟨a, ha, rfl⟩ := hx; exact h_mem a ha
    calc l1.length = (l1.map f).length := (List.length_map ..).symm
      _ ≤ l2.length := (List.subperm_of_subset h_map_nodup h_map_sub).length_le

/-- floatingUnits の長さは rotate180 で不変 -/
theorem floatingUnits_length_rotate180 (s : Shape) :
        (floatingUnits s).length = (floatingUnits s.rotate180).length := by
    -- 補助: s → s.r180 方向の |fU(s)| ≤ |fU(s.r180)|
    suffices h_le : ∀ (t : Shape),
            (floatingUnits t).length ≤ (floatingUnits t.rotate180).length by
        apply Nat.le_antisymm (h_le s)
        have h := h_le s.rotate180
        rw [Shape.rotate180_rotate180] at h; exact h
    intro t
    -- 各 u ∈ fU(t) に対応する v ∈ fU(t.r180) を choose で取る
    have hg_ex : ∀ u ∈ floatingUnits t,
            ∃ v ∈ floatingUnits t.rotate180,
                (∀ p, u.rotate180.positions.any (· == p) = v.positions.any (· == p))
                ∧ u.rotate180.typeOrd = v.typeOrd :=
        floatingUnit_any_in_rotate180 t
    -- 非依存型の写像を構築
    open Classical in
    let g : FallingUnit → FallingUnit :=
        fun u => if h : u ∈ floatingUnits t
            then (hg_ex u h).choose
            else u
    have hg_mem : ∀ u ∈ floatingUnits t, g u ∈ floatingUnits t.rotate180 := by
        intro u hu
        show (if h : u ∈ floatingUnits t then (hg_ex u h).choose else u) ∈ _
        rw [dif_pos hu]
        exact (hg_ex u hu).choose_spec.1
    have hg_any : ∀ u ∈ floatingUnits t, ∀ p : QuarterPos,
            u.rotate180.positions.any (· == p) = (g u).positions.any (· == p) := by
        intro u hu
        show ∀ p, u.rotate180.positions.any (· == p) =
            (if h : u ∈ floatingUnits t then (hg_ex u h).choose else u).positions.any (· == p)
        rw [dif_pos hu]
        exact (hg_ex u hu).choose_spec.2.1
    -- 注射性
    have hg_inj : ∀ u1 ∈ floatingUnits t, ∀ u2 ∈ floatingUnits t,
            g u1 = g u2 → u1 = u2 := by
        intro u1 hu1 u2 hu2 h_eq
        by_contra h_ne
        have ⟨p, hp⟩ := floatingUnit_positions_nonempty t u1 hu1
        have h1 : u1.rotate180.positions.any (· == p.rotate180) = true := by
            rw [any_positions_rotate180]; exact List.any_eq_true.mpr ⟨p, hp, BEq.rfl⟩
        have h2 : u2.rotate180.positions.any (· == p.rotate180) = true := by
            rw [hg_any u2 hu2, ← h_eq, ← hg_any u1 hu1]; exact h1
        rw [any_positions_rotate180] at h2
        obtain ⟨i, hi, h_eq_i⟩ := List.mem_iff_getElem.mp hu1
        obtain ⟨j, hj, h_eq_j⟩ := List.mem_iff_getElem.mp hu2
        subst h_eq_i; subst h_eq_j
        have h_ij : i ≠ j := fun h_eq_ij => h_ne (by subst h_eq_ij; rfl)
        exact absurd
            (by rw [List.any_eq_true] at h2 ⊢; exact h2 :
                ((floatingUnits t)[j]).positions.any (· == p) = true)
            (Bool.eq_false_iff.mp
                (floatingUnits_pairwise_disjoint t i j hi hj h_ij p
                    (List.any_eq_true.mpr ⟨p, hp, BEq.rfl⟩)))
    exact length_le_of_injection _ _ g hg_mem hg_inj (floatingUnits_nodup t) (floatingUnits_nodup t.rotate180)

/-- insertSorted は要素 u をソート済みリスト sorted の位置 k に挿入する形で分解できる:
    insertSorted u sorted fuel = sorted.take k ++ [u] ++ sorted.drop k
    （fuel ≥ sorted.length のとき）。
    結果として、sorted 内の既存要素の相対順序は保存される。 -/
theorem insertSorted_split (u : FallingUnit) (sorted : List FallingUnit)
        (fuel : Nat) (h_fuel : fuel ≥ sorted.length) :
        ∃ k, k ≤ sorted.length ∧
            insertSorted u sorted fuel = sorted.take k ++ [u] ++ sorted.drop k := by
    induction sorted, fuel using insertSorted.induct u with
    | case1 sorted =>
        -- fuel = 0 → u :: sorted, k = 0
        exact ⟨0, by omega, by simp only [insertSorted, List.take_zero, List.nil_append, List.drop_zero, List.cons_append]⟩
    | case2 =>
        -- sorted = [] → k = 0
        exact ⟨0, by omega, rfl⟩
    | case3 fuel v rest h_spb =>
        -- shouldProcessBefore(u, v) = true → u :: v :: rest, k = 0
        simp only [insertSorted, h_spb, ite_true]
        exact ⟨0, by omega, rfl⟩
    | case4 fuel v rest h_not_spb ih =>
        -- shouldProcessBefore(u, v) = false → v :: insertSorted u rest fuel
        simp only [insertSorted, h_not_spb]
        have h_fuel' : fuel ≥ rest.length := by
            simp only [List.length] at h_fuel; omega
        obtain ⟨k', hk', hk'_eq⟩ := ih h_fuel'
        exact ⟨k' + 1, by simp only [List.length]; omega,
            by simp only [Bool.false_eq_true, ↓reduceIte, hk'_eq, List.append_assoc, List.cons_append, List.nil_append, List.take_succ_cons, List.drop_succ_cons]⟩

-- ================================================================
-- バブルソート帰納法の基盤 (posIn, invCount, swap ヘルパー)
-- ================================================================

/-- 等価述語 (DecidableEq ベース) -/
def eqPred (x : FallingUnit) : FallingUnit → Bool := fun y => decide (y = x)

/-- eqPred x x = true (反射性) -/
theorem eqPred_self (x : FallingUnit) : eqPred x x = true := decide_eq_true rfl

/-- eqPred x y = true → y = x (等価性抽出) -/
theorem eq_of_eqPred (x y : FallingUnit) (h : eqPred x y = true) : y = x :=
    of_decide_eq_true h

/-- リスト中の要素 x の位置を返す (DecidableEq ベース) -/
def posIn (x : FallingUnit) (l : List FallingUnit) : Nat :=
    l.findIdx (eqPred x)

/-- posIn x l < l.length ← x ∈ l -/
theorem posIn_lt_length (x : FallingUnit) (l : List FallingUnit)
        (hx : x ∈ l) : posIn x l < l.length := by
    exact List.findIdx_lt_length_of_exists ⟨x, hx, eqPred_self x⟩

/-- posIn で取得した位置の要素は x に等しい -/
theorem getElem_posIn (x : FallingUnit) (l : List FallingUnit)
        (hx : x ∈ l) :
        l[posIn x l]'(posIn_lt_length x l hx) = x := by
    have h := posIn_lt_length x l hx
    have h_match : eqPred x (l[posIn x l]'h) = true :=
        @List.findIdx_getElem _ (eqPred x) l h
    exact eq_of_eqPred x _ h_match

/-- NoDup リスト上で posIn は単射 -/
theorem posIn_injective (l : List FallingUnit) (_h_nodup : l.Nodup)
        (x y : FallingUnit) (hx : x ∈ l) (hy : y ∈ l)
        (h_eq : posIn x l = posIn y l) : x = y := by
    have hx_get := getElem_posIn x l hx
    have hy_get := getElem_posIn y l hy
    have h_len_x := posIn_lt_length x l hx
    have h_len_y := posIn_lt_length y l hy
    calc x = l[posIn x l]'h_len_x := hx_get.symm
      _ = l[posIn y l]'h_len_y := by congr 1
      _ = y := hy_get

/-- NoDup リストにおいて posIn l[k] l = k -/
theorem posIn_getElem_self (l : List FallingUnit) (h_nodup : l.Nodup)
        (k : Nat) (hk : k < l.length) :
        posIn l[k] l = k := by
    unfold posIn
    rw [List.findIdx_eq hk]
    constructor
    · exact eqPred_self _
    · intro j hj
      have h_ne : l[j]'(Nat.lt_trans hj hk) ≠ l[k] := by
        intro h_eq
        exact absurd (h_nodup.getElem_inj_iff.mp h_eq) (by omega)
      simp only [eqPred, h_ne, decide_false]

/-- リスト l1 の l2 に対する反転数: l1[i], l1[j] (i<j) で l2 内位置が反転するペアの数 -/
def invCount (l1 l2 : List FallingUnit) : Nat :=
    let pairs := do
        let i ← List.range l1.length
        let j ← List.range l1.length
        if i < j then pure (i, j) else []
    pairs.foldl (fun acc (i, j) =>
        if h₁ : i < l1.length then
            if h₂ : j < l1.length then
                if posIn l1[i] l2 > posIn l1[j] l2 then acc + 1 else acc
            else acc
        else acc
    ) 0

/-- foldl で条件付き加算した結果は非負・単調非減少 -/
theorem foldl_cond_add_ge_init {α : Type*} (l : List α) (p : α → Bool) (init : Nat) :
        l.foldl (fun acc x => if p x then acc + 1 else acc) init ≥ init := by
    induction l generalizing init with
    | nil => simp only [List.foldl, ge_iff_le, Std.le_refl]
    | cons hd tl ih =>
      simp only [List.foldl]
      by_cases hp : p hd = true
      · simp only [hp, ite_true]
        have := ih (init + 1)
        omega
      · simp only [Bool.eq_false_iff.mpr (by simpa using hp)]
        exact ih init

/-- foldl 条件付き加算 = 0 → リストの全要素が条件を満たさない -/
theorem foldl_cond_add_zero {α : Type*} (l : List α) (p : α → Bool) :
        l.foldl (fun acc x => if p x then acc + 1 else acc) 0 = 0 →
        ∀ x ∈ l, p x = false := by
    induction l with
    | nil => simp only [List.foldl_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
    | cons hd tl ih =>
      simp only [List.foldl]
      intro h_fold
      by_cases hp : p hd = true
      · simp only [hp, ite_true] at h_fold
        have h_ge := foldl_cond_add_ge_init tl p 1
        simp only [Nat.zero_add] at h_fold
        omega
      · have hp_false : p hd = false := by simpa using hp
        simp only [hp_false] at h_fold
        intro x hx
        cases hx with
        | head => exact hp_false
        | tail _ hx => exact ih h_fold x hx

/-- 単調非減少関数の foldl は init 以上 -/
theorem foldl_mono_ge_init {α : Type*} (l : List α) (f : Nat → α → Nat) (init : Nat)
        (h_mono : ∀ acc x, f acc x ≥ acc) :
        l.foldl f init ≥ init := by
    induction l generalizing init with
    | nil => simp only [List.foldl, ge_iff_le, Std.le_refl]
    | cons hd tl ih =>
      simp only [List.foldl]
      have h1 := h_mono init hd
      have h2 := ih (f init hd)
      omega

/-- 単調非減少 foldl = 0 → 全要素で f 0 x = 0 (帰納法) -/
theorem foldl_mono_all_zero {α : Type*} (l : List α) (f : Nat → α → Nat)
        (h_all : ∀ x ∈ l, f 0 x = 0) :
        l.foldl f 0 = 0 := by
    induction l with
    | nil => simp only [List.foldl]
    | cons x xs ih =>
      simp only [List.foldl]
      have h_f0 : f 0 x = 0 := h_all x List.mem_cons_self
      rw [h_f0]
      exact ih (fun y hy => h_all y (List.mem_cons_of_mem x hy))

/-- foldl の init 単調性 -/
theorem foldl_mono_le_init {β : Type*} (l : List β) (f : Nat → β → Nat)
        (a b : Nat) (h_le : a ≤ b)
        (h_mono_le : ∀ acc₁ acc₂ y, acc₁ ≤ acc₂ → f acc₁ y ≤ f acc₂ y) :
        l.foldl f a ≤ l.foldl f b := by
    induction l generalizing a b with
    | nil => simp only [List.foldl]; exact h_le
    | cons hd tl ih =>
      simp only [List.foldl]
      exact ih (f a hd) (f b hd) (h_mono_le a b hd h_le)

/-- 単調 foldl で member が 1 以上寄与 → foldl ≥ 1 -/
theorem foldl_mono_ge_of_mem {β : Type*} (l : List β) (f : Nat → β → Nat) (x : β)
        (h_mono : ∀ acc y, f acc y ≥ acc)
        (h_mono_le : ∀ acc₁ acc₂ y, acc₁ ≤ acc₂ → f acc₁ y ≤ f acc₂ y)
        (h_mem : x ∈ l) (h_pos : f 0 x ≥ 1) :
        l.foldl f 0 ≥ 1 := by
    induction l with
    | nil => simp only [List.not_mem_nil] at h_mem
    | cons hd tl ih =>
      simp only [List.foldl]
      cases h_mem with
      | head =>
        have h1 := foldl_mono_ge_init tl f (f 0 x) h_mono
        omega
      | tail _ hx =>
        have ih_result := ih hx
        calc 1 ≤ tl.foldl f 0 := ih_result
          _ ≤ tl.foldl f (f 0 hd) := foldl_mono_le_init tl f 0 (f 0 hd) (by omega) h_mono_le

/-- invCount = 0 → 全ペア (i, j) (i < j) で反転なし -/
theorem invCount_zero_no_inv (l1 l2 : List FallingUnit)
        (h_inv : invCount l1 l2 = 0)
        (i j : Nat) (h_lt : i < j) (hi : i < l1.length) (hj : j < l1.length) :
        ¬(posIn l1[i] l2 > posIn l1[j] l2) := by
    intro h_pos
    simp only [invCount] at h_inv
    set f : Nat → Nat × Nat → Nat := fun acc ij =>
        if h₁ : ij.1 < l1.length then
            if h₂ : ij.2 < l1.length then
                if posIn l1[ij.1] l2 > posIn l1[ij.2] l2 then acc + 1 else acc
            else acc
        else acc
    have h_f_pos : f 0 (i, j) ≥ 1 := by
        show (if h₁ : i < l1.length then
            if h₂ : j < l1.length then
                if posIn l1[i] l2 > posIn l1[j] l2 then 0 + 1 else 0
            else 0
         else 0) ≥ 1
        simp only [hi, dite_true, hj, h_pos, ite_true]
        omega
    have h_mem : (i, j) ∈ (do
        let i ← List.range l1.length
        let j ← List.range l1.length
        if i < j then pure (i, j) else [] : List (Nat × Nat)) := by
        show (i, j) ∈ (List.range l1.length).flatMap fun a =>
            (List.range l1.length).flatMap fun b =>
                if a < b then [(a, b)] else []
        rw [List.mem_flatMap]
        refine ⟨i, List.mem_range.mpr hi, ?_⟩
        rw [List.mem_flatMap]
        refine ⟨j, List.mem_range.mpr hj, ?_⟩
        rw [if_pos h_lt]
        exact List.Mem.head _
    have h_mono : ∀ acc (y : Nat × Nat), f acc y ≥ acc := by
        intro acc y
        show (if h₁ : y.1 < l1.length then _ else acc) ≥ acc
        split
        · split
          · split <;> omega
          · omega
        · omega
    have h_mono_le : ∀ acc₁ acc₂ (y : Nat × Nat), acc₁ ≤ acc₂ → f acc₁ y ≤ f acc₂ y := by
        intro a1 a2 y h_le
        show (if h₁ : y.1 < l1.length then _ else a1) ≤ (if h₁ : y.1 < l1.length then _ else a2)
        split
        · rename_i h1
          show (if h₂ : y.2 < l1.length then _ else a1) ≤ (if h₂ : y.2 < l1.length then _ else a2)
          split
          · rename_i h2
            show (if posIn l1[y.1] l2 > posIn l1[y.2] l2 then a1 + 1 else a1) ≤
                 (if posIn l1[y.1] l2 > posIn l1[y.2] l2 then a2 + 1 else a2)
            split <;> omega
          · exact h_le
        · exact h_le
    have h_ge := foldl_mono_ge_of_mem _ f (i, j) h_mono h_mono_le h_mem h_f_pos
    omega

/-- NoDup 置換リストで反転数 0 → リスト一致 -/
theorem invCount_zero_imp_eq (l1 l2 : List FallingUnit)
        (h_perm : l1.Perm l2) (h_nodup : l1.Nodup) (h_inv : invCount l1 l2 = 0) :
        l1 = l2 := by
    have h_len := h_perm.length_eq
    have h_nodup2 : l2.Nodup := h_perm.nodup_iff.mp h_nodup
    apply List.ext_getElem h_len
    intro k hk1 hk2
    suffices h_posIn_eq : ∀ (m : Nat) (hm : m < l1.length), posIn (l1[m]'hm) l2 = m by
        have h_mem : l1[k] ∈ l2 := h_perm.mem_iff.mp (List.getElem_mem hk1)
        have h_get := getElem_posIn l1[k] l2 h_mem
        simp only [h_posIn_eq k hk1] at h_get
        exact h_get.symm
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
    intro hm
    have h_mem_m : l1[m] ∈ l2 := h_perm.mem_iff.mp (List.getElem_mem hm)
    have h_pos_lt : posIn l1[m] l2 < l2.length := posIn_lt_length l1[m] l2 h_mem_m
    have h_pos_lt1 : posIn l1[m] l2 < l1.length := by omega
    have h_ge : posIn l1[m] l2 ≥ m := by
        by_contra h_lt_m
        simp only [Nat.not_le] at h_lt_m
        have h_pm := ih (posIn l1[m] l2) h_lt_m h_pos_lt1
        have h_same := posIn_injective l2 h_nodup2
            (l1[posIn l1[m] l2]'h_pos_lt1) (l1[m])
            (h_perm.mem_iff.mp (List.getElem_mem h_pos_lt1))
            h_mem_m
            h_pm
        have := h_nodup.getElem_inj_iff (hi := h_pos_lt1) (hj := hm) |>.mp h_same
        omega
    by_contra h_ne
    have h_gt : posIn l1[m] l2 > m := by omega
    have h_l2m_mem : l2[m]'(by omega) ∈ l1 :=
        h_perm.mem_iff.mpr (List.getElem_mem (by omega))
    obtain ⟨m', hm'_lt, hm'_eq⟩ := List.getElem_of_mem h_l2m_mem
    have h_posIn_m' : posIn l1[m'] l2 = m := by
        rw [hm'_eq]; exact posIn_getElem_self l2 h_nodup2 m (by omega)
    have h_m'_ge_m : m' ≥ m := by
        by_contra h_m'_lt
        simp only [Nat.not_le] at h_m'_lt
        have := ih m' h_m'_lt (by omega)
        omega
    have h_m'_ne_m : m' ≠ m := by
        intro h_eq; subst h_eq
        exact absurd h_posIn_m' h_ne
    exact invCount_zero_no_inv l1 l2 h_inv m m' (by omega) hm (by omega) (by omega)

/-- 単調 foldl > 0 → 寄与する要素が存在する -/
theorem foldl_mono_pos_exists {α : Type*} (l : List α) (f : Nat → α → Nat)
        (_h_mono : ∀ acc x, f acc x ≥ acc)
        (_h_mono_add : ∀ acc₁ acc₂ x, acc₁ ≤ acc₂ → f acc₁ x ≤ f acc₂ x)
        (h_pos : l.foldl f 0 > 0) :
        ∃ x ∈ l, f 0 x > 0 := by
    by_contra h_all
    push Not at h_all
    have h_all' : ∀ x ∈ l, f 0 x = 0 := fun x hx => by have := h_all x hx; omega
    have h_fold_zero := foldl_mono_all_zero l f h_all'
    omega

/-- invCount > 0 → 反転ペアが存在する -/
theorem exists_inv_of_invCount_pos (l1 l2 : List FallingUnit)
        (h_inv_pos : invCount l1 l2 > 0) :
        ∃ (i j : Nat) (hi : i < l1.length) (hj : j < l1.length),
            i < j ∧ posIn (l1[i]'hi) l2 > posIn (l1[j]'hj) l2 := by
    simp only [invCount] at h_inv_pos
    set f : Nat → Nat × Nat → Nat := fun acc ij =>
        if h₁ : ij.1 < l1.length then
            if h₂ : ij.2 < l1.length then
                if posIn l1[ij.1] l2 > posIn l1[ij.2] l2 then acc + 1 else acc
            else acc
        else acc
    have h_mono : ∀ acc (y : Nat × Nat), f acc y ≥ acc := by
        intro acc y; simp only [f]
        split <;> [split <;> [split <;> omega; omega]; omega]
    have h_mono_add : ∀ acc₁ acc₂ (y : Nat × Nat), acc₁ ≤ acc₂ → f acc₁ y ≤ f acc₂ y := by
        intro a1 a2 y h_le; simp only [f]
        split <;> [split <;> [split <;> omega; omega]; omega]
    obtain ⟨⟨i, j⟩, h_mem, h_f_pos⟩ := foldl_mono_pos_exists _ f h_mono h_mono_add h_inv_pos
    have h_f_val : f 0 (i, j) > 0 := h_f_pos
    simp only [f] at h_f_val
    split at h_f_val
    · rename_i h1
      split at h_f_val
      · rename_i h2
        split at h_f_val
        · rename_i h_inv
          have h_ij_lt : i < j := by
            have h_flat : (i, j) ∈ (List.range l1.length).flatMap fun a =>
                (List.range l1.length).flatMap fun b =>
                    if a < b then [(a, b)] else [] := by
              exact h_mem
            rw [List.mem_flatMap] at h_flat
            obtain ⟨a, _, ha⟩ := h_flat
            rw [List.mem_flatMap] at ha
            obtain ⟨b, _, hb⟩ := ha
            split at hb
            · rename_i h_lt; simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hb; omega
            · simp only [List.not_mem_nil] at hb
          exact ⟨i, j, h1, h2, h_ij_lt, h_inv⟩
        · omega
      · omega
    · omega

/-- 反転ペアが存在 → 隣接反転ペアが存在する -/
theorem exists_adj_inv_of_exists_inv (l1 l2 : List FallingUnit)
        (i j : Nat) (h_lt : i < j) (hi : i < l1.length) (hj : j < l1.length)
        (h_inv : posIn (l1[i]'hi) l2 > posIn (l1[j]'hj) l2) :
        ∃ (k : Nat) (hk : k + 1 < l1.length),
            posIn (l1[k]'(by omega)) l2 > posIn (l1[k + 1]'hk) l2 := by
    suffices h_suff : ∀ (gap : Nat) (i j : Nat) (h_lt : i < j) (hi : i < l1.length)
        (hj : j < l1.length) (h_gap : gap = j - i)
        (h_inv : posIn (l1[i]'hi) l2 > posIn (l1[j]'hj) l2),
        ∃ (k : Nat) (hk : k + 1 < l1.length),
            posIn (l1[k]'(by omega)) l2 > posIn (l1[k + 1]'hk) l2 by
        exact h_suff (j - i) i j h_lt hi hj rfl h_inv
    intro gap
    induction gap using Nat.strongRecOn with
    | ind gap ih =>
    intro i j h_lt hi hj h_gap h_inv
    by_cases h_adj : j = i + 1
    · exact ⟨i, by omega, by subst h_adj; exact h_inv⟩
    · by_cases h_mid : posIn (l1[i]'hi) l2 > posIn (l1[i + 1]'(by omega)) l2
      · exact ⟨i, by omega, h_mid⟩
      · have h_inv' : posIn (l1[i + 1]'(by omega)) l2 > posIn (l1[j]'hj) l2 := by omega
        exact ih (j - (i + 1)) (by omega) (i + 1) j (by omega) (by omega) hj rfl h_inv'

-- ================================================================
-- invCount_adj_swap_lt の証明のためのヘルパー群
-- ================================================================

-- 位置 k と k+1 の置換
def swapIndex (k m : Nat) : Nat :=
    if m = k then k + 1 else if m = k + 1 then k else m

theorem swapIndex_invol (k m : Nat) : swapIndex k (swapIndex k m) = m := by
    simp only [swapIndex]
    split
    · split
      · omega
      · split <;> omega
    · split
      · split <;> omega
      · rfl

theorem swapIndex_lt_of_lt (k m n : Nat) (hk : k + 1 < n) (hm : m < n) : swapIndex k m < n := by
    unfold swapIndex; split
    · omega
    · split <;> omega

theorem swapIndex_preserves_lt (k : Nat) {i j : Nat} (h_lt : i < j)
        (h_ne : (i, j) ≠ (k, k + 1)) : swapIndex k i < swapIndex k j := by
    unfold swapIndex
    by_cases hi_k : i = k <;> by_cases hi_k1 : i = k + 1 <;>
        by_cases hj_k : j = k <;> by_cases hj_k1 : j = k + 1 <;>
        simp_all only [lt_self_iff_false, Nat.lt_add_one, ne_eq, not_true_eq_false, Prod.mk.injEq, and_false, not_false_eq_true, Nat.add_eq_left, one_ne_zero, Nat.left_eq_add, ↓reduceIte, and_self, and_true] <;> omega

theorem swapIndex_pair_ne (k : Nat) {i j : Nat} (h_lt : i < j)
        (_h_ne : (i, j) ≠ (k, k + 1)) : (swapIndex k i, swapIndex k j) ≠ (k, k + 1) := by
    intro h_eq
    have h1 := congr_arg Prod.fst h_eq
    have h2 := congr_arg Prod.snd h_eq
    simp only at h1 h2
    have hi_eq : i = k + 1 := by
        have := swapIndex_invol k i; rw [h1] at this
        simp only [swapIndex, ite_true] at this; exact this.symm
    have hj_eq : j = k := by
        have := swapIndex_invol k j; rw [h2] at this
        simp only [swapIndex, show ¬(k + 1 = k) from by omega, ite_false, ite_true] at this
        exact this.symm
    omega

-- pairsList: (i,j) ペアのリスト (i < j < n)
def pairsList (n : Nat) : List (Nat × Nat) :=
    (List.range n).flatMap fun i =>
        (List.range n).flatMap fun j =>
            if i < j then [(i, j)] else []

theorem mem_pairsList {n : Nat} {p : Nat × Nat} :
        p ∈ pairsList n ↔ p.1 < n ∧ p.2 < n ∧ p.1 < p.2 := by
    constructor
    · intro hp
      simp only [pairsList, List.mem_flatMap, List.mem_range] at hp
      obtain ⟨a, ha, b, hb, h3⟩ := hp
      by_cases hab : a < b
      · simp only [hab, ite_true, List.mem_singleton] at h3
        obtain ⟨h_fst, h_snd⟩ := Prod.mk.inj h3
        exact ⟨h_fst ▸ ha, h_snd ▸ hb, h_fst ▸ h_snd ▸ hab⟩
      · simp only [hab, ite_false, List.not_mem_nil] at h3
    · rintro ⟨h1, h2, h_lt⟩
      show p ∈ (List.range n).flatMap _
      rw [List.mem_flatMap]
      refine ⟨p.1, List.mem_range.mpr h1, ?_⟩
      rw [List.mem_flatMap]
      refine ⟨p.2, List.mem_range.mpr h2, ?_⟩
      simp only [h_lt, ↓reduceIte, Prod.mk.eta, List.mem_cons, List.not_mem_nil, or_false]

theorem pairsList_nodup (n : Nat) : (pairsList n).Nodup := by
    simp only [pairsList]
    refine List.nodup_flatMap.mpr ⟨?_, ?_⟩
    · intro i _
      refine List.nodup_flatMap.mpr ⟨?_, ?_⟩
      · intro j _
        by_cases hij : i < j
        · simp only [hij, ite_true]; exact List.nodup_singleton _
        · simp only [hij, ite_false]; exact List.nodup_nil
      · exact List.nodup_range.pairwise_of_forall_ne (fun j1 hj1 j2 hj2 hne => by
          simp only [Function.onFun, List.disjoint_left]
          intro a ha1 ha2
          by_cases h1 : i < j1 <;> by_cases h2 : i < j2
          · simp only [h1, ite_true, List.mem_singleton] at ha1
            simp only [h2, ite_true, List.mem_singleton] at ha2
            exact absurd (by rw [ha1] at ha2; exact (Prod.mk.inj ha2).2) hne
          · simp only [h2, ite_false, List.not_mem_nil] at ha2
          · simp only [h1, ite_false, List.not_mem_nil] at ha1
          · simp only [h1, ite_false, List.not_mem_nil] at ha1)
    · exact List.nodup_range.pairwise_of_forall_ne (fun i1 hi1 i2 hi2 hne => by
        simp only [Function.onFun, List.disjoint_left]
        intro a ha1 ha2
        simp only [List.mem_flatMap, List.mem_range] at ha1 ha2
        obtain ⟨j1, _, hj1⟩ := ha1
        obtain ⟨j2, _, hj2⟩ := ha2
        by_cases h1 : i1 < j1 <;> by_cases h2 : i2 < j2
        · simp only [h1, ite_true, List.mem_singleton] at hj1
          simp only [h2, ite_true, List.mem_singleton] at hj2
          exact absurd (by rw [hj1] at hj2; exact (Prod.mk.inj hj2).1) hne
        · simp only [h2, ite_false, List.not_mem_nil] at hj2
        · simp only [h1, ite_false, List.not_mem_nil] at hj1
        · simp only [h1, ite_false, List.not_mem_nil] at hj1)

-- σ をペアに適用
def swapPair (k : Nat) (p : Nat × Nat) : Nat × Nat := (swapIndex k p.1, swapIndex k p.2)

theorem swapPair_invol (k : Nat) (p : Nat × Nat) : swapPair k (swapPair k p) = p := by
    simp only [swapPair, swapIndex_invol]

theorem swapPair_injective (k : Nat) : Function.Injective (swapPair k) := by
    intro a b h
    have := congr_arg (swapPair k) h
    rwa [swapPair_invol, swapPair_invol] at this

-- foldl ヘルパー
theorem rc_add_f_ic (f : Nat × Nat → Nat) :
        RightCommutative (fun (acc : Nat) (a : Nat × Nat) => acc + f a) :=
    ⟨fun a b c => by omega⟩

theorem foldl_add_init_ic (l : List (Nat × Nat)) (f : Nat × Nat → Nat) (init : Nat) :
        l.foldl (fun acc a => acc + f a) init =
        init + l.foldl (fun acc a => acc + f a) 0 := by
    induction l generalizing init with
    | nil => simp only [List.foldl, Nat.add_zero]
    | cons x xs ih =>
        simp only [List.foldl]
        rw [ih (init + f x), ih (0 + f x)]
        omega

theorem foldl_add_extract_ic (l : List (Nat × Nat)) (f : Nat × Nat → Nat)
        (x : Nat × Nat) (hx : x ∈ l) (_hnd : l.Nodup) :
        l.foldl (fun acc a => acc + f a) 0 =
        f x + (l.erase x).foldl (fun acc a => acc + f a) 0 := by
    have hperm := List.perm_cons_erase hx
    rw [hperm.foldl_eq (rcomm := rc_add_f_ic f) 0]
    simp only [List.foldl, Nat.zero_add]
    exact foldl_add_init_ic _ f (f x)

theorem pairFoldl_split_ic (n k : Nat) (v : Nat × Nat → Nat)
        (hk : k + 1 < n) :
        (pairsList n).foldl (fun acc p => acc + v p) 0 = v (k, k + 1) +
        ((pairsList n).erase (k, k + 1)).foldl (fun acc p => acc + v p) 0 :=
    foldl_add_extract_ic (pairsList n) v (k, k + 1)
        (mem_pairsList.mpr ⟨by omega, hk, by omega⟩) (pairsList_nodup n)

theorem mem_erase_nodup_ic {l : List (Nat × Nat)} {a x : Nat × Nat}
        (hnd : l.Nodup) (h : x ∈ l.erase a) : x ∈ l ∧ x ≠ a :=
    ⟨List.mem_of_mem_erase h, fun heq => by subst heq; exact hnd.not_mem_erase h⟩

theorem foldl_σ_reindex_ic (n k : Nat) (v : Nat × Nat → Nat) (hk : k + 1 < n) :
        ((pairsList n).erase (k, k + 1)).foldl (fun acc p => acc + v (swapPair k p)) 0 =
        ((pairsList n).erase (k, k + 1)).foldl (fun acc p => acc + v p) 0 := by
    have hnd := pairsList_nodup n
    have h_nodup_erase := hnd.erase (k, k + 1)
    have h_map_nodup := List.Nodup.map (swapPair_injective k) h_nodup_erase
    have h_perm : ((pairsList n).erase (k, k + 1)).map (swapPair k) |>.Perm
            ((pairsList n).erase (k, k + 1)) := by
        rw [List.perm_ext_iff_of_nodup h_map_nodup h_nodup_erase]
        intro x
        simp only [List.mem_map]
        constructor
        · rintro ⟨a, ha_mem, ha_eq⟩
          rw [← ha_eq]
          have ⟨ha_in, ha_ne⟩ := mem_erase_nodup_ic hnd ha_mem
          rw [mem_pairsList] at ha_in
          exact (List.mem_erase_of_ne (swapIndex_pair_ne k ha_in.2.2 ha_ne)).mpr
              (mem_pairsList.mpr ⟨swapIndex_lt_of_lt k a.1 n hk ha_in.1,
                   swapIndex_lt_of_lt k a.2 n hk ha_in.2.1,
                   swapIndex_preserves_lt k ha_in.2.2 ha_ne⟩)
        · intro hx_mem
          have ⟨hx_in, hx_ne⟩ := mem_erase_nodup_ic hnd hx_mem
          rw [mem_pairsList] at hx_in
          refine ⟨swapPair k x, ?_, swapPair_invol k x⟩
          apply (List.mem_erase_of_ne ?_).mpr
          · rw [mem_pairsList]; simp only [swapPair]
            exact ⟨swapIndex_lt_of_lt k x.1 n hk hx_in.1,
                   swapIndex_lt_of_lt k x.2 n hk hx_in.2.1,
                   swapIndex_preserves_lt k hx_in.2.2 hx_ne⟩
          · intro h_eq
            have h_inv := swapPair_invol k x
            rw [h_eq] at h_inv
            simp only [swapPair, swapIndex, ite_true, show ¬(k + 1 = k) from by omega, ite_false] at h_inv
            have := hx_in.2.2
            rw [← h_inv] at this
            simp only at this; omega
    set erase_list := (pairsList n).erase (k, k + 1)
    have h_eq : erase_list.foldl (fun acc p => acc + v (swapPair k p)) 0 =
        (erase_list.map (swapPair k)).foldl (fun acc p => acc + v p) 0 :=
        (List.foldl_map (f := swapPair k) (g := fun acc p => acc + v p)).symm
    rw [h_eq]
    exact h_perm.foldl_eq (rcomm := rc_add_f_ic v) 0

theorem foldl_add_congr_ic (l : List (Nat × Nat)) (f g : Nat × Nat → Nat)
        (h : ∀ x ∈ l, f x = g x) :
        l.foldl (fun acc p => acc + f p) 0 = l.foldl (fun acc p => acc + g p) 0 := by
    induction l with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.foldl]
        have h_eq := h x List.mem_cons_self
        rw [h_eq]
        rw [foldl_add_init_ic xs f (0 + g x), foldl_add_init_ic xs g (0 + g x)]
        congr 1
        exact ih (fun y hy => h y (List.mem_cons_of_mem x hy))

theorem pairFoldl_decrease_ic (n k : Nat) (v v' : Nat × Nat → Nat)
        (hk : k + 1 < n)
        (h_old_kk : v (k, k + 1) ≥ 1)
        (h_new_kk : v' (k, k + 1) = 0)
        (h_other : ∀ p ∈ (pairsList n).erase (k, k + 1),
            v' p = v (swapPair k p)) :
        (pairsList n).foldl (fun acc p => acc + v' p) 0 <
        (pairsList n).foldl (fun acc p => acc + v p) 0 := by
    rw [pairFoldl_split_ic n k v hk, pairFoldl_split_ic n k v' hk]
    rw [h_new_kk]; simp only [Nat.zero_add]
    have h_erase_eq : ((pairsList n).erase (k, k + 1)).foldl (fun acc p => acc + v' p) 0 =
        ((pairsList n).erase (k, k + 1)).foldl (fun acc p => acc + v (swapPair k p)) 0 :=
        foldl_add_congr_ic _ _ _ h_other
    rw [h_erase_eq, foldl_σ_reindex_ic n k v hk]
    omega

-- ================================================================
-- swap ヘルパー (getElem_swap 系)
-- ================================================================

-- swap list の長さ保存
theorem swap_length_ic (l : List FallingUnit) (k : Nat) (hk : k + 1 < l.length) :
        (l.take k ++ l[k + 1]'hk :: l[k]'(by omega) :: l.drop (k + 2)).length =
        l.length := by
    simp only [List.length_append, List.length_take, List.length_cons, List.length_drop]
    omega

-- getElem_swap: m < k
theorem getElem_swap_lt_ic (l : List FallingUnit) (k m : Nat)
        (hk : k + 1 < l.length) (hm : m < l.length) (h : m < k) :
        (l.take k ++ l[k + 1]'hk :: l[k]'(by omega) :: l.drop (k + 2))[m]'(by
            rw [swap_length_ic]; exact hm) =
        l[m]'hm := by
    have h_take_bound : m < (l.take k).length := by
        rw [List.length_take_of_le (by omega)]; exact h
    simp only [List.getElem_append_left h_take_bound, List.getElem_take]

-- getElem_swap: m = k → l[k+1]
theorem getElem_swap_eq_ic (l : List FallingUnit) (k : Nat)
        (hk : k + 1 < l.length) :
        (l.take k ++ l[k + 1]'hk :: l[k]'(by omega) :: l.drop (k + 2))[k]'(by
            rw [swap_length_ic]; omega) =
        l[k + 1]'hk := by
    have h_tk : (l.take k).length = k := List.length_take_of_le (by omega)
    have h_ge : (l.take k).length ≤ k := by omega
    rw [List.getElem_append_right h_ge]
    simp only [h_tk, Nat.sub_self]
    rfl

-- getElem_swap: m = k+1 → l[k]
theorem getElem_swap_eq_succ_ic (l : List FallingUnit) (k : Nat)
        (hk : k + 1 < l.length) :
        (l.take k ++ l[k + 1]'hk :: l[k]'(by omega) :: l.drop (k + 2))[k + 1]'(by
            rw [swap_length_ic]; exact hk) =
        l[k]'(by omega) := by
    have h_tk : (l.take k).length = k := List.length_take_of_le (by omega)
    have h_ge : (l.take k).length ≤ k + 1 := by omega
    rw [List.getElem_append_right h_ge]
    simp only [h_tk, show k + 1 - k = 1 from by omega]
    rfl

-- getElem_swap: m > k+1 → l[m]
theorem getElem_swap_gt_ic (l : List FallingUnit) (k m : Nat)
        (hk : k + 1 < l.length) (hm : m < l.length) (h : m > k + 1) :
        (l.take k ++ l[k + 1]'hk :: l[k]'(by omega) :: l.drop (k + 2))[m]'(by
            rw [swap_length_ic]; exact hm) =
        l[m]'hm := by
    rw [List.getElem_append]
    have h_not_lt : ¬(m < (List.take k l).length) := by
        rw [List.length_take_of_le (by omega)]; omega
    simp only [h_not_lt, dite_false]
    set len := (List.take k l).length
    have hlen_eq : len = k := List.length_take_of_le (by omega)
    rw [List.getElem_cons]; split; · omega
    rw [List.getElem_cons]; split; · omega
    rw [List.getElem_drop]; congr 1; omega

-- invContrib: ペア (i,j) の反転数への寄与
def invContrib_ic (l1 l2 : List FallingUnit) (p : Nat × Nat) : Nat :=
    if h₁ : p.1 < l1.length then
        if h₂ : p.2 < l1.length then
            if posIn l1[p.1] l2 > posIn l1[p.2] l2 then 1 else 0
        else 0
    else 0

-- invCount = pairsList(n).foldl(+invContrib)
theorem invCount_eq_pairsFoldl (l1 l2 : List FallingUnit) :
        invCount l1 l2 =
        (pairsList l1.length).foldl (fun acc p => acc + invContrib_ic l1 l2 p) 0 := by
    unfold invCount
    suffices ∀ (init : Nat) (l : List (Nat × Nat)),
        l.foldl (fun acc (ij : Nat × Nat) =>
            if h₁ : ij.1 < l1.length then
                if h₂ : ij.2 < l1.length then
                    if posIn l1[ij.1] l2 > posIn l1[ij.2] l2 then acc + 1 else acc
                else acc
            else acc) init = l.foldl (fun acc p => acc + invContrib_ic l1 l2 p) init from
        this 0 _
    intro init l
    induction l generalizing init with
    | nil => rfl
    | cons p ps ih =>
        simp only [List.foldl]
        have h_eq : (if h₁ : p.1 < l1.length then
            if h₂ : p.2 < l1.length then
                if posIn l1[p.1] l2 > posIn l1[p.2] l2 then init + 1 else init
            else init
         else init) = init + invContrib_ic l1 l2 p := by
            simp only [invContrib_ic]
            split
            · split
              · split <;> omega
              · omega
            · omega
        rw [h_eq]
        exact ih _

-- getElem_swap: swapIndex で統合
theorem getElem_swap_swapIndex (l : List FallingUnit) (k m : Nat)
        (hk : k + 1 < l.length) (hm : m < l.length) :
        (l.take k ++ l[k + 1]'hk :: l[k]'(by omega) :: l.drop (k + 2))[m]'(by
            rw [swap_length_ic]; exact hm) =
        l[swapIndex k m]'(swapIndex_lt_of_lt k m l.length hk hm) := by
    by_cases h1 : m < k
    · have hσ : swapIndex k m = m := by
          simp only [swapIndex, show m ≠ k from by omega, ↓reduceIte, show m ≠ k + 1 from by omega]
      simp only [hσ]; exact getElem_swap_lt_ic l k m hk hm h1
    · by_cases h2 : m = k
      · have hσ : swapIndex k m = k + 1 := by simp only [swapIndex, h2, ↓reduceIte]
        simp only [hσ]
        have := getElem_swap_eq_ic l k hk
        exact h2 ▸ this
      · by_cases h3 : m = k + 1
        · have hσ : swapIndex k m = k := by
              simp only [swapIndex, h3, Nat.add_eq_left, one_ne_zero, ↓reduceIte]
          simp only [hσ]
          have := getElem_swap_eq_succ_ic l k hk
          exact h3 ▸ this
        · have hσ : swapIndex k m = m := by
              simp only [swapIndex, show m ≠ k from h2, ↓reduceIte, show m ≠ k + 1 from h3]
          simp only [hσ]; exact getElem_swap_gt_ic l k m hk hm (by omega)

/-- 核心: 隣接反転 swap で invCount が厳密に減少する -/
theorem invCount_adj_swap_lt (l1 l2 : List FallingUnit)
        (_h_perm : l1.Perm l2) (_h_nodup : l1.Nodup)
        (k : Nat) (hk : k + 1 < l1.length)
        (h_inv_k : posIn (l1[k]'(by omega)) l2 > posIn (l1[k + 1]'hk) l2) :
        invCount (l1.take k ++ l1[k + 1]'hk :: l1[k]'(by omega) :: l1.drop (k + 2)) l2 <
            invCount l1 l2 := by
    set l1' := l1.take k ++ l1[k + 1]'hk :: l1[k]'(by omega) :: l1.drop (k + 2)
    set n := l1.length
    have hl1'_len : l1'.length = n := swap_length_ic l1 k hk
    rw [invCount_eq_pairsFoldl l1 l2, invCount_eq_pairsFoldl l1' l2]
    rw [hl1'_len]
    apply pairFoldl_decrease_ic n k (invContrib_ic l1 l2) (invContrib_ic l1' l2) hk
    · simp only [invContrib_ic, show k < l1.length from by omega, dite_true,
                  show k + 1 < l1.length from hk]
      split
      · omega
      · omega
    · have h_eq_k : l1'[k]'(by omega) = l1[k + 1]'hk :=
          getElem_swap_eq_ic l1 k hk
      have h_eq_k1 : l1'[k + 1]'(by omega) = l1[k]'(by omega) :=
          getElem_swap_eq_succ_ic l1 k hk
      simp only [invContrib_ic, show k < l1'.length from by omega, dite_true,
                  show k + 1 < l1'.length from by omega, h_eq_k, h_eq_k1]
      split
      · omega
      · rfl
    · intro p hp
      have ⟨hp_in, hp_ne⟩ := mem_erase_nodup_ic (pairsList_nodup n) hp
      rw [mem_pairsList] at hp_in
      have h_eq1 : l1'[p.1]'(by omega) = l1[swapIndex k p.1]'(swapIndex_lt_of_lt k p.1 n hk hp_in.1) :=
          getElem_swap_swapIndex l1 k p.1 hk (by omega)
      have h_eq2 : l1'[p.2]'(by omega) = l1[swapIndex k p.2]'(swapIndex_lt_of_lt k p.2 n hk hp_in.2.1) :=
          getElem_swap_swapIndex l1 k p.2 hk (by omega)
      simp only [invContrib_ic, swapPair,
                  show p.1 < l1'.length from by omega, dite_true,
                  show p.2 < l1'.length from by omega,
                  show (swapIndex k p.1) < l1.length from swapIndex_lt_of_lt k p.1 n hk hp_in.1,
                  show (swapIndex k p.2) < l1.length from swapIndex_lt_of_lt k p.2 n hk hp_in.2.1,
                  h_eq1, h_eq2]
      congr 1

/-- 反転数 > 0 → 隣接反転ペアが存在し、そのスワップで反転数が減少する -/
theorem exists_adj_inv_swap (l1 l2 : List FallingUnit)
        (h_perm : l1.Perm l2) (h_nodup : l1.Nodup)
        (h_inv_pos : invCount l1 l2 > 0) :
        ∃ (k : Nat) (hk : k + 1 < l1.length),
            posIn (l1[k]'(by omega)) l2 > posIn (l1[k + 1]'hk) l2 ∧
            invCount (l1.take k ++ l1[k + 1]'hk :: l1[k]'(by omega) :: l1.drop (k + 2)) l2 <
                invCount l1 l2 := by
    obtain ⟨i, j, hi, hj, h_lt_ij, h_inv_ij⟩ := exists_inv_of_invCount_pos l1 l2 h_inv_pos
    obtain ⟨k, hk, h_inv_k⟩ := exists_adj_inv_of_exists_inv l1 l2 i j h_lt_ij hi hj h_inv_ij
    exact ⟨k, hk, h_inv_k, invCount_adj_swap_lt l1 l2 h_perm h_nodup k hk h_inv_k⟩

/-- 隣接 swap は Perm を保存する -/
theorem adj_swap_perm (l : List FallingUnit) (k : Nat) (hk : k + 1 < l.length) :
        (l.take k ++ l[k + 1]'hk :: l[k]'(by omega) :: l.drop (k + 2)).Perm l := by
    set a := l[k]'(by omega) with ha_def
    set b := l[k + 1]'hk with hb_def
    set prefix_ := l.take k with hpre_def
    set suffix_ := l.drop (k + 2) with hsuf_def
    have h_split : l = prefix_ ++ a :: b :: suffix_ := by
        simp only [hpre_def, ha_def, hb_def, hsuf_def]
        conv_lhs => rw [← List.take_append_drop k l]
        have h_dk : l.drop k = l[k]'(by omega) :: l.drop (k + 1) :=
            (List.cons_getElem_drop_succ (h := by omega)).symm
        have h_dk1 : l.drop (k + 1) = l[k + 1]'hk :: l.drop (k + 2) :=
            (List.cons_getElem_drop_succ (h := hk)).symm
        rw [h_dk, h_dk1]
    have h1 : (prefix_ ++ b :: a :: suffix_).Perm (prefix_ ++ a :: b :: suffix_) := by
        apply List.Perm.append_left
        exact List.Perm.swap a b suffix_
    have h2 : (prefix_ ++ a :: b :: suffix_) = l := h_split.symm
    rw [h2] at h1
    exact h1

-- ================================================================
-- floatingUnits の位置非共有 (メンバーシップベース)
-- ================================================================

/-- floatingUnits の異なる要素は位置非共有 -/
theorem floatingUnits_elem_positions_disjoint (s : Shape)
        (u v : FallingUnit) (hu : u ∈ floatingUnits s) (hv : v ∈ floatingUnits s)
        (h_ne : u ≠ v) :
        ∀ p, p ∈ u.positions → v.positions.any (· == p) = false := by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hu
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hv
    have h_ij : i ≠ j := fun h_eq => h_ne (by subst h_eq; rfl)
    intro p hp
    exact floatingUnits_pairwise_disjoint s i j hi hj h_ij p
        (List.any_eq_true.mpr ⟨p, hp, BEq.rfl⟩)

-- ================================================================
-- pin の minLayerAtDir 性質
-- ================================================================

/-- pin は自分の方角でのみ minLayerAtDir が some を返す -/
theorem pin_minLayerAtDir_none (p : QuarterPos) (d : Direction) (h : d ≠ p.dir) :
        (FallingUnit.pin p).minLayerAtDir d = none := by
    unfold FallingUnit.minLayerAtDir FallingUnit.positions
    simp only [List.filterMap_cons, List.filterMap_nil]
    have h_neq : (p.dir == d) = false := by
        revert h; cases p.dir <;> cases d <;> decide
    rw [h_neq]
    rfl

/-- pin は自分の方角では minLayerAtDir = some p.layer -/
theorem pin_minLayerAtDir_self (p : QuarterPos) :
        (FallingUnit.pin p).minLayerAtDir p.dir = some p.layer := by
    simp only [FallingUnit.minLayerAtDir, FallingUnit.positions, List.filterMap_cons,
        List.filterMap_nil]
    simp only [BEq.rfl, ↓reduceIte, List.foldl_cons, List.foldl_nil]

-- ================================================================
-- 構造結合到達可能 → 同クラスタ → 位置非共有矛盾
-- ================================================================

/-- u がクラスタ型 floatingUnit で、p1 ∈ u.positions かつ
    isStructurallyBonded s p1 p2 = true であれば、
    p2 も u のクラスタに属する（GenericReachable + 完全性）。
    p2 が別の v.positions にも属すると位置非共有に矛盾する。 -/
theorem floatingUnits_bonded_positions_absurd (s : Shape)
        (u v : FallingUnit) (hu : u ∈ floatingUnits s) (hv : v ∈ floatingUnits s)
        (h_ne : u ≠ v)
        (ps_u : List QuarterPos) (h_u_eq : u = .cluster ps_u)
        (h_psu_mem : ps_u ∈ allStructuralClustersList s)
        (p1 p2 : QuarterPos) (hp1 : p1 ∈ ps_u) (hp2 : p2 ∈ v.positions)
        (h_isb : isStructurallyBonded s p1 p2 = true) :
        False := by
    -- ps_u = structuralClusterList s seed for some seed
    obtain ⟨seed, h_ps_eq, h_layer_seed, _⟩ :=
        allStructuralClustersList_is_structuralClusterList s ps_u h_psu_mem
    -- p1 ∈ ps_u → (structuralClusterList s seed).any (· == p1) = true
    have hp1_any : (structuralClusterList s seed).any (· == p1) = true :=
        h_ps_eq ▸ List.any_eq_true.mpr ⟨p1, hp1, BEq.rfl⟩
    -- GenericReachable seed p1
    have h_reach_p1 := structuralClusterList_sound s seed p1 hp1_any
    -- GenericReachable seed p2 (seed → ... → p1 → p2)
    have h_reach_p2 : GenericReachable (isStructurallyBonded s) seed p2 :=
        h_reach_p1.trans (.step h_isb .refl)
    -- p2 ∈ structuralClusterList s seed (完全性)
    have h_lc : s.layerCount > 0 := by omega
    have hp2_any : (structuralClusterList s seed).any (· == p2) = true :=
        structuralClusterList_complete s seed p2 h_lc h_reach_p2
    -- p2 ∈ ps_u
    have hp2_in_psu : p2 ∈ ps_u := by
        rw [h_ps_eq]
        exact List.any_eq_true.mp hp2_any |>.choose_spec.2 |> eq_of_beq |> fun h =>
            h ▸ (List.any_eq_true.mp hp2_any).choose_spec.1
    -- p2 ∈ u.positions (since u = cluster ps_u → positions = ps_u)
    have hp2_u : p2 ∈ u.positions := h_u_eq ▸ hp2_in_psu
    -- 位置非共有: p2 ∈ u.positions → v.positions.any (· == p2) = false
    have h_disj := floatingUnits_elem_positions_disjoint s u v hu hv h_ne p2 hp2_u
    -- だが p2 ∈ v.positions → v.positions.any (· == p2) = true
    have h_p2_v : v.positions.any (· == p2) = true :=
        List.any_eq_true.mpr ⟨p2, hp2, BEq.rfl⟩
    exact absurd h_p2_v (by rw [h_disj]; exact Bool.noConfusion)

-- ================================================================
-- 構造結合のステップ幅制約
-- ================================================================

/-- isStructurallyBonded true → 層差は 0 (水平) か 1 (垂直) -/
theorem isStructurallyBonded_layer_diff (s : Shape) (p1 p2 : QuarterPos)
        (h : isStructurallyBonded s p1 p2 = true) :
        p1.layer = p2.layer ∨ p1.layer + 1 = p2.layer ∨ p2.layer + 1 = p1.layer := by
    simp only [isStructurallyBonded] at h
    generalize hq1 : p1.getQuarter s = q1 at h
    generalize hq2 : p2.getQuarter s = q2 at h
    cases q1 with
    | none => cases q2 <;> simp only [Bool.false_eq_true] at h
    | some v1 => cases q2 with
        | none => simp only [Bool.false_eq_true] at h
        | some v2 =>
            simp only [Bool.and_eq_true] at h
            obtain ⟨⟨_, _⟩, h_bond⟩ := h
            simp only [Bool.or_eq_true, Bool.and_eq_true] at h_bond
            rcases h_bond with ⟨h_layer, _⟩ | ⟨h_vert, _⟩
            · left; exact beq_iff_eq.mp h_layer
            · simp only [LayerIndex.verticallyAdjacent, Bool.or_eq_true, beq_iff_eq] at h_vert
              rcases h_vert with h | h
              · right; left; omega
              · right; right; omega

/-- isStructurallyBonded true で方角が変わる → 水平ステップ (同層・隣接方角) -/
theorem isStructurallyBonded_dir_change_horizontal (s : Shape) (p1 p2 : QuarterPos)
        (h : isStructurallyBonded s p1 p2 = true) (h_dir : p1.dir ≠ p2.dir) :
        p1.layer = p2.layer ∧ p1.dir.adjacent p2.dir = true := by
    simp only [isStructurallyBonded] at h
    generalize hq1 : p1.getQuarter s = q1 at h
    generalize hq2 : p2.getQuarter s = q2 at h
    cases q1 with
    | none => cases q2 <;> simp only [Bool.false_eq_true] at h
    | some v1 => cases q2 with
        | none => simp only [Bool.false_eq_true] at h
        | some v2 =>
            simp only [Bool.and_eq_true] at h
            obtain ⟨⟨_, _⟩, h_bond⟩ := h
            simp only [Bool.or_eq_true, Bool.and_eq_true] at h_bond
            rcases h_bond with ⟨h_layer, h_adj⟩ | ⟨_, h_dir_eq⟩
            · exact ⟨beq_iff_eq.mp h_layer, h_adj⟩
            · exact absurd (beq_iff_eq.mp h_dir_eq) h_dir

-- ================================================================
-- GenericReachable の層到達定理 (離散的中間値定理)
-- ================================================================

/-- GenericReachable パスで layer a ≤ L ≤ layer b なら、
    seed から到達可能な層 L の位置が存在する -/
theorem genReachable_exists_at_layer (s : Shape)
        (p q : QuarterPos) (h : GenericReachable (isStructurallyBonded s) p q)
        (L : Nat) (hp : p.layer ≤ L) (hq : L ≤ q.layer) :
        ∃ r, GenericReachable (isStructurallyBonded s) p r ∧ r.layer = L := by
    induction h generalizing L with
    | refl => exact ⟨_, .refl, by omega⟩
    | step h_edge h_rest ih =>
        rename_i mid _
        have h_diff := isStructurallyBonded_layer_diff s _ mid h_edge
        by_cases h_le : mid.layer ≤ L
        · obtain ⟨r, h_reach, h_rl⟩ := ih L h_le hq
          exact ⟨r, .step h_edge h_reach, h_rl⟩
        · push Not at h_le
          refine ⟨_, .refl, ?_⟩
          rcases h_diff with h | h | h <;> omega

/-- GenericReachable パスで layer a ≥ L ≥ layer b なら、
    seed から到達可能な層 L の位置が存在する (対称版) -/
theorem genReachable_exists_at_layer_ge (s : Shape)
        (p q : QuarterPos) (h : GenericReachable (isStructurallyBonded s) p q)
        (L : Nat) (hp : L ≤ p.layer) (hq : q.layer ≤ L) :
        ∃ r, GenericReachable (isStructurallyBonded s) p r ∧ r.layer = L := by
    induction h generalizing L with
    | refl => exact ⟨_, .refl, by omega⟩
    | step h_edge h_rest ih =>
        rename_i mid _
        have h_diff := isStructurallyBonded_layer_diff s _ mid h_edge
        by_cases h_ge : L ≤ mid.layer
        · obtain ⟨r, h_reach, h_rl⟩ := ih L h_ge hq
          exact ⟨r, .step h_edge h_reach, h_rl⟩
        · push Not at h_ge
          refine ⟨_, .refl, ?_⟩
          rcases h_diff with h | h | h <;> omega

/-- GenericReachable パスの始点・終点のレイヤ間の任意のレイヤに到達可能 (統合版) -/
theorem genReachable_exists_at_layer_between (s : Shape)
        (p q : QuarterPos) (h : GenericReachable (isStructurallyBonded s) p q)
        (L : Nat) (hL_ge : min p.layer q.layer ≤ L) (hL_le : L ≤ max p.layer q.layer) :
        ∃ r, GenericReachable (isStructurallyBonded s) p r ∧ r.layer = L := by
    by_cases h_pq : p.layer ≤ q.layer
    · exact genReachable_exists_at_layer s p q h L (by omega) (by omega)
    · push Not at h_pq
      exact genReachable_exists_at_layer_ge s p q h L (by omega) (by omega)

-- ================================================================
-- GenericReachable の水平ステップ存在定理
-- ================================================================

/-- d1 ≠ d2 で GenericReachable なら、パス上に水平ステップ (同層・隣接方角) があり、
    その 2 位置は seed から到達可能 -/
theorem genReachable_diff_dir_horizontal (s : Shape)
        (p q : QuarterPos)
        (h : GenericReachable (isStructurallyBonded s) p q)
        (h_dir : p.dir ≠ q.dir) :
        ∃ a b, isStructurallyBonded s a b = true ∧
            a.layer = b.layer ∧ a.dir.adjacent b.dir = true ∧
            a.dir = p.dir ∧
            GenericReachable (isStructurallyBonded s) p a ∧
            GenericReachable (isStructurallyBonded s) p b := by
    revert h_dir
    induction h with
    | refl => intro h_dir; exact absurd rfl h_dir
    | @step p' mid r' h_edge h_rest ih =>
        intro h_dir
        by_cases h_pd : p'.dir = mid.dir
        · -- p'.dir = mid.dir → mid.dir ≠ r'.dir → 帰納法
          have h_md : mid.dir ≠ r'.dir := fun heq => h_dir (h_pd.trans heq)
          obtain ⟨a, b, hab, h_layer, h_adj, h_a_dir, h_reach_a, h_reach_b⟩ := ih h_md
          exact ⟨a, b, hab, h_layer, h_adj, h_a_dir.trans h_pd.symm,
              .step h_edge h_reach_a, .step h_edge h_reach_b⟩
        · -- p'.dir ≠ mid.dir → p'→mid は水平ステップ
          have ⟨h_layer, h_adj⟩ :=
              isStructurallyBonded_dir_change_horizontal s p' mid h_edge h_pd
          exact ⟨p', mid, h_edge, h_layer, h_adj, rfl, .refl, .step h_edge .refl⟩

-- ================================================================
-- Direction の方角ブロッキング (4方角 cyclic)
-- ================================================================

/-- 任意の方角 d3 は、隣接する 2 方角 d1, d2 のいずれかに隣接するか等しい -/
theorem dir_covered_by_adjacent_pair (d1 d2 d3 : Direction)
        (h_adj : d1.adjacent d2 = true) :
        d3 = d1 ∨ d3 = d2 ∨ d3.adjacent d1 = true ∨ d3.adjacent d2 = true := by
    revert h_adj; cases d1 <;> cases d2 <;> cases d3 <;> decide

/-- 2つの異なる方角は全4方角をカバーする: d3 は d1 か d2 に等しいか、どちらかに隣接 -/
theorem dir_covered_by_diff_pair (d1 d2 d3 : Direction) (h_ne : d1 ≠ d2) :
        d3 = d1 ∨ d3 = d2 ∨ d3.adjacent d1 = true ∨ d3.adjacent d2 = true := by
    revert h_ne; cases d1 <;> cases d2 <;> cases d3 <;> decide

/-- 層 L で隣接 2 方角 (d_a, d_b) をクラスタ u が占有 (canFormBond) する場合、
    v は層 L にどの方角でも位置を持てない。
    理由: v の (L, d_c) は d_a or d_b に隣接 → isStructurallyBonded → 同クラスタ矛盾。
    または d_c = d_a or d_c = d_b → disjoint 矛盾。 -/
theorem horizontal_pair_blocks_layer (s : Shape)
        (u v : FallingUnit) (hu : u ∈ floatingUnits s) (hv : v ∈ floatingUnits s)
        (h_ne : u ≠ v)
        (ps_u : List QuarterPos) (h_u_eq : u = .cluster ps_u)
        (h_psu_mem : ps_u ∈ allStructuralClustersList s)
        (ps_v : List QuarterPos) (h_v_eq : v = .cluster ps_v)
        (h_psv_mem : ps_v ∈ allStructuralClustersList s)
        (d_a d_b : Direction) (h_adj : d_a.adjacent d_b = true)
        (L : Nat)
        (pa : QuarterPos) (hpa_mem : pa ∈ ps_u) (hpa_dir : pa.dir = d_a) (hpa_layer : pa.layer = L)
        (pb : QuarterPos) (hpb_mem : pb ∈ ps_u) (hpb_dir : pb.dir = d_b) (hpb_layer : pb.layer = L)
        (pv : QuarterPos) (hpv_mem : pv ∈ ps_v) (hpv_layer : pv.layer = L) :
        False := by
    -- pv の方角を d_c とする
    set d_c := pv.dir with hpv_dir
    -- List.Mem → List.any (· == p) = true 変換ヘルパー
    have hpa_any : ps_u.any (· == pa) = true :=
        List.any_eq_true.mpr ⟨pa, hpa_mem, BEq.rfl⟩
    have hpb_any : ps_u.any (· == pb) = true :=
        List.any_eq_true.mpr ⟨pb, hpb_mem, BEq.rfl⟩
    have hpv_any : ps_v.any (· == pv) = true :=
        List.any_eq_true.mpr ⟨pv, hpv_mem, BEq.rfl⟩
    -- d_c は d_a, d_b のいずれかに等しいか隣接
    rcases dir_covered_by_adjacent_pair d_a d_b d_c h_adj with
        h_eq_a | h_eq_b | h_adj_a | h_adj_b
    · -- d_c = d_a → pv = pa (同 layer, 同 dir) → disjoint 矛盾
      have h_eq : pv = pa := by
          have h1 : pv.layer = pa.layer := hpv_layer.trans hpa_layer.symm
          have h2 : pv.dir = pa.dir := hpv_dir.symm.trans (h_eq_a.trans hpa_dir.symm)
          cases pv; cases pa; simp_all only [ne_eq, FallingUnit.cluster.injEq, List.any_eq_true, beq_iff_eq, exists_eq_right]
      have h_disj := floatingUnits_elem_positions_disjoint s u v hu hv h_ne pa (h_u_eq ▸ hpa_mem)
      have : v.positions.any (· == pa) = true :=
          List.any_eq_true.mpr ⟨pv, h_v_eq ▸ hpv_mem, by rw [h_eq]; exact BEq.rfl⟩
      rw [h_disj] at this; exact absurd this (by decide)
    · -- d_c = d_b → pv = pb → disjoint 矛盾
      have h_eq : pv = pb := by
          have h1 : pv.layer = pb.layer := hpv_layer.trans hpb_layer.symm
          have h2 : pv.dir = pb.dir := hpv_dir.symm.trans (h_eq_b.trans hpb_dir.symm)
          cases pv; cases pb; simp_all only [ne_eq, FallingUnit.cluster.injEq, List.any_eq_true, beq_iff_eq, exists_eq_right]
      have h_disj := floatingUnits_elem_positions_disjoint s u v hu hv h_ne pb (h_u_eq ▸ hpb_mem)
      have : v.positions.any (· == pb) = true :=
          List.any_eq_true.mpr ⟨pv, h_v_eq ▸ hpv_mem, by rw [h_eq]; exact BEq.rfl⟩
      rw [h_disj] at this; exact absurd this (by decide)
    · -- d_c adj d_a → isStructurallyBonded s pa pv = true → floatingUnits_bonded_positions_absurd
      have h_pa_bond := allStructuralClustersList_all_bondable s ps_u h_psu_mem pa hpa_any
      have h_pv_bond := allStructuralClustersList_all_bondable s ps_v h_psv_mem pv hpv_any
      obtain ⟨q_a, hq_a_get, hq_a_bond⟩ := h_pa_bond
      obtain ⟨q_v, hq_v_get, hq_v_bond⟩ := h_pv_bond
      have h_isb : isStructurallyBonded s pa pv = true := by
          unfold isStructurallyBonded
          rw [hq_a_get, hq_v_get]
          simp only [hq_a_bond, hq_v_bond, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true]
          left; exact ⟨by simp only [hpa_layer, hpv_layer, BEq.rfl],
              by rw [hpa_dir]; exact (Direction.adjacent_symm pv.dir d_a).symm ▸ h_adj_a⟩
      exact floatingUnits_bonded_positions_absurd s u v hu hv h_ne ps_u h_u_eq h_psu_mem pa pv
          hpa_mem (h_v_eq ▸ hpv_mem) h_isb
    · -- d_c adj d_b → 同様に isStructurallyBonded s pb pv → 矛盾
      have h_pb_bond := allStructuralClustersList_all_bondable s ps_u h_psu_mem pb hpb_any
      have h_pv_bond := allStructuralClustersList_all_bondable s ps_v h_psv_mem pv hpv_any
      obtain ⟨q_b, hq_b_get, hq_b_bond⟩ := h_pb_bond
      obtain ⟨q_v, hq_v_get, hq_v_bond⟩ := h_pv_bond
      have h_isb : isStructurallyBonded s pb pv = true := by
          unfold isStructurallyBonded
          rw [hq_b_get, hq_v_get]
          simp only [hq_b_bond, hq_v_bond, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true]
          left; exact ⟨by simp only [hpb_layer, hpv_layer, BEq.rfl],
              by rw [hpb_dir]; exact (Direction.adjacent_symm pv.dir d_b).symm ▸ h_adj_b⟩
      exact floatingUnits_bonded_positions_absurd s u v hu hv h_ne ps_u h_u_eq h_psu_mem pb pv
          hpb_mem (h_v_eq ▸ hpv_mem) h_isb

-- ================================================================
-- floatingUnits クラスタメンバーシップ
-- ================================================================

/-- floatingUnits のクラスタは allStructuralClustersList のメンバーである -/
theorem floatingUnits_cluster_in_allStructuralClustersList (s : Shape) (ps : List QuarterPos)
        (h : FallingUnit.cluster ps ∈ floatingUnits s) :
        ps ∈ allStructuralClustersList s := by
    rw [floatingUnits_eq_append, List.mem_append] at h
    cases h with
    | inl h_cluster =>
        rw [List.mem_map] at h_cluster
        obtain ⟨ps', hps', h_eq⟩ := h_cluster
        cases h_eq
        exact (List.mem_filter.mp hps').1
    | inr h_pin =>
        rw [List.mem_map] at h_pin
        obtain ⟨_, _, h_eq⟩ := h_pin
        exact absurd h_eq (by simp only [reduceCtorEq, not_false_eq_true])

/-- 同一クラスタの 2 位置は GenericReachable で結合 -/
theorem cluster_genReachable (s : Shape) (ps : List QuarterPos)
        (hps : ps ∈ allStructuralClustersList s)
        (p q : QuarterPos) (hp : p ∈ ps) (hq : q ∈ ps) :
        GenericReachable (isStructurallyBonded s) p q := by
    obtain ⟨seed, h_eq, h_layer, _⟩ :=
        allStructuralClustersList_is_structuralClusterList s ps hps
    have hp_any : (structuralClusterList s seed).any (· == p) = true :=
        h_eq ▸ List.any_eq_true.mpr ⟨p, hp, BEq.rfl⟩
    have hq_any : (structuralClusterList s seed).any (· == q) = true :=
        h_eq ▸ List.any_eq_true.mpr ⟨q, hq, BEq.rfl⟩
    exact (structuralClusterList_sound s seed p hp_any).symm
        (isStructurallyBonded_symm s) |>.trans
        (structuralClusterList_sound s seed q hq_any)

/-- GenericReachable パス上の到達点は元のクラスタに属する -/
theorem genReachable_mem_cluster (s : Shape) (ps : List QuarterPos)
        (hps : ps ∈ allStructuralClustersList s)
        (p q : QuarterPos) (hp : p ∈ ps)
        (h : GenericReachable (isStructurallyBonded s) p q) :
        q ∈ ps := by
    obtain ⟨seed, h_eq, h_layer, _⟩ :=
        allStructuralClustersList_is_structuralClusterList s ps hps
    have hp_any : (structuralClusterList s seed).any (· == p) = true :=
        h_eq ▸ List.any_eq_true.mpr ⟨p, hp, BEq.rfl⟩
    have h_reach_q : GenericReachable (isStructurallyBonded s) seed q :=
        (structuralClusterList_sound s seed p hp_any).trans h
    have h_lc : s.layerCount > 0 := by omega
    have hq_any := structuralClusterList_complete s seed q h_lc h_reach_q
    -- hq_any : (structuralClusterList s seed).any (· == q) = true
    -- h_eq : ps = structuralClusterList s seed → ps 内のメンバーシップに変換
    have hq_in_scl := List.any_eq_true.mp hq_any
    obtain ⟨q', hq'_mem, hq'_beq⟩ := hq_in_scl
    have hq_eq : q' = q := eq_of_beq hq'_beq
    rw [h_eq]; exact hq_eq ▸ hq'_mem

/-- 異なるクラスタの水平ペアがレイヤ L をブロック → 全位置が L の片側にある -/
theorem cluster_all_one_side_of_blocking (s : Shape)
        (u v : FallingUnit) (hu : u ∈ floatingUnits s) (hv : v ∈ floatingUnits s)
        (h_ne : u ≠ v)
        (ps_u : List QuarterPos) (h_u_eq : u = .cluster ps_u)
        (h_psu_mem : ps_u ∈ allStructuralClustersList s)
        (ps_v : List QuarterPos) (h_v_eq : v = .cluster ps_v)
        (h_psv_mem : ps_v ∈ allStructuralClustersList s)
        (d_a d_b : Direction) (h_adj : d_a.adjacent d_b = true)
        (L_h : Nat)
        (pa : QuarterPos) (hpa_mem : pa ∈ ps_u) (hpa_dir : pa.dir = d_a) (hpa_layer : pa.layer = L_h)
        (pb : QuarterPos) (hpb_mem : pb ∈ ps_u) (hpb_dir : pb.dir = d_b) (hpb_layer : pb.layer = L_h)
        (pv : QuarterPos) (hpv_mem : pv ∈ ps_v) :
        pv.layer ≠ L_h := by
    intro h_eq
    exact horizontal_pair_blocks_layer s u v hu hv h_ne
        ps_u h_u_eq h_psu_mem ps_v h_v_eq h_psv_mem
        d_a d_b h_adj L_h pa hpa_mem hpa_dir hpa_layer pb hpb_mem hpb_dir hpb_layer
        pv hpv_mem h_eq

/-- 水平ペアのレイヤより上に位置がないか下に位置がないか (片側制約) -/
theorem cluster_positions_one_side (s : Shape)
        (u v : FallingUnit) (hu : u ∈ floatingUnits s) (hv : v ∈ floatingUnits s)
        (h_ne : u ≠ v)
        (ps_u : List QuarterPos) (h_u_eq : u = .cluster ps_u)
        (h_psu_mem : ps_u ∈ allStructuralClustersList s)
        (ps_v : List QuarterPos) (h_v_eq : v = .cluster ps_v)
        (h_psv_mem : ps_v ∈ allStructuralClustersList s)
        (d_a d_b : Direction) (h_adj : d_a.adjacent d_b = true)
        (L_h : Nat)
        (pa : QuarterPos) (hpa_mem : pa ∈ ps_u) (hpa_dir : pa.dir = d_a) (hpa_layer : pa.layer = L_h)
        (pb : QuarterPos) (hpb_mem : pb ∈ ps_u) (hpb_dir : pb.dir = d_b) (hpb_layer : pb.layer = L_h)
        -- v が L_h の上下両方に位置を持つなら矛盾
        (pv_lo pv_hi : QuarterPos) (hlo_mem : pv_lo ∈ ps_v) (hhi_mem : pv_hi ∈ ps_v)
        (h_lo : pv_lo.layer ≤ L_h) (h_hi : L_h ≤ pv_hi.layer) :
        False := by
    -- pv_lo と pv_hi の GR パスを取得
    have h_gr := cluster_genReachable s ps_v h_psv_mem pv_lo pv_hi hlo_mem hhi_mem
    -- IVT で L_h にある v の位置を取得
    obtain ⟨r_v, h_reach_rv, h_rv_layer⟩ :=
        genReachable_exists_at_layer s pv_lo pv_hi h_gr L_h h_lo h_hi
    -- r_v ∈ ps_v
    have h_rv_mem := genReachable_mem_cluster s ps_v h_psv_mem pv_lo r_v hlo_mem h_reach_rv
    -- horizontal_pair_blocks_layer で矛盾
    exact horizontal_pair_blocks_layer s u v hu hv h_ne
        ps_u h_u_eq h_psu_mem ps_v h_v_eq h_psv_mem
        d_a d_b h_adj L_h pa hpa_mem hpa_dir hpa_layer pb hpb_mem hpb_dir hpb_layer
        r_v h_rv_mem h_rv_layer

/-- minLayerAtDir は対応方角の全位置レイヤ以下 -/
theorem minLayerAtDir_le_of_mem (u : FallingUnit) (dir : Direction) (l : Nat)
        (h : u.minLayerAtDir dir = some l) (p : QuarterPos)
        (hp : p ∈ u.positions) (hd : p.dir = dir) :
        l ≤ p.layer := by
    simp only [FallingUnit.minLayerAtDir] at h
    change (u.positions.filterMap fun q =>
        if q.dir == dir then some q.layer else none).foldl foldMinOption none = some l at h
    have : p.layer ∈ (u.positions.filterMap fun q =>
        if q.dir == dir then some q.layer else none) := by
        rw [List.mem_filterMap]
        exact ⟨p, hp, by simp only [show (p.dir == dir) = true from by rw [hd]; exact BEq.rfl, ↓reduceIte]⟩
    exact foldMinOption_none_le _ l h p.layer this

-- ================================================================
-- shouldProcessBefore の mutual 不可性 (位置非共有 → 双方向 shouldProcessBefore 不可)
-- ================================================================

/-- 位置非共有な要素間で shouldProcessBefore が双方向 true にはならない。
    shouldProcessBefore(u,v)=true は ∃ dir, u.minLayer@dir < v.minLayer@dir を意味する。
    shouldProcessBefore(v,u)=true は ∃ dir', v.minLayer@dir' < u.minLayer@dir' を意味する。
    minLayer の witness は対応する位置を持ち、
    tied_no_shared_dir の証明パターンにより同一 (layer, dir) が共有されて矛盾する。 -/
-- shouldProcessBefore true の展開による方角 witness の抽出
theorem shouldProcessBefore_true_witness (u v : FallingUnit)
        (h : shouldProcessBefore u v = true) :
        ∃ d lu lv, u.minLayerAtDir d = some lu ∧ v.minLayerAtDir d = some lv ∧ lu < lv := by
    simp only [shouldProcessBefore, Direction.all, List.any_cons, List.any_nil,
        Bool.or_false, Bool.or_eq_true] at h
    -- h : (ne_case || se_case || sw_case || nw_case) = true
    -- Bool.or_eq_true で分岐
    rcases h with h | h | h | h
    · -- ne ケース
      generalize hne_u : u.minLayerAtDir .ne = u_ne at h
      generalize hne_v : v.minLayerAtDir .ne = v_ne at h
      rcases u_ne with _ | lu <;> rcases v_ne with _ | lv <;> simp only [Bool.false_eq_true, decide_eq_true_eq] at h
      exact ⟨.ne, lu, lv, hne_u, hne_v, h⟩
    · generalize hse_u : u.minLayerAtDir .se = u_se at h
      generalize hse_v : v.minLayerAtDir .se = v_se at h
      rcases u_se with _ | lu <;> rcases v_se with _ | lv <;> simp only [Bool.false_eq_true, decide_eq_true_eq] at h
      exact ⟨.se, lu, lv, hse_u, hse_v, h⟩
    · generalize hsw_u : u.minLayerAtDir .sw = u_sw at h
      generalize hsw_v : v.minLayerAtDir .sw = v_sw at h
      rcases u_sw with _ | lu <;> rcases v_sw with _ | lv <;> simp only [Bool.false_eq_true, decide_eq_true_eq] at h
      exact ⟨.sw, lu, lv, hsw_u, hsw_v, h⟩
    · generalize hnw_u : u.minLayerAtDir .nw = u_nw at h
      generalize hnw_v : v.minLayerAtDir .nw = v_nw at h
      rcases u_nw with _ | lu <;> rcases v_nw with _ | lv <;> simp only [Bool.false_eq_true, decide_eq_true_eq] at h
      exact ⟨.nw, lu, lv, hnw_u, hnw_v, h⟩

theorem shouldProcessBefore_no_mutual (s : Shape)
        (u v : FallingUnit) (hu : u ∈ floatingUnits s) (hv : v ∈ floatingUnits s)
        (h_ne : u ≠ v)
        (h_spb_uv : shouldProcessBefore u v = true)
        (h_spb_vu : shouldProcessBefore v u = true) : False := by
    -- shouldProcessBefore(u,v) と shouldProcessBefore(v,u) から方角 witness を抽出
    obtain ⟨d1, lu1, lv1, hu1, hv1, h_lt1⟩ := shouldProcessBefore_true_witness u v h_spb_uv
    obtain ⟨d2, lv2, lu2, hv2, hu2, h_lt2⟩ := shouldProcessBefore_true_witness v u h_spb_vu
    -- d1 = d2 の場合: 同方角で lu < lv かつ lv < lu → omega 矛盾
    by_cases h_dir : d1 = d2
    · subst h_dir
      -- u.minLayerAtDir d1 = some lu1, u.minLayerAtDir d1 = some lu2
      rw [hu1] at hu2; rw [hv1] at hv2
      cases hu2; cases hv2
      omega
    -- d1 ≠ d2 の場合:
    -- u は d1, d2 両方角で minLayerAtDir = some → pin ではない（cluster 型）
    -- v も同様に cluster 型
    · -- u が pin なら矛盾: pin は 1 方角しか持たない
      have h_u_not_pin : ∀ p, u ≠ .pin p := by
          intro p h_eq; subst h_eq
          -- (pin p).minLayerAtDir d1 = some lu1 → d1 = p.dir
          -- (pin p).minLayerAtDir d2 = some lu2 → d2 = p.dir → d1 = d2 矛盾
          by_cases h1 : d1 = p.dir
          · by_cases h2 : d2 = p.dir
            · exact h_dir (h1.trans h2.symm)
            · rw [pin_minLayerAtDir_none p d2 h2] at hu2; exact absurd hu2 (by simp only [reduceCtorEq, not_false_eq_true])
          · rw [pin_minLayerAtDir_none p d1 h1] at hu1; exact absurd hu1 (by simp only [reduceCtorEq, not_false_eq_true])
      -- v が pin なら矛盾
      have h_v_not_pin : ∀ p, v ≠ .pin p := by
          intro p h_eq; subst h_eq
          by_cases h1 : d1 = p.dir
          · by_cases h2 : d2 = p.dir
            · exact h_dir (h1.trans h2.symm)
            · rw [pin_minLayerAtDir_none p d2 h2] at hv2; exact absurd hv2 (by simp only [reduceCtorEq, not_false_eq_true])
          · rw [pin_minLayerAtDir_none p d1 h1] at hv1; exact absurd hv1 (by simp only [reduceCtorEq, not_false_eq_true])
      -- u, v は cluster 型
      obtain ⟨ps_u, rfl⟩ : ∃ ps, u = .cluster ps := by
          cases u with
          | cluster ps => exact ⟨ps, rfl⟩
          | pin p => exact absurd rfl (h_u_not_pin p)
      obtain ⟨ps_v, rfl⟩ : ∃ ps, v = .cluster ps := by
          cases v with
          | cluster ps => exact ⟨ps, rfl⟩
          | pin p => exact absurd rfl (h_v_not_pin p)
      -- minLayerAtDir の witness 位置を取得
      obtain ⟨pu1, hpu1_mem, hpu1_dir, hpu1_layer⟩ := minLayerAtDir_some_witness _ d1 lu1 hu1
      obtain ⟨pv1, hpv1_mem, hpv1_dir, hpv1_layer⟩ := minLayerAtDir_some_witness _ d1 lv1 hv1
      obtain ⟨pv2, hpv2_mem, hpv2_dir, hpv2_layer⟩ := minLayerAtDir_some_witness _ d2 lv2 hv2
      obtain ⟨pu2, hpu2_mem, hpu2_dir, hpu2_layer⟩ := minLayerAtDir_some_witness _ d2 lu2 hu2
      -- 位置非共有
      have h_disj := floatingUnits_elem_positions_disjoint s _ _ hu hv h_ne
      -- ps_u, ps_v ∈ allStructuralClustersList
      have h_psu_mem := floatingUnits_cluster_in_allStructuralClustersList s ps_u hu
      have h_psv_mem := floatingUnits_cluster_in_allStructuralClustersList s ps_v hv
      -- u, v の d1/d2 間 GenericReachable
      have h_gr_u12 := cluster_genReachable s ps_u h_psu_mem pu1 pu2 hpu1_mem hpu2_mem
      have h_gr_u21 := cluster_genReachable s ps_u h_psu_mem pu2 pu1 hpu2_mem hpu1_mem
      have h_gr_v12 := cluster_genReachable s ps_v h_psv_mem pv1 pv2 hpv1_mem hpv2_mem
      have h_gr_v21 := cluster_genReachable s ps_v h_psv_mem pv2 pv1 hpv2_mem hpv1_mem
      -- d1 ≠ d2 の方角不等式
      have h_d2_ne_d1 : d2 ≠ d1 := fun h => h_dir h.symm
      -- u の d1→d2 パスの水平ステップ: (a_u, b_u) at L_u, a_u.dir = d1
      obtain ⟨a_u, b_u, _, h_LU_eq, h_adj_u, h_au_dir, h_reach_au, h_reach_bu⟩ :=
          genReachable_diff_dir_horizontal s pu1 pu2 h_gr_u12
              (hpu1_dir ▸ hpu2_dir ▸ h_dir)
      -- u の d2→d1 パスの水平ステップ: (a'_u, b'_u) at L'_u, a'_u.dir = d2
      obtain ⟨a'_u, b'_u, _, h_LU'_eq, h_adj_u', h_a'u_dir, h_reach_a'u, h_reach_b'u⟩ :=
          genReachable_diff_dir_horizontal s pu2 pu1 h_gr_u21
              (hpu2_dir ▸ hpu1_dir ▸ h_d2_ne_d1)
      -- v の d1→d2 パスの水平ステップ: (a_v, b_v) at L_v, a_v.dir = d1
      obtain ⟨a_v, b_v, _, h_LV_eq, h_adj_v, h_av_dir, h_reach_av, h_reach_bv⟩ :=
          genReachable_diff_dir_horizontal s pv1 pv2 h_gr_v12
              (hpv1_dir ▸ hpv2_dir ▸ h_dir)
      -- v の d2→d1 パスの水平ステップ: (a'_v, b'_v) at L'_v, a'_v.dir = d2
      obtain ⟨a'_v, b'_v, _, h_LV'_eq, h_adj_v', h_a'v_dir, h_reach_a'v, h_reach_b'v⟩ :=
          genReachable_diff_dir_horizontal s pv2 pv1 h_gr_v21
              (hpv2_dir ▸ hpv1_dir ▸ h_d2_ne_d1)
      -- 水平ステップ位置がクラスタに属する
      have h_au_mem := genReachable_mem_cluster s ps_u h_psu_mem pu1 a_u hpu1_mem h_reach_au
      have h_bu_mem := genReachable_mem_cluster s ps_u h_psu_mem pu1 b_u hpu1_mem h_reach_bu
      have h_a'u_mem := genReachable_mem_cluster s ps_u h_psu_mem pu2 a'_u hpu2_mem h_reach_a'u
      have h_b'u_mem := genReachable_mem_cluster s ps_u h_psu_mem pu2 b'_u hpu2_mem h_reach_b'u
      have h_av_mem := genReachable_mem_cluster s ps_v h_psv_mem pv1 a_v hpv1_mem h_reach_av
      have h_bv_mem := genReachable_mem_cluster s ps_v h_psv_mem pv1 b_v hpv1_mem h_reach_bv
      have h_a'v_mem := genReachable_mem_cluster s ps_v h_psv_mem pv2 a'_v hpv2_mem h_reach_a'v
      have h_b'v_mem := genReachable_mem_cluster s ps_v h_psv_mem pv2 b'_v hpv2_mem h_reach_b'v
      -- L_u, L'_u, L_v, L'_v の定義
      set L_u := a_u.layer with hLU_def
      set L'_u := a'_u.layer with hLU'_def
      set L_v := a_v.layer with hLV_def
      set L'_v := a'_v.layer with hLV'_def
      -- minLayerAtDir の最小性から L_u ≥ lu1, L'_u ≥ lu2, L_v ≥ lv1, L'_v ≥ lv2
      have h_LU_ge : lu1 ≤ L_u :=
          minLayerAtDir_le_of_mem _ d1 lu1 hu1 a_u h_au_mem (h_au_dir ▸ hpu1_dir)
      have h_LU'_ge : lu2 ≤ L'_u :=
          minLayerAtDir_le_of_mem _ d2 lu2 hu2 a'_u h_a'u_mem (h_a'u_dir ▸ hpu2_dir)
      have h_LV_ge : lv1 ≤ L_v :=
          minLayerAtDir_le_of_mem _ d1 lv1 hv1 a_v h_av_mem (h_av_dir ▸ hpv1_dir)
      have h_LV'_ge : lv2 ≤ L'_v :=
          minLayerAtDir_le_of_mem _ d2 lv2 hv2 a'_v h_a'v_mem (h_a'v_dir ▸ hpv2_dir)
      -- b'_u, b_v のレイヤ等式を事前計算
      have h_bu'_layer : b'_u.layer = L'_u := by rw [hLU'_def]; exact h_LU'_eq.symm
      have h_bv_layer : b_v.layer = L_v := by rw [hLV_def]; exact h_LV_eq.symm
      -- 片側制約: v は L'_u を跨げない → ∀ pv, pv.layer < L'_u or > L'_u
      -- V < L'_u の証明（V ≥ L'_u は pv2.layer ≥ L'_u ≥ lu2 > lv2 で矛盾）
      have h_V_lt_LU' : ∀ p, p ∈ ps_v → p.layer < L'_u := by
          intro p hp
          -- p.layer ≠ L'_u (blocking)
          have h_ne_LU' := cluster_all_one_side_of_blocking s
              (.cluster ps_u) (.cluster ps_v) hu hv h_ne
              ps_u rfl h_psu_mem ps_v rfl h_psv_mem
              a'_u.dir b'_u.dir h_adj_u' L'_u
              a'_u h_a'u_mem rfl rfl b'_u h_b'u_mem rfl h_bu'_layer
              p hp
          -- v を跨ぐ位置がないことから片側を決定
          by_contra h_not_lt
          push Not at h_not_lt
          have h_gt : p.layer > L'_u := by omega
          -- pv2.layer = lv2 < lu2 ≤ L'_u → pv2 は L'_u の下側
          have h_pv2_lt : pv2.layer < L'_u := by omega
          -- p が L'_u より上、pv2 が L'_u より下 → 跨ぎ矛盾
          exact cluster_positions_one_side s
              (.cluster ps_u) (.cluster ps_v) hu hv h_ne
              ps_u rfl h_psu_mem ps_v rfl h_psv_mem
              a'_u.dir b'_u.dir h_adj_u' L'_u
              a'_u h_a'u_mem rfl rfl b'_u h_b'u_mem rfl h_bu'_layer
              pv2 p hpv2_mem hp (by omega) (by omega)
      -- U < L_v の証明（U ≥ L_v は pu1.layer ≥ L_v ≥ lv1 > lu1 で矛盾）
      have h_U_lt_LV : ∀ p, p ∈ ps_u → p.layer < L_v := by
          intro p hp
          have h_ne_LV := cluster_all_one_side_of_blocking s
              (.cluster ps_v) (.cluster ps_u) hv hu (Ne.symm h_ne)
              ps_v rfl h_psv_mem ps_u rfl h_psu_mem
              a_v.dir b_v.dir h_adj_v L_v
              a_v h_av_mem rfl rfl b_v h_bv_mem rfl h_bv_layer
              p hp
          by_contra h_not_lt
          push Not at h_not_lt
          have h_gt : p.layer > L_v := by omega
          -- pu1.layer = lu1 < lv1 ≤ L_v → pu1 は L_v の下側
          have h_pu1_lt : pu1.layer < L_v := by omega
          exact cluster_positions_one_side s
              (.cluster ps_v) (.cluster ps_u) hv hu (Ne.symm h_ne)
              ps_v rfl h_psv_mem ps_u rfl h_psu_mem
              a_v.dir b_v.dir h_adj_v L_v
              a_v h_av_mem rfl rfl b_v h_bv_mem rfl h_bv_layer
              pu1 p hpu1_mem hp (by omega) (by omega)
      -- L'_u ∈ U → L'_u < L_v、L_v ∈ V → L_v < L'_u → 矛盾
      have h_LU'_lt_LV : L'_u < L_v := h_U_lt_LV a'_u h_a'u_mem
      have h_LV_lt_LU' : L_v < L'_u := h_V_lt_LU' a_v h_av_mem
      omega

-- ================================================================
-- insertSorted の shouldProcessBefore 順序保存
-- ================================================================

/-- shouldProcessBefore(a, b) = true かつ b ∈ sorted ならば、
    insertSorted a sorted fuel で a は b より前に配置される。
    証明: sorted を先頭から走査し、shouldProcessBefore a head を判定。
    - shouldProcessBefore a head = true: a を挿入 → b は head 以降にあるので a < b
    - shouldProcessBefore a head = false: head ≠ b (もし head = b なら shouldProcessBefore a b = true ≠ false で矛盾)
      → b ∈ rest, 帰納法で成立 -/
theorem insertSorted_before_shouldProcessBefore (a b : FallingUnit) (sorted : List FallingUnit)
        (fuel : Nat) (h_fuel : fuel ≥ sorted.length)
        (h_mem : b ∈ sorted) (h_spb : shouldProcessBefore a b = true) :
        ∃ prefix_ suffix_,
            insertSorted a sorted fuel = prefix_ ++ [a] ++ suffix_ ∧
            b ∈ suffix_ := by
    induction sorted, fuel using insertSorted.induct a with
    | case1 sorted =>
        -- fuel = 0 → insertSorted a sorted 0 = a :: sorted
        exact ⟨[], sorted, by simp only [insertSorted, List.nil_append, List.cons_append], h_mem⟩
    | case2 =>
        -- sorted = [] → b ∈ [] 矛盾
        simp only [List.not_mem_nil] at h_mem
    | case3 fuel v rest h_spb_v =>
        -- shouldProcessBefore(a, v) = true → a :: v :: rest, b ∈ v :: rest
        simp only [insertSorted, h_spb_v, ite_true]
        exact ⟨[], v :: rest, rfl, h_mem⟩
    | case4 fuel v rest h_not_spb ih =>
        -- shouldProcessBefore(a, v) = false → v :: insertSorted a rest fuel
        simp only [insertSorted, h_not_spb]
        -- b ∈ v :: rest
        cases h_mem with
        | head =>
            -- b = v だが shouldProcessBefore a b = true ≠ false = shouldProcessBefore a v → 矛盾
            simp_all only [Bool.false_eq_true]
        | tail _ hb_rest =>
            -- b ∈ rest, 帰納法
            have h_fuel' : fuel ≥ rest.length := by
                simp only [List.length] at h_fuel; omega
            obtain ⟨p, s, h_eq, h_b_s⟩ := ih h_fuel' hb_rest
            exact ⟨v :: p, s, by simp only [Bool.false_eq_true, ↓reduceIte, h_eq, List.append_assoc, List.cons_append, List.nil_append], h_b_s⟩

/-- insertSorted は既存要素の相対順序を保存する。
    a ∈ sorted で b ∈ sorted かつ a が b より前にあるなら、
    insertSorted u sorted fuel でも a は b より前にある。 -/
theorem insertSorted_preserves_relative_order (u : FallingUnit)
        (sorted : List FallingUnit) (fuel : Nat) (h_fuel : fuel ≥ sorted.length)
        (a b : FallingUnit) (ha : a ∈ sorted) (hb : b ∈ sorted)
        (h_before : ∃ prefix_ mid suffix_, sorted = prefix_ ++ [a] ++ mid ++ [b] ++ suffix_) :
        ∃ prefix_ mid suffix_,
            insertSorted u sorted fuel = prefix_ ++ [a] ++ mid ++ [b] ++ suffix_ := by
    induction sorted, fuel using insertSorted.induct u with
    | case1 sorted =>
        -- fuel = 0 → insertSorted u sorted 0 = u :: sorted
        obtain ⟨p, m, s_, h_eq⟩ := h_before
        exact ⟨u :: p, m, s_, by simp only [h_eq, List.append_assoc, List.cons_append, List.nil_append, insertSorted]⟩
    | case2 =>
        -- sorted = [] → a ∈ [] 矛盾
        nomatch ha
    | case3 fuel v rest h_spb =>
        -- shouldProcessBefore(u, v) = true → result = u :: v :: rest = u :: sorted
        obtain ⟨p, m, s_, h_eq⟩ := h_before
        simp only [insertSorted, h_spb, ite_true]
        exact ⟨u :: p, m, s_, congrArg (u :: ·) h_eq⟩
    | case4 fuel v rest h_not_spb ih =>
        -- shouldProcessBefore(u, v) = false → result = v :: insertSorted u rest fuel
        simp only [insertSorted]
        rw [if_neg h_not_spb]
        obtain ⟨p, m, s_, h_eq⟩ := h_before
        -- v :: rest = p ++ [a] ++ m ++ [b] ++ s_
        cases p with
        | nil =>
            -- p = [], v :: rest = [a] ++ m ++ [b] ++ s_
            -- よって v = a, rest = m ++ [b] ++ s_
            simp only [List.nil_append, List.cons_append, List.cons.injEq] at h_eq
            obtain ⟨rfl, rfl⟩ := h_eq
            -- result = v :: insertSorted u (m ++ [b] ++ s_) fuel
            -- b は insertSorted の結果にも含まれる (insertSorted_perm より)
            have h_fuel' : fuel ≥ (m ++ [b] ++ s_).length := by
                simp only [List.length_cons] at h_fuel; omega
            have h_b_in_rest : b ∈ m ++ [b] ++ s_ :=
                List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
            have h_b_in_result : b ∈ insertSorted u (m ++ [b] ++ s_) fuel :=
                (insertSorted_perm u (m ++ [b] ++ s_) fuel).mem_iff.mpr
                    (List.mem_cons_of_mem u h_b_in_rest)
            obtain ⟨s1, s2, h_split⟩ := List.append_of_mem h_b_in_result
            refine ⟨[], s1, s2, ?_⟩
            rw [h_split]
            simp only [List.nil_append, List.cons_append, List.append_assoc]
        | cons v' p' =>
            -- p = v' :: p', v :: rest = (v' :: p') ++ [a] ++ m ++ [b] ++ s_
            -- よって v = v', rest = p' ++ [a] ++ m ++ [b] ++ s_
            simp only [List.cons_append, List.cons.injEq] at h_eq
            obtain ⟨rfl, rfl⟩ := h_eq
            have h_fuel' : fuel ≥ (p' ++ [a] ++ m ++ [b] ++ s_).length := by
                simp only [List.length_cons] at h_fuel; omega
            have ha' : a ∈ p' ++ [a] ++ m ++ [b] ++ s_ :=
                List.mem_append_left _ (List.mem_append_left _
                    (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)))
            have hb' : b ∈ p' ++ [a] ++ m ++ [b] ++ s_ :=
                List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
            obtain ⟨p'', m'', s_'', h_result⟩ :=
                ih h_fuel' ha' hb' ⟨p', m, s_, rfl⟩
            exact ⟨v :: p'', m'', s_'', congrArg (v :: ·) h_result⟩

-- ================================================================
-- sortFallingUnits 出力の反転ペアが tied であることの補題
-- ================================================================

/-- shouldProcessBefore(u,v)=false が sorted の全要素に対して成立するとき、
    insertSorted は u を末尾に追加する。 -/
theorem insertSorted_append_when_no_shouldProcessBefore (u : FallingUnit) (sorted : List FallingUnit)
        (fuel : Nat) (h_fuel : fuel ≥ sorted.length)
        (h_no_spb : ∀ v, v ∈ sorted → shouldProcessBefore u v = false) :
        insertSorted u sorted fuel = sorted ++ [u] := by
    induction sorted, fuel using insertSorted.induct u with
    | case1 sorted =>
        -- fuel = 0 → sorted = [] (h_fuel : 0 ≥ sorted.length)
        have h_empty : sorted = [] := by
            cases sorted with
            | nil => rfl
            | cons _ _ => simp only [List.length_cons, ge_iff_le, Nat.le_zero_eq, Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero, and_false] at h_fuel
        subst h_empty
        simp only [insertSorted, List.nil_append]
    | case2 =>
        -- sorted = [] → [u] = [] ++ [u]
        simp only [insertSorted, List.nil_append]
    | case3 fuel v rest h_spb =>
        -- shouldProcessBefore(u, v) = true → 矛盾 (h_no_spb v)
        simp_all only [List.mem_cons, true_or, Bool.false_eq_true]
    | case4 fuel v rest h_not_spb ih =>
        -- shouldProcessBefore(u, v) = false → v :: insertSorted u rest fuel
        simp only [insertSorted, h_not_spb, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.cons.injEq, true_and]
        have h_fuel' : fuel ≥ rest.length := by simp_all only [List.mem_cons, true_or, Bool.false_eq_true, not_false_eq_true, ge_iff_le, or_true, implies_true, forall_const, Nat.succ_eq_add_one, List.length_cons, Nat.add_le_add_iff_right, forall_eq_or_imp]
        have h_no_spb' : ∀ w, w ∈ rest → shouldProcessBefore u w = false := by
            intro w hw
            exact h_no_spb w (List.mem_cons_of_mem v hw)
        rw [ih h_fuel' h_no_spb']

/-- 分解表現 l = prefix ++ [a] ++ suffix ∧ b ∈ suffix → posIn a l < posIn b l -/
theorem posIn_lt_of_decomposition (a b : FallingUnit)
        (l : List FallingUnit) (h_nodup : l.Nodup)
        (prefix_ suffix_ : List FallingUnit)
        (h_eq : l = prefix_ ++ [a] ++ suffix_)
        (h_b_in : b ∈ suffix_) :
        posIn a l < posIn b l := by
    subst h_eq
    -- [a] ++ suffix_ = a :: suffix_ に変換して prefix_ に対する帰納法
    simp only [List.append_assoc, List.singleton_append] at h_nodup ⊢
    -- h_nodup : (prefix_ ++ (a :: suffix_)).Nodup
    -- ⊢ posIn a (prefix_ ++ (a :: suffix_)) < posIn b (prefix_ ++ (a :: suffix_))
    induction prefix_ with
    | nil =>
        -- l = a :: suffix_
        simp only [List.nil_append]
        unfold posIn
        simp only [List.findIdx_cons, eqPred_self, cond_true]
        -- ⊢ 0 < bif eqPred b a then 0 else suffix_.findIdx (eqPred b) + 1
        have h_a_notin : a ∉ suffix_ := (List.nodup_cons.mp h_nodup).1
        have h_b_ne_a : b ≠ a := fun h => h_a_notin (h ▸ h_b_in)
        have h_eq_pred : eqPred b a = false := by simp only [eqPred, Ne.symm h_b_ne_a, decide_false]
        simp only [h_eq_pred, cond_false, Nat.zero_lt_succ]
    | cons x rest ih =>
        -- l = x :: rest ++ (a :: suffix_)
        simp only [List.cons_append]
        -- ⊢ posIn a (x :: (rest ++ (a :: suffix_))) < posIn b (x :: (rest ++ (a :: suffix_)))
        have ⟨hx_notin, h_rest_nodup⟩ := List.nodup_cons.mp h_nodup
        -- x ≠ a, x ≠ b
        have h_x_ne_a : x ≠ a := by
            intro h; subst h
            exact hx_notin (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
        have h_x_ne_b : x ≠ b := by
            intro h; subst h
            exact hx_notin (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h_b_in))))
        -- posIn a (x :: l') = posIn a l' + 1 (x ≠ a → eqPred a x = false → findIdx skips x)
        -- posIn b (x :: l') = posIn b l' + 1 (x ≠ b → eqPred b x = false → findIdx skips x)
        have h_eqp_a : eqPred a x = false := by simp only [eqPred, h_x_ne_a, decide_false]
        have h_eqp_b : eqPred b x = false := by simp only [eqPred, h_x_ne_b, decide_false]
        show posIn a (x :: (rest ++ (a :: suffix_))) < posIn b (x :: (rest ++ (a :: suffix_)))
        unfold posIn
        simp only [List.findIdx_cons, h_eqp_a, h_eqp_b, cond_false]
        -- ⊢ findIdx ... + 1 < findIdx ... + 1 ← 実質的に posIn a l' + 1 < posIn b l' + 1
        -- IH: posIn a (rest ++ (a :: suffix_)) < posIn b (rest ++ (a :: suffix_))
        have h_ih := ih h_rest_nodup
        unfold posIn at h_ih
        omega

/-- (fU s).map mapFU と fU σ_shape のソート後 foldl 結果は等しい（汎用版）。
    Phase 1: l_mid を経由して sorted_foldl_pointwise_eq' を適用
    Phase 2: sortFallingUnits'(l_mid) と sortFallingUnits'(l2) の Perm 不変性を方角素性から証明。
    settle_foldl_eq / settle_foldl_eq_cw を統合する LayerPerm-generic 版。 -/
theorem settle_foldl_eq_generic (s : Shape) (obs : List Layer)
        (mapFU : FallingUnit → FallingUnit)
        (σ_qpos : QuarterPos → QuarterPos)
        (σ_shape : Shape)
        (h_any_in : ∀ u ∈ floatingUnits s,
            ∃ v ∈ floatingUnits σ_shape,
                (∀ p, (mapFU u).positions.any (· == p) = v.positions.any (· == p))
                ∧ (mapFU u).typeOrd = v.typeOrd)
        (h_any_mapFU : ∀ u p,
            (mapFU u).positions.any (· == σ_qpos p) = u.positions.any (· == p))
        (h_length : (floatingUnits s).length = (floatingUnits σ_shape).length) :
        Shape.ofLayers
          ((sortFallingUnits' ((floatingUnits s).map mapFU)).foldl
            (fun obs u => placeFallingUnit σ_shape obs u (landingDistance u obs)) obs) =
        Shape.ofLayers
          ((sortFallingUnits' (floatingUnits σ_shape)).foldl
            (fun obs u => placeFallingUnit σ_shape obs u (landingDistance u obs)) obs) := by
    set l1 := (floatingUnits s).map mapFU with hl1_def
    set l2 := floatingUnits σ_shape with hl2_def
    -- l_mid の構築: l1 と pointwise .any 等価で、l2 の要素からなるリスト
    open Classical in
    let g : FallingUnit → FallingUnit :=
        fun u => if h : u ∈ floatingUnits s
            then (h_any_in u h).choose
            else u
    have hg_mem : ∀ u ∈ floatingUnits s, g u ∈ floatingUnits σ_shape := by
        intro u hu
        show (if h : u ∈ floatingUnits s then (h_any_in u h).choose else u) ∈ _
        rw [dif_pos hu]
        exact (h_any_in u hu).choose_spec.1
    have hg_any : ∀ u ∈ floatingUnits s, ∀ p : QuarterPos,
            (mapFU u).positions.any (· == p) = (g u).positions.any (· == p) := by
        intro u hu
        show ∀ p, (mapFU u).positions.any (· == p) =
            (if h : u ∈ floatingUnits s then (h_any_in u h).choose else u).positions.any (· == p)
        rw [dif_pos hu]
        exact (h_any_in u hu).choose_spec.2.1
    have hg_type : ∀ u ∈ floatingUnits s,
            (mapFU u).typeOrd = (g u).typeOrd := by
        intro u hu
        show (mapFU u).typeOrd =
            (if h : u ∈ floatingUnits s then (h_any_in u h).choose else u).typeOrd
        rw [dif_pos hu]
        exact (h_any_in u hu).choose_spec.2.2
    set l_mid := (floatingUnits s).map g with hl_mid_def
    -- Phase 1: sortFallingUnits'(l1).foldl f obs = sortFallingUnits'(l_mid).foldl f obs
    have h_phase1 : (sortFallingUnits' l1).foldl
            (fun obs u => placeFallingUnit σ_shape obs u (landingDistance u obs)) obs =
            (sortFallingUnits' l_mid).foldl
            (fun obs u => placeFallingUnit σ_shape obs u (landingDistance u obs)) obs := by
        -- derived comparison: r(a,b) = fallingUnitOrd(mapFU(a), mapFU(b))
        let r := fun a b => fallingUnitOrd (mapFU a) (mapFU b)
        have h_r_eq_g : ∀ a ∈ floatingUnits s, ∀ b ∈ floatingUnits s,
                r a b = fallingUnitOrd (g a) (g b) := by
            intro a ha b hb
            exact fallingUnitOrd_eq_of_any_eq (hg_any a ha) (hg_any b hb)
                (minLayer_ext (hg_any a ha))
                (minLayer_ext (hg_any b hb))
                (hg_type a ha)
                (hg_type b hb)
        have h_sort_l1 : sortFallingUnits' l1 =
                ((floatingUnits s).mergeSort r).map mapFU := by
            simp only [sortFallingUnits', hl1_def]
            exact (List.map_mergeSort (f := mapFU) (fun a _ b _ => rfl)).symm
        have h_sort_lmid : sortFallingUnits' l_mid =
                ((floatingUnits s).mergeSort r).map g := by
            simp only [sortFallingUnits', hl_mid_def]
            exact (List.map_mergeSort (f := g) (fun a ha b hb => h_r_eq_g a ha b hb)).symm
        rw [h_sort_l1, h_sort_lmid]
        set base := (floatingUnits s).mergeSort r with hbase_def
        have h_foldl := foldl_pointwise_ext σ_shape
            (base.map mapFU) (base.map g) obs
            (by simp only [List.length_map])
            (fun i hi p => by
                simp only [List.length_map] at hi
                simp only [List.getElem_map]
                have h_mem : base[i] ∈ floatingUnits s :=
                    (List.mergeSort_perm ..).mem_iff.mp (List.getElem_mem hi)
                exact hg_any base[i] h_mem p)
        rw [h_foldl]
    -- l_mid は NoDup
    have h_nodup_mid : l_mid.Nodup := by
        rw [hl_mid_def]
        refine (List.nodup_map_iff_inj_on (floatingUnits_nodup s)).mpr ?_
        intro u1 hu1 u2 hu2 h_eq
        by_contra h_ne
        have ⟨p, hp⟩ := floatingUnit_positions_nonempty s u1 hu1
        have h1 : (mapFU u1).positions.any (· == σ_qpos p) = true := by
            rw [h_any_mapFU]; exact List.any_eq_true.mpr ⟨p, hp, BEq.rfl⟩
        have h2 : (mapFU u2).positions.any (· == σ_qpos p) = true := by
            rw [hg_any u2 hu2, ← h_eq, ← hg_any u1 hu1]; exact h1
        rw [h_any_mapFU] at h2
        obtain ⟨i, hi, h_eq_i⟩ := List.mem_iff_getElem.mp hu1
        obtain ⟨j, hj, h_eq_j⟩ := List.mem_iff_getElem.mp hu2
        subst h_eq_i; subst h_eq_j
        have h_ij : i ≠ j := fun h_eq_ij => h_ne (by subst h_eq_ij; rfl)
        exact absurd
            (by rw [List.any_eq_true] at h2 ⊢; exact h2 :
                ((floatingUnits s)[j]).positions.any (· == p) = true)
            (Bool.eq_false_iff.mp
                (floatingUnits_pairwise_disjoint s i j hi hj h_ij p
                    (List.any_eq_true.mpr ⟨p, hp, BEq.rfl⟩)))
    -- l_mid ⊆ fU(σ_shape)
    have h_sub_fU : ∀ u, u ∈ l_mid → u ∈ floatingUnits σ_shape := by
        intro u hu
        rw [hl_mid_def] at hu
        rw [List.mem_map] at hu
        obtain ⟨v, hv_mem, rfl⟩ := hu
        exact hg_mem v hv_mem
    -- l_mid ~ l2 (Perm)
    have h_l_mid_perm : l_mid.Perm l2 := by
        have h_len : l_mid.length = l2.length := by
            rw [hl_mid_def, hl2_def, List.length_map]
            exact h_length
        have h_subperm : l_mid.Subperm l2 :=
            List.subperm_of_subset h_nodup_mid (fun u hu => h_sub_fU u hu)
        exact h_subperm.perm_of_length_le (by omega)
    -- Phase 2: sortFallingUnits'(l_mid) = sortFallingUnits'(l2)
    have h_antisymm : ∀ a ∈ l_mid, ∀ b ∈ l_mid,
            fallingUnitOrd a b = true → fallingUnitOrd b a = true → a = b := by
        intro a ha b hb h_ab h_ba
        exact fallingUnitOrd_antisymm_of_floatingUnits_impl σ_shape a b
            (h_sub_fU a ha) (h_sub_fU b hb) h_ab h_ba
    have h_phase2 : sortFallingUnits' l_mid = sortFallingUnits' l2 := by
        simp only [sortFallingUnits']
        exact mergeSort_perm_eq (le := fallingUnitOrd)
            (fun _ _ _ => fallingUnitOrd_trans)
            fallingUnitOrd_total'
            h_l_mid_perm
            h_antisymm
    congr 1
    rw [← h_phase2]; exact h_phase1

/-- (fU s).map r180 と fU s.r180 のソート後 foldl 結果は等しい（rotate180 特化版）。
    settle_foldl_eq_generic の rotate180 インスタンス。 -/
theorem settle_foldl_eq (s : Shape) (obs : List Layer) :
        Shape.ofLayers
          ((sortFallingUnits' ((floatingUnits s).map FallingUnit.rotate180)).foldl
            (fun obs u => placeFallingUnit s.rotate180 obs u (landingDistance u obs)) obs) =
        Shape.ofLayers
          ((sortFallingUnits' (floatingUnits s.rotate180)).foldl
            (fun obs u => placeFallingUnit s.rotate180 obs u (landingDistance u obs)) obs) :=
    settle_foldl_eq_generic s obs FallingUnit.rotate180 QuarterPos.rotate180 s.rotate180
        (floatingUnit_any_in_rotate180 s)
        any_positions_rotate180
        (floatingUnits_length_rotate180 s)

-- ============================================================

end Gravity


