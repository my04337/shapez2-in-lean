-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity.ProcessWave

namespace Gravity

open Shape (layers_rotate180 clearPositions_rotate180)

-- process_rotate180 の本体
-- ============================================================

/-- 落下処理と 180° 回転は可換である。
    波動モデルでは layerCount 制約なしで成立する（foldl モデルでは ≥6L で偽だった） -/
theorem process_rotate180 (s : Shape) :
        (process s).map Shape.rotate180 = process s.rotate180 := by
    simp only [process]
    rw [processWave_rotate180_comm s]
    have h := option_bind_normalize_rotate180 (some (processWave s))
    simp only [Option.bind_some, Option.map_some] at h
    exact h

-- ============================================================
-- 90° 回転 (rotateCW) 等変性
-- ============================================================

-- 基盤定義
-- ============================================================

/-- FallingUnit を rotateCW する -/
private def FallingUnit.rotateCW : FallingUnit → FallingUnit
    | .cluster ps => .cluster (ps.map QuarterPos.rotateCW)
    | .pin p => .pin p.rotateCW

/-- FallingUnit.positions は rotateCW で等変 -/
private theorem FallingUnit.positions_rotateCW (u : FallingUnit) :
        u.rotateCW.positions = u.positions.map QuarterPos.rotateCW := by
    cases u with
    | cluster ps => rfl
    | pin p => rfl

/-- QuarterPos.rotateCW は layer を保持 -/
private theorem QuarterPos.rotateCW_layer (p : QuarterPos) :
        p.rotateCW.layer = p.layer := rfl

/-- QuarterPos.rotateCW の dir フィールド -/
private theorem QuarterPos.rotateCW_dir (p : QuarterPos) :
        p.rotateCW.dir = p.dir.rotateCW := rfl

/-- map が foldl min layer を保存する場合 (rotateCW 版) -/
private theorem foldl_map_layer_cw (l : List QuarterPos) (init : Nat) :
        (l.map QuarterPos.rotateCW).foldl (fun a q => min a q.layer) init =
        l.foldl (fun a q => min a q.layer) init := by
    simp only [List.foldl_map, QuarterPos.rotateCW_layer]

/-- FallingUnit.minLayer は rotateCW で不変 -/
private theorem FallingUnit.minLayer_rotateCW (u : FallingUnit) :
        u.rotateCW.minLayer = u.minLayer := by
    simp only [FallingUnit.minLayer, FallingUnit.positions_rotateCW]
    cases u.positions with
    | nil => rfl
    | cons p rest => exact foldl_map_layer_cw rest p.layer

/-- typeOrd は rotateCW で不変 -/
private theorem FallingUnit.typeOrd_rotateCW (u : FallingUnit) :
        u.rotateCW.typeOrd = u.typeOrd := by
    cases u <;> rfl

/-- sortGroup は rotateCW で不変 -/
private theorem FallingUnit.sortGroup_rotateCW (u : FallingUnit) :
        u.rotateCW.sortGroup = u.sortGroup := by
    simp only [FallingUnit.sortGroup, FallingUnit.minLayer_rotateCW,
        FallingUnit.typeOrd_rotateCW]

-- sortFallingUnits'_rotateCW は fallingUnitOrd（全順序）では不要
-- 代わりに sort_foldl_map_perm_bridge で foldl レベルの等価性を使う

-- パイプライン等変性
-- ============================================================

/-- Shape.ofLayers と map Layer.rotateCW の可換性 -/
private theorem ofLayers_rotateCW (ls : List Layer) :
        (Shape.ofLayers ls).map Shape.rotateCW =
        Shape.ofLayers (ls.map Layer.rotateCW) := by
    cases ls with
    | nil => rfl
    | cons l rest =>
        simp only [Shape.ofLayers, Option.map]
        congr 1

/-- Option Shape の normalize と rotateCW の可換性 -/
private theorem option_bind_normalize_rotateCW (os : Option Shape) :
        (os.bind Shape.normalize).map Shape.rotateCW =
        (os.map Shape.rotateCW).bind Shape.normalize := by
    cases os with
    | none => rfl
    | some s =>
        simp only [Option.bind, Option.map]
        exact s.normalize_map_layers Layer.rotateCW Layer.isEmpty_rotateCW

/-- isOccupied は rotateCW で等変 -/
private theorem isOccupied_rotateCW (obs : List Layer) (layer : Nat) (d : Direction) :
        isOccupied (obs.map Layer.rotateCW) layer (d.rotateCW) =
        isOccupied obs layer d := by
    simp only [isOccupied, List.getElem?_map]
    cases obs[layer]? with
    | none => rfl
    | some l => simp only [Option.map_some, QuarterPos.getDir_rotateCW]

/-- landed 判定は rotateCW で不変 -/
private theorem landed_rotateCW (positions : List QuarterPos) (obs : List Layer) (d : Nat) :
        (positions.map QuarterPos.rotateCW).any (fun p =>
            let newLayer := p.layer - d
            newLayer == 0 || isOccupied (obs.map Layer.rotateCW) (newLayer - 1) p.dir) =
        positions.any (fun p =>
            let newLayer := p.layer - d
            newLayer == 0 || isOccupied obs (newLayer - 1) p.dir) := by
    induction positions with
    | nil => rfl
    | cons p rest ih =>
        simp only [List.map, List.any]
        rw [ih]
        congr 1
        simp only [QuarterPos.rotateCW]
        congr 1
        exact isOccupied_rotateCW obs _ _

/-- landingDistance.check は rotateCW で不変 -/
private theorem landingDistance_check_rotateCW (positions : List QuarterPos) (obs : List Layer)
        (maxDrop d fuel : Nat) :
        landingDistance.check (obs.map Layer.rotateCW) (positions.map QuarterPos.rotateCW) maxDrop d fuel =
        landingDistance.check obs positions maxDrop d fuel := by
    induction fuel generalizing d with
    | zero => rfl
    | succ n ih =>
        simp only [landingDistance.check]
        split
        · rfl
        · rw [landed_rotateCW]
          split
          · rfl
          · exact ih (d + 1)

/-- landingDistance は rotateCW で不変 -/
private theorem landingDistance_rotateCW (u : FallingUnit) (obs : List Layer) :
        landingDistance u.rotateCW (obs.map Layer.rotateCW) = landingDistance u obs := by
    simp only [landingDistance]
    simp only [FallingUnit.minLayer_rotateCW, FallingUnit.positions_rotateCW]
    exact landingDistance_check_rotateCW u.positions obs u.minLayer 1 (u.minLayer + 1)

/-- setDir と rotateCW の可換性（一般版） -/
private theorem setDir_rotateCW (l : Layer) (d : Direction) (q : Quarter) :
        (QuarterPos.setDir l d q).rotateCW =
        QuarterPos.setDir (l.rotateCW) (d.rotateCW) q := by
    cases d <;> rfl

/-- replicate Layer.empty の map rotateCW -/
private theorem replicate_empty_rotateCW (n : Nat) :
        (List.replicate n Layer.empty).map Layer.rotateCW = List.replicate n Layer.empty := by
    induction n with
    | zero => rfl
    | succ n ih =>
        show Layer.empty.rotateCW :: (List.replicate n Layer.empty).map Layer.rotateCW =
             Layer.empty :: List.replicate n Layer.empty
        rw [ih]
        rfl

/-- placeQuarter は rotateCW で等変 -/
private theorem placeQuarter_rotateCW (layers : List Layer) (lay : Nat) (d : Direction) (q : Quarter) :
        (placeQuarter layers lay d q).map Layer.rotateCW =
        placeQuarter (layers.map Layer.rotateCW) lay (d.rotateCW) q := by
    simp only [placeQuarter, List.length_map]
    if h : lay < layers.length then
        simp only [h, ↓reduceIte, List.getElem?_map]
        cases layers[lay]? with
        | none => rfl
        | some l => simp only [Option.map_some]; rw [List.map_set, setDir_rotateCW]
    else
        simp only [h, ↓reduceIte]
        have hext : List.map Layer.rotateCW layers ++ List.replicate (lay + 1 - layers.length) Layer.empty =
            (layers ++ List.replicate (lay + 1 - layers.length) Layer.empty).map Layer.rotateCW := by
            rw [List.map_append, replicate_empty_rotateCW]
        rw [hext, List.getElem?_map]
        cases (layers ++ List.replicate (lay + 1 - layers.length) Layer.empty)[lay]? with
        | none => rfl
        | some l =>
            simp only [Option.map_some]
            rw [List.map_set, setDir_rotateCW]

/-- placeFallingUnit は rotateCW で等変 -/
private theorem placeFallingUnit_rotateCW (origShape : Shape) (obs : List Layer)
        (u : FallingUnit) (dropDist : Nat) :
        (placeFallingUnit origShape obs u dropDist).map Layer.rotateCW =
        placeFallingUnit origShape.rotateCW (obs.map Layer.rotateCW) u.rotateCW dropDist := by
    simp only [placeFallingUnit, FallingUnit.positions_rotateCW]
    suffices h : ∀ (acc : List Layer),
        (u.positions.foldl (fun obs p =>
            match p.getQuarter origShape with
            | some q => placeQuarter obs (p.layer - dropDist) p.dir q
            | none => obs) acc).map Layer.rotateCW =
        (u.positions.map QuarterPos.rotateCW).foldl (fun obs p =>
            match p.getQuarter origShape.rotateCW with
            | some q => placeQuarter obs (p.layer - dropDist) p.dir q
            | none => obs) (acc.map Layer.rotateCW) from h obs
    intro acc
    induction u.positions generalizing acc with
    | nil => rfl
    | cons p rest ih =>
        simp only [List.foldl_cons, List.map_cons]
        have hstep : (match p.getQuarter origShape with
            | some q => placeQuarter acc (p.layer - dropDist) p.dir q
            | none => acc).map Layer.rotateCW =
            (match p.rotateCW.getQuarter origShape.rotateCW with
            | some q => placeQuarter (acc.map Layer.rotateCW)
                (p.rotateCW.layer - dropDist) p.rotateCW.dir q
            | none => acc.map Layer.rotateCW) := by
            rw [QuarterPos.getQuarter_rotateCW]
            cases p.getQuarter origShape with
            | none => rfl
            | some q =>
                rw [QuarterPos.rotateCW_layer, QuarterPos.rotateCW_dir]
                exact placeQuarter_rotateCW ..
        rw [ih, hstep]

/-- flatMap + map の交換則 (rotateCW 版) -/
private theorem flatMap_map_rotateCW (units : List FallingUnit) :
        (units.map FallingUnit.rotateCW).flatMap FallingUnit.positions =
        (units.flatMap FallingUnit.positions).map QuarterPos.rotateCW := by
    simp only [List.flatMap_map, List.map_flatMap, FallingUnit.positions_rotateCW]

/-- sorted.foldl (placeFallingUnit + landingDistance) の rotateCW 等変性 -/
private theorem foldl_place_rotateCW (s : Shape) (sorted : List FallingUnit) (obs : List Layer) :
        (sorted.foldl (fun obs u =>
            let d := landingDistance u obs
            placeFallingUnit s obs u d
        ) obs).map Layer.rotateCW =
        (sorted.map FallingUnit.rotateCW).foldl (fun obs u =>
            let d := landingDistance u obs
            placeFallingUnit s.rotateCW obs u d
        ) (obs.map Layer.rotateCW) := by
    induction sorted generalizing obs with
    | nil => rfl
    | cons u rest ih =>
        simp only [List.foldl_cons, List.map_cons]
        rw [ih]
        congr 1
        rw [landingDistance_rotateCW, placeFallingUnit_rotateCW]

-- placeLDGroups の rotateCW 等変性
-- ============================================================

/-- takeWhile と map の可換性（述語が f を通して対応する場合）- Facade 内部用 -/
private theorem takeWhile_map_comm {f : α → β} {p : β → Bool} {q : α → Bool}
        (h : ∀ x, p (f x) = q x) (l : List α) :
        (l.map f).takeWhile p = (l.takeWhile q).map f := by
    induction l with
    | nil => rfl
    | cons a t ih =>
        simp only [List.map_cons, List.takeWhile_cons]; rw [h]; split <;> simp [ih]

/-- dropWhile と map の可換性（述語が f を通して対応する場合）- Facade 内部用 -/
private theorem dropWhile_map_comm {f : α → β} {p : β → Bool} {q : α → Bool}
        (h : ∀ x, p (f x) = q x) (l : List α) :
        (l.map f).dropWhile p = (l.dropWhile q).map f := by
    induction l with
    | nil => rfl
    | cons a t ih =>
        simp only [List.map_cons, List.dropWhile_cons]; rw [h]; split <;> simp [ih]

/-- 固定着地距離 d での foldl placeFallingUnit の rotateCW 等変性 -/
private theorem foldl_place_fixed_d_rotateCW (s : Shape) (group : List FallingUnit)
        (obs : List Layer) (d : Nat) :
        (group.foldl (fun acc fu => placeFallingUnit s acc fu d) obs).map Layer.rotateCW =
        (group.map FallingUnit.rotateCW).foldl
            (fun acc fu => placeFallingUnit s.rotateCW acc fu d)
            (obs.map Layer.rotateCW) := by
    induction group generalizing obs with
    | nil => rfl
    | cons u rest ih =>
        simp only [List.foldl_cons, List.map_cons]
        rw [ih]; congr 1; exact placeFallingUnit_rotateCW s obs u d

/-- placeLDGroups は rotateCW で等変である -/
private theorem placeLDGroups_rotateCW (s : Shape) (sorted : List FallingUnit) (obs : List Layer) :
        (placeLDGroups s sorted obs).map Layer.rotateCW =
        placeLDGroups s.rotateCW (sorted.map FallingUnit.rotateCW)
            (obs.map Layer.rotateCW) := by
    suffices h : ∀ (n : Nat) (sorted : List FallingUnit) (obs : List Layer),
        sorted.length ≤ n →
        (placeLDGroups s sorted obs).map Layer.rotateCW =
        placeLDGroups s.rotateCW (sorted.map FallingUnit.rotateCW)
            (obs.map Layer.rotateCW) from
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
            have hld : landingDistance first.rotateCW (obs.map Layer.rotateCW) =
                    landingDistance first obs :=
                landingDistance_rotateCW first obs
            conv_rhs =>
                rw [show first.rotateCW :: rest.map FallingUnit.rotateCW =
                    (first :: rest).map FallingUnit.rotateCW from rfl]
                rw [dropWhile_map_comm (fun u => by rw [landingDistance_rotateCW, hld])]
                rw [takeWhile_map_comm (fun u => by rw [landingDistance_rotateCW, hld])]
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
            exact foldl_place_fixed_d_rotateCW s _ obs _

-- 浮遊位置のメンバーシップ CW 等変性
-- ============================================================

/-- List.map QuarterPos.rotateCW 後の .any (rotateCW 版) -/
theorem any_map_rotateCW_beq (ps : List QuarterPos) (p : QuarterPos) :
        (ps.map QuarterPos.rotateCW).any (· == p) =
        ps.any (· == p.rotateCCW) := by
    have h := LayerPerm.list_any_map .rotateCW ps p.rotateCCW
    simpa only [QuarterPos.rotateCCW_rotateCW] using h

-- floatingUnit_any_in_rotateCW
-- ============================================================

/-- floatingUnits s の各ユニットに対し、floatingUnits s.rotateCW に
    .any 等価かつ型が一致するクラスタユニットが存在する -/
private theorem floatingUnit_any_in_rotateCW_cluster (s : Shape) (ps : List QuarterPos)
        (hu : FallingUnit.cluster ps ∈ floatingUnits s) :
        ∃ v ∈ floatingUnits s.rotateCW,
            (∀ p, (FallingUnit.cluster ps).rotateCW.positions.any (· == p) = v.positions.any (· == p))
            ∧ (FallingUnit.cluster ps).rotateCW.typeOrd = v.typeOrd := by
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
        -- pos.rotateCW は s.rotateCW で bondable
        have h_bond_cw : match pos.rotateCW.getQuarter s.rotateCW with
                | some q => q.canFormBond = true | none => False := by
            rw [QuarterPos.getQuarter_rotateCW]
            obtain ⟨q, hq, hb⟩ := h_bondable; rw [hq]; exact hb
        have h_layer_cw : pos.rotateCW.layer < s.rotateCW.layerCount := by
            rw [Shape.layerCount_rotateCW, QuarterPos.rotateCW_layer]; exact h_layer
        have h_covers := allStructuralClustersList_covers s.rotateCW pos.rotateCW
            h_layer_cw h_bond_cw
        rw [List.any_eq_true] at h_covers
        obtain ⟨c', hc'_mem, hc'_any⟩ := h_covers
        obtain ⟨pos', hc'_eq, _, _⟩ :=
            allStructuralClustersList_is_structuralClusterList s.rotateCW c' hc'_mem
        -- c' の .any と (ps.map rotateCW) の .any は一致する
        have h_any_eq : ∀ (q : QuarterPos),
                c'.any (· == q) = (ps.map QuarterPos.rotateCW).any (· == q) := by
            intro q
            have h_sc : ps.any (· == q.rotateCCW) =
                    (structuralClusterList s.rotateCW pos.rotateCW).any (· == q) := by
                have h := mem_structuralCluster_rotateCW s pos q.rotateCCW
                simp only [QuarterPos.rotateCCW_rotateCW, structuralCluster,
                    List.mem_toFinset] at h
                rw [hps_eq]
                exact Bool.eq_iff_iff.mpr
                    ((any_beq_iff_mem _ _).trans (h.trans (any_beq_iff_mem _ _).symm))
            rw [hc'_eq]
            rw [any_map_rotateCW_beq]
            rw [h_sc]
            -- 同じ連結成分の一意性
            have h_pos_cw_in_c' : (structuralClusterList s.rotateCW pos').any (· == pos.rotateCW) = true := by
                rw [← hc'_eq]; exact hc'_any
            cases hq : (structuralClusterList s.rotateCW pos').any (· == q) with
            | true =>
                have h_q_reach := structuralClusterList_sound s.rotateCW pos' q hq
                have h_q_from_pos := GenericReachable.trans
                    ((structuralClusterList_sound s.rotateCW pos' pos.rotateCW h_pos_cw_in_c').symm
                        (fun a b => isStructurallyBonded_symm s.rotateCW a b))
                    h_q_reach
                symm; exact structuralClusterList_complete s.rotateCW pos.rotateCW q
                    (by rw [Shape.layerCount_rotateCW]; omega)
                    h_q_from_pos
            | false =>
                symm
                cases hq2 : (structuralClusterList s.rotateCW pos.rotateCW).any (· == q) with
                | false => rfl
                | true =>
                    exfalso
                    have h_pos'_in_sc : (structuralClusterList s.rotateCW pos.rotateCW).any (· == pos') = true :=
                        structuralClusterList_complete s.rotateCW pos.rotateCW pos'
                            (by rw [Shape.layerCount_rotateCW]; omega)
                            ((structuralClusterList_sound s.rotateCW pos' pos.rotateCW h_pos_cw_in_c').symm
                                (fun a b => isStructurallyBonded_symm s.rotateCW a b))
                    have := structuralClusterList_complete s.rotateCW pos' q
                        (by rw [Shape.layerCount_rotateCW]; omega)
                        (GenericReachable.trans
                            ((structuralClusterList_sound s.rotateCW pos.rotateCW pos' h_pos'_in_sc).symm
                                (fun a b => isStructurallyBonded_symm s.rotateCW a b))
                            (structuralClusterList_sound s.rotateCW pos.rotateCW q hq2))
                    rw [hq] at this; exact Bool.noConfusion this
        -- c' が浮遊であることを示す
        have h_floating : c'.all (fun p => !((groundedPositionsList s.rotateCW).any (· == p))) = true := by
            rw [List.all_eq_true]
            intro q hq_mem
            have hq_any : c'.any (· == q) = true :=
                List.any_eq_true.mpr ⟨q, hq_mem, beq_self_eq_true q⟩
            rw [h_any_eq] at hq_any
            rw [any_map_rotateCW_beq] at hq_any
            rw [List.all_eq_true] at hps_floating
            have h_qr_in_ps : q.rotateCCW ∈ ps := by
                rw [List.any_eq_true] at hq_any
                obtain ⟨x, hx_mem, hx_beq⟩ := hq_any
                exact eq_of_beq hx_beq ▸ hx_mem
            have h_ungrounded := hps_floating q.rotateCCW h_qr_in_ps
            simp only [Bool.not_eq_true'] at h_ungrounded ⊢
            have h_gp : (groundedPositionsList s).any (· == q.rotateCCW) =
                    (groundedPositionsList s.rotateCW).any (· == q) := by
                have h := mem_groundedPositions_rotateCW s q.rotateCCW
                simp only [QuarterPos.rotateCCW_rotateCW, groundedPositions,
                    List.mem_toFinset] at h
                exact Bool.eq_iff_iff.mpr
                    ((any_beq_iff_mem _ _).trans (h.trans (any_beq_iff_mem _ _).symm))
            rw [← h_gp]; exact h_ungrounded
        have h_v_mem : FallingUnit.cluster c' ∈ floatingUnits s.rotateCW := by
            rw [floatingUnits_eq_append, List.mem_append]
            exact .inl (List.mem_map.mpr ⟨c', List.mem_filter.mpr ⟨hc'_mem, h_floating⟩, rfl⟩)
        exact ⟨.cluster c', h_v_mem, ⟨fun p => by
            simp only [FallingUnit.rotateCW, FallingUnit.positions]
            exact (h_any_eq p).symm, rfl⟩⟩
    | inr h_pin =>
        rw [List.mem_map] at h_pin
        obtain ⟨_, _, h_eq⟩ := h_pin
        exact absurd h_eq (by intro h'; exact FallingUnit.noConfusion h')

/-- floatingUnits s の各ユニットに対し、floatingUnits s.rotateCW に
    .any 等価かつ型が一致するピンユニットが存在する -/
private theorem floatingUnit_any_in_rotateCW_pin (s : Shape) (p : QuarterPos)
        (hu : FallingUnit.pin p ∈ floatingUnits s) :
        ∃ v ∈ floatingUnits s.rotateCW,
            (∀ q, (FallingUnit.pin p).rotateCW.positions.any (· == q) = v.positions.any (· == q))
            ∧ (FallingUnit.pin p).rotateCW.typeOrd = v.typeOrd := by
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
        have h_pin_cw : p.rotateCW ∈ allIsolatedPins s.rotateCW := by
            unfold allIsolatedPins
            rw [allValid_rotateCW]
            rw [List.mem_filter]
            constructor
            · unfold allIsolatedPins at hp_pins
              have h_p_valid := (List.mem_filter.mp hp_pins).1
              have h_layer : p.layer < s.layerCount :=
                  (allValid_any_iff_layer' s p).mp
                      (List.any_eq_true.mpr ⟨p, h_p_valid, BEq.rfl⟩)
              have h_any := (allValid_any_iff_layer' s p.rotateCW).mpr h_layer
              rw [List.any_eq_true] at h_any
              obtain ⟨y, hy, hye⟩ := h_any; exact eq_of_beq hye ▸ hy
            · rw [QuarterPos.getQuarter_rotateCW]
              unfold allIsolatedPins at hp_pins
              exact (List.mem_filter.mp hp_pins).2
        have h_ungrounded_bool : (groundedPositionsList s.rotateCW).any (· == p.rotateCW) = false := by
            have h_gp : (groundedPositionsList s).any (· == p) =
                    (groundedPositionsList s.rotateCW).any (· == p.rotateCW) := by
                have h := mem_groundedPositions_rotateCW s p
                simp only [groundedPositions, List.mem_toFinset] at h
                exact Bool.eq_iff_iff.mpr
                    ((any_beq_iff_mem _ _).trans (h.trans (any_beq_iff_mem _ _).symm))
            rw [← h_gp]; exact hp_floating_bool
        have h_v_mem : FallingUnit.pin p.rotateCW ∈ floatingUnits s.rotateCW := by
            rw [floatingUnits_eq_append, List.mem_append]
            refine .inr (List.mem_map.mpr ⟨p.rotateCW, ?_, rfl⟩)
            rw [List.mem_filter]
            refine ⟨h_pin_cw, ?_⟩
            simp only [Bool.not_eq_true']
            exact h_ungrounded_bool
        exact ⟨.pin p.rotateCW, h_v_mem, ⟨fun q => rfl, rfl⟩⟩

/-- floatingUnits s の各ユニットに対し、floatingUnits s.rotateCW に
    .any 等価かつ型が一致するユニットが存在する -/
private theorem floatingUnit_any_in_rotateCW (s : Shape) (u : FallingUnit)
        (hu : u ∈ floatingUnits s) :
        ∃ v ∈ floatingUnits s.rotateCW,
            (∀ p, u.rotateCW.positions.any (· == p) = v.positions.any (· == p))
            ∧ u.rotateCW.typeOrd = v.typeOrd := by
    cases u with
    | cluster ps =>
        simpa using floatingUnit_any_in_rotateCW_cluster s ps hu
    | pin p =>
        simpa using floatingUnit_any_in_rotateCW_pin s p hu

-- ============================================================
-- floatingUnit_any_in_rotateCW の逆方向
-- ============================================================

/-- BEq と rotateCW の交換: q.rotateCW == p ↔ q == p.rotateCCW -/
private theorem beq_rotateCW_iff (q p : QuarterPos) :
        (q.rotateCW == p) = (q == p.rotateCCW) := by
    cases hqp : (q == p.rotateCCW) with
    | false =>
        simp only [beq_eq_false_iff_ne, ne_eq] at hqp ⊢
        intro h; exact hqp (by rw [← h, QuarterPos.rotateCW_rotateCCW])
    | true =>
        simp only [beq_iff_eq] at hqp ⊢
        rw [hqp, QuarterPos.rotateCCW_rotateCW]

/-- BEq と rotate180 の交換: q.rotate180 == p ↔ q == p.rotate180 -/
private theorem beq_rotate180_iff (q p : QuarterPos) :
        (q.rotate180 == p) = (q == p.rotate180) := by
    cases hqp : (q == p.rotate180) with
    | false =>
        simp only [beq_eq_false_iff_ne, ne_eq] at hqp ⊢
        intro h; exact hqp (by rw [← h, QuarterPos.rotate180_rotate180])
    | true =>
        simp only [beq_iff_eq] at hqp ⊢
        rw [hqp, QuarterPos.rotate180_rotate180]

/-- rotateCCW ∘ rotate180 = rotateCW -/
private theorem QuarterPos.rotateCCW_rotate180 (p : QuarterPos) :
        p.rotateCCW.rotate180 = p.rotateCW := by
    simp only [QuarterPos.rotateCCW, QuarterPos.rotate180, QuarterPos.rotateCW,
        Direction.rotateCCW, Direction.rotate180, Direction.rotateCW]
    cases p.dir <;> rfl

/-- (l.map rotateCW).any (· == p) = l.any (· == p.rotateCCW) -/
private theorem any_map_rotateCW (l : List QuarterPos) (p : QuarterPos) :
        (l.map QuarterPos.rotateCW).any (· == p) = l.any (· == p.rotateCCW) := by
    rw [List.any_map]; congr 1; ext q; exact beq_rotateCW_iff q p

/-- (l.map rotate180).any (· == p) = l.any (· == p.rotate180) -/
private theorem any_map_rotate180 (l : List QuarterPos) (p : QuarterPos) :
        (l.map QuarterPos.rotate180).any (· == p) = l.any (· == p.rotate180) := by
    rw [List.any_map]; congr 1; ext q; exact beq_rotate180_iff q p

/-- floatingUnit_any_in_rotateCW の逆方向:
    floatingUnits s.rotateCW の各 v に対し floatingUnits s に .any 等価な u.rotateCW が存在。
    証明: floatingUnit_any_in_rotateCW を s.rotateCW に適用して
    floatingUnits(s.rotate180) の w を得て、floatingUnit_any_in_rotate180 を
    s.rotate180 に適用して floatingUnits(s) の x にチェインする。 -/
private theorem floatingUnit_any_in_rotateCW_rev (s : Shape) (v : FallingUnit)
        (hv : v ∈ floatingUnits s.rotateCW) :
        ∃ u ∈ floatingUnits s,
            (∀ p, u.rotateCW.positions.any (· == p) = v.positions.any (· == p))
            ∧ u.rotateCW.typeOrd = v.typeOrd := by
    -- Step 1: v ∈ floatingUnits(s.rotateCW) → ∃ w ∈ floatingUnits(s.rotate180)
    have h_eq : s.rotateCW.rotateCW = s.rotate180 :=
        (Shape.rotate180_eq_rotateCW_rotateCW s).symm
    obtain ⟨w, hw_mem, hw_any, hw_type⟩ := floatingUnit_any_in_rotateCW s.rotateCW v hv
    rw [h_eq] at hw_mem
    -- Step 2: w ∈ floatingUnits(s.rotate180) → ∃ x ∈ floatingUnits(s.rotate180.rotate180) = floatingUnits(s)
    obtain ⟨x, hx_mem, hx_any, hx_type⟩ := floatingUnit_any_in_rotate180 s.rotate180 w hw_mem
    rw [Shape.rotate180_rotate180] at hx_mem
    -- Step 3: chain .any properties via rewrite
    refine ⟨x, hx_mem, fun p => ?_, ?_⟩
    · -- x.rotateCW.positions.any (· == p) = v.positions.any (· == p)
      -- Chain: x.rCW[p] → x[p.rCCW] → w.r180[p.rCCW] → w[p.rCCW.r180=p.rCW]
      --        → v.rCW[p.rCW] → v[p.rCW.rCCW=p]
      rw [FallingUnit.positions_rotateCW, any_map_rotateCW,
          ← hx_any p.rotateCCW,
          FallingUnit.positions_rotate180, any_map_rotate180,
          QuarterPos.rotateCCW_rotate180,
          ← hw_any p.rotateCW,
          FallingUnit.positions_rotateCW, any_map_rotateCW,
          QuarterPos.rotateCW_rotateCCW]
    · -- typeOrd: chain x.rCW.typeOrd = x.typeOrd = w.r180.typeOrd = w.typeOrd = v.rCW.typeOrd = v.typeOrd
      rw [FallingUnit.typeOrd_rotateCW, ← hx_type,
          FallingUnit.typeOrd_rotate180, ← hw_type,
          FallingUnit.typeOrd_rotateCW]

-- ============================================================
-- settling ↔ settling.map FU.rotateCW の .any 対応（将来の
-- axiom 除去で再利用する想定の per-FU 対応補題群）
-- ============================================================

-- 注: `foldl_min_fu_le_init` と `foldl_min_fu_le_mem` は 2026-04-23 に
-- `CommExt/FloatUnits.lean` に public 版として移設。`ProcessWave.lean` の
-- `waveStep_grounding_mono` でも利用するため。本ファイルでは `foldl_min_fu_eq_init_or_mem` のみ保持。

/-- foldl min の結果は init か l 内の要素の minLayer のいずれかに等しい -/
private theorem foldl_min_fu_eq_init_or_mem (l : List FallingUnit) (init : Nat) :
        l.foldl (fun acc u => min acc u.minLayer) init = init ∨
        ∃ u ∈ l, l.foldl (fun acc u => min acc u.minLayer) init = u.minLayer := by
    induction l generalizing init with
    | nil => exact .inl rfl
    | cons x xs ih =>
        simp only [List.foldl_cons]
        rcases ih (min init x.minLayer) with heq | ⟨u, hu, heq⟩
        · rcases le_total init x.minLayer with h | h
          · left; rw [heq]; exact min_eq_left h
          · right; exact ⟨x, .head _, by rw [heq]; exact min_eq_right h⟩
        · right; exact ⟨u, .tail _ hu, heq⟩

/-- minML = minML' : floatingUnits の最小 minLayer は rotateCW で不変。
    per-FU 双方向対応 (floatingUnit_any_in_rotateCW / _rev) が minLayer を保存するため。 -/
private theorem minML_eq_rotateCW (s : Shape)
        (h : (floatingUnits s).isEmpty = false) :
        let fus := floatingUnits s
        let minML := fus.tail.foldl (fun acc u => min acc u.minLayer)
            (fus.head?.map FallingUnit.minLayer |>.getD 0)
        let fus' := floatingUnits s.rotateCW
        let minML' := fus'.tail.foldl (fun acc u => min acc u.minLayer)
            (fus'.head?.map FallingUnit.minLayer |>.getD 0)
        minML = minML' := by
    intro fus minML fus' minML'
    have h' : (floatingUnits s.rotateCW).isEmpty = false := by
        rw [← floatingUnits_isEmpty_rotateCW]; exact h
    -- minML と minML' は fold-min なので、全要素以下かつ要素の1つに等しい
    -- 両リストの要素は minLayer について双対応 → 最小値は同じ
    -- 以下、minML ≤ minML' と minML' ≤ minML を示す
    --
    -- 先に fus, fus' 分解表現
    have h_fus_cases : ∃ x xs, fus = x :: xs := by
        cases hfus : fus with
        | nil =>
            have : (floatingUnits s).isEmpty = true := by
                show fus.isEmpty = true
                rw [hfus]; rfl
            rw [this] at h; exact Bool.noConfusion h
        | cons x xs => exact ⟨x, xs, rfl⟩
    have h_fus'_cases : ∃ x xs, fus' = x :: xs := by
        cases hfus' : fus' with
        | nil =>
            have : (floatingUnits s.rotateCW).isEmpty = true := by
                show fus'.isEmpty = true
                rw [hfus']; rfl
            rw [this] at h'; exact Bool.noConfusion h'
        | cons x xs => exact ⟨x, xs, rfl⟩
    obtain ⟨x, xs, hfus_eq⟩ := h_fus_cases
    obtain ⟨x', xs', hfus'_eq⟩ := h_fus'_cases
    -- 両 fold は同じ構造: head.minLayer を init として tail を fold
    have hminML_eq : minML = fus.foldl (fun acc u => min acc u.minLayer) x.minLayer := by
        show fus.tail.foldl (fun acc u => min acc u.minLayer)
            (fus.head?.map FallingUnit.minLayer |>.getD 0) = _
        rw [hfus_eq]; simp [List.foldl_cons]
    have hminML'_eq : minML' = fus'.foldl (fun acc u => min acc u.minLayer) x'.minLayer := by
        show fus'.tail.foldl (fun acc u => min acc u.minLayer)
            (fus'.head?.map FallingUnit.minLayer |>.getD 0) = _
        rw [hfus'_eq]; simp [List.foldl_cons]
    rw [hminML_eq, hminML'_eq]
    -- 両方向対応で minML_min 同値を示す
    apply Nat.le_antisymm
    · -- fus-fold min ≤ fus'-fold min
      -- fus'-fold は x'.minLayer か fus' 内の要素の minLayer
      -- その要素 v には対応 u ∈ fus が存在し u.minLayer = v.minLayer
      -- ∴ fus-fold ≤ u.minLayer = v.minLayer ≤ fus'-fold の下界
      rcases foldl_min_fu_eq_init_or_mem fus' x'.minLayer with heq | ⟨v, hv_fus', heq⟩
      · rw [heq]
        -- x' ∈ fus', 対応 u ∈ fus
        have hx'_fus' : x' ∈ fus' := by rw [hfus'_eq]; exact .head _
        obtain ⟨u, hu_fus, hu_any, _⟩ := floatingUnit_any_in_rotateCW_rev s x' hx'_fus'
        have h_ml : u.rotateCW.minLayer = x'.minLayer := minLayer_ext hu_any
        rw [FallingUnit.minLayer_rotateCW] at h_ml
        exact h_ml ▸ foldl_min_fu_le_mem fus x.minLayer hu_fus
      · rw [heq]
        obtain ⟨u, hu_fus, hu_any, _⟩ := floatingUnit_any_in_rotateCW_rev s v hv_fus'
        have h_ml : u.rotateCW.minLayer = v.minLayer := minLayer_ext hu_any
        rw [FallingUnit.minLayer_rotateCW] at h_ml
        exact h_ml ▸ foldl_min_fu_le_mem fus x.minLayer hu_fus
    · -- fus'-fold min ≤ fus-fold min (対称)
      rcases foldl_min_fu_eq_init_or_mem fus x.minLayer with heq | ⟨u, hu_fus, heq⟩
      · rw [heq]
        have hx_fus : x ∈ fus := by rw [hfus_eq]; exact .head _
        obtain ⟨v, hv_fus', hv_any, _⟩ := floatingUnit_any_in_rotateCW s x hx_fus
        have h_ml : x.rotateCW.minLayer = v.minLayer := minLayer_ext hv_any
        rw [FallingUnit.minLayer_rotateCW] at h_ml
        exact h_ml ▸ foldl_min_fu_le_mem fus' x'.minLayer hv_fus'
      · rw [heq]
        obtain ⟨v, hv_fus', hv_any, _⟩ := floatingUnit_any_in_rotateCW s u hu_fus
        have h_ml : u.rotateCW.minLayer = v.minLayer := minLayer_ext hv_any
        rw [FallingUnit.minLayer_rotateCW] at h_ml
        exact h_ml ▸ foldl_min_fu_le_mem fus' x'.minLayer hv_fus'

/-- settling' の全体 .any カバレッジは settling.map FU.rotateCW と一致する。
    floatingUnit_any_in_rotateCW / _rev の双方向対応から導出。 -/
private theorem settling_positions_any_rotateCW (s : Shape)
        (h : (floatingUnits s).isEmpty = false) :
        let fus := floatingUnits s
        let minML := fus.tail.foldl (fun acc u => min acc u.minLayer)
            (fus.head?.map FallingUnit.minLayer |>.getD 0)
        let settling := fus.filter fun u => u.minLayer == minML
        let settlingPos := settling.flatMap FallingUnit.positions
        let fus' := floatingUnits s.rotateCW
        let minML' := fus'.tail.foldl (fun acc u => min acc u.minLayer)
            (fus'.head?.map FallingUnit.minLayer |>.getD 0)
        let settling' := fus'.filter fun u => u.minLayer == minML'
        let settlingPos' := settling'.flatMap FallingUnit.positions
        ∀ p, settlingPos'.any (· == p) = (settlingPos.map QuarterPos.rotateCW).any (· == p) := by
    intro fus minML settling settlingPos fus' minML' settling' settlingPos' p
    rw [any_map_rotateCW_beq]
    -- Goal: settlingPos'.any (· == p) = settlingPos.any (· == p.rotateCCW)
    -- Work via List.any_eq_true and List.mem_flatMap
    cases h_lhs : settlingPos'.any (· == p) with
    | true =>
        symm
        rw [List.any_eq_true] at h_lhs ⊢
        obtain ⟨q, hq_mem, hq_beq⟩ := h_lhs
        have hq_eq : q = p := eq_of_beq hq_beq
        rw [hq_eq] at hq_mem
        -- p ∈ settlingPos' = settling'.flatMap FU.positions
        rw [List.mem_flatMap] at hq_mem
        obtain ⟨v, hv_settling', hv_pos⟩ := hq_mem
        have hv_fus' : v ∈ fus' := List.mem_of_mem_filter hv_settling'
        obtain ⟨u, hu_fus, hu_any, _⟩ := floatingUnit_any_in_rotateCW_rev s v hv_fus'
        -- u.rotateCW.positions.any (· == p) = v.positions.any (· == p)
        have h_p_any : v.positions.any (· == p) = true :=
            List.any_eq_true.mpr ⟨p, hv_pos, beq_self_eq_true p⟩
        have h_urCW : u.rotateCW.positions.any (· == p) = true := (hu_any p).symm ▸ h_p_any
        rw [FallingUnit.positions_rotateCW, any_map_rotateCW_beq] at h_urCW
        -- u.positions.any (· == p.rotateCCW) = true
        -- Need u ∈ settling to get p.rotateCCW ∈ settlingPos
        have hv_ml : (v.minLayer == minML') = true := (List.mem_filter.mp hv_settling').2
        have h_ml_eq : u.rotateCW.minLayer = v.minLayer := minLayer_ext hu_any
        rw [FallingUnit.minLayer_rotateCW] at h_ml_eq
        have hu_ml : (u.minLayer == minML) = true := by
            have hml : u.minLayer = minML' := by
                rw [h_ml_eq]; exact eq_of_beq hv_ml
            have hmlr : minML' = minML := (minML_eq_rotateCW s h).symm
            exact beq_of_eq (hml.trans hmlr)
        have hu_settling : u ∈ settling := List.mem_filter.mpr ⟨hu_fus, hu_ml⟩
        -- p.rotateCCW ∈ u.positions (from h_urCW)
        have h_pCCW_mem : p.rotateCCW ∈ u.positions := by
            rw [List.any_eq_true] at h_urCW
            obtain ⟨q, hq_mem, hq_beq⟩ := h_urCW
            exact eq_of_beq hq_beq ▸ hq_mem
        -- p.rotateCCW ∈ settlingPos
        have h_pCCW_settlingPos : p.rotateCCW ∈ settlingPos :=
            List.mem_flatMap.mpr ⟨u, hu_settling, h_pCCW_mem⟩
        exact ⟨p.rotateCCW, h_pCCW_settlingPos, beq_self_eq_true _⟩
    | false =>
        symm
        rw [Bool.eq_false_iff] at h_lhs ⊢
        intro h_rhs
        rw [List.any_eq_true] at h_rhs
        obtain ⟨q, hq_mem, hq_beq⟩ := h_rhs
        have hq_eq : q = p.rotateCCW := eq_of_beq hq_beq
        rw [hq_eq] at hq_mem
        rw [List.mem_flatMap] at hq_mem
        obtain ⟨u, hu_settling, hu_pos⟩ := hq_mem
        have hu_fus : u ∈ fus := List.mem_of_mem_filter hu_settling
        obtain ⟨v, hv_fus', hv_any, _⟩ := floatingUnit_any_in_rotateCW s u hu_fus
        -- v.positions.any (· == p)
        have h_u_any : u.positions.any (· == p.rotateCCW) = true :=
            List.any_eq_true.mpr ⟨p.rotateCCW, hu_pos, beq_self_eq_true _⟩
        have h_vp : v.positions.any (· == p) = true := by
            rw [← hv_any p, FallingUnit.positions_rotateCW, any_map_rotateCW_beq]
            exact h_u_any
        -- v ∈ settling'
        have hu_ml : (u.minLayer == minML) = true := (List.mem_filter.mp hu_settling).2
        have h_ml_eq : u.rotateCW.minLayer = v.minLayer := minLayer_ext hv_any
        rw [FallingUnit.minLayer_rotateCW] at h_ml_eq
        have hv_ml : (v.minLayer == minML') = true := by
            have hml : v.minLayer = minML := by
                rw [← h_ml_eq]; exact eq_of_beq hu_ml
            have hmlr : minML = minML' := minML_eq_rotateCW s h
            exact beq_of_eq (hml.trans hmlr)
        have hv_settling' : v ∈ settling' := List.mem_filter.mpr ⟨hv_fus', hv_ml⟩
        -- p ∈ v.positions → p ∈ settlingPos' → settlingPos'.any (· == p) = true
        have h_p_mem : p ∈ v.positions := by
            rw [List.any_eq_true] at h_vp
            obtain ⟨q, hq_mem, hq_beq⟩ := h_vp
            exact eq_of_beq hq_beq ▸ hq_mem
        have : settlingPos'.any (· == p) = true :=
            List.any_eq_true.mpr ⟨p, List.mem_flatMap.mpr ⟨v, hv_settling', h_p_mem⟩, beq_self_eq_true _⟩
        exact h_lhs this

-- process_rotateCW 本体
-- ============================================================

/-- waveStep は rotateCW で等変である。

    **現状（2026-04-20）**: 一時 axiom として導入。
    真定理であることは vanilla4/5/stress8 で計算検証済み（`#guard` 相当）。
    構成的証明は `docs/plans/gravity-proof-execution-plan.md` §2 S3 参照。

    **de-axiomatization 計画**:
    1. `allIsolatedPins_rotateCW_perm`, `allStructuralClustersList_rotateCW_perm`
       を構築 → `floatingUnits_rotateCW_perm`
    2. `settling_rotateCW_perm : settling'.Perm (settling.map FU.rotateCW)` を
       `Perm.filter` + `FallingUnit.minLayer_rotateCW` + 本ファイルの
       `settling_positions_any_rotateCW` / `minML_eq_rotateCW` 経由で導出
    3. `placeLDGroups_perm_within_LD` を `placeFallingUnit_comm_of_layer_disjoint`
       の応用として構築
    4. 以上を組み合わせて axiom を構成的 theorem に置換 -/
private axiom waveStep_rotateCW_comm (s : Shape) :
        waveStep s.rotateCW = (waveStep s).rotateCW

/-- processWave は rotateCW で等変である（waveStep_rotateCW_comm を前提） -/
private theorem processWave_rotateCW_comm (s : Shape) :
        processWave s.rotateCW = (processWave s).rotateCW := by
    suffices h : ∀ n (t : Shape), nonGroundedLayerSum t ≤ n →
            processWave t.rotateCW = (processWave t).rotateCW from
        h _ s le_rfl
    intro n
    induction n with
    | zero =>
        intro t ht
        have h_zero : nonGroundedLayerSum t = 0 := Nat.le_zero.mp ht
        have h_empty : (floatingUnits t).isEmpty = true :=
            nonGroundedLayerSum_zero_fus_empty t h_zero
        have h_r_empty : (floatingUnits t.rotateCW).isEmpty = true := by
            rw [← floatingUnits_isEmpty_rotateCW]; exact h_empty
        have lhs_eq : processWave t.rotateCW = t.rotateCW := by
            conv_lhs => unfold processWave
            simp only [h_r_empty, ↓reduceIte]
        have rhs_eq : processWave t = t := by
            conv_lhs => unfold processWave
            simp only [h_empty, ↓reduceIte]
        rw [lhs_eq, rhs_eq]
    | succ n ih =>
        intro t ht
        cases h : (floatingUnits t).isEmpty with
        | true =>
            have h_r : (floatingUnits t.rotateCW).isEmpty = true := by
                rw [← floatingUnits_isEmpty_rotateCW]; exact h
            have lhs_eq : processWave t.rotateCW = t.rotateCW := by
                conv_lhs => unfold processWave
                simp only [h_r, ↓reduceIte]
            have rhs_eq : processWave t = t := by
                conv_lhs => unfold processWave
                simp only [h, ↓reduceIte]
            rw [lhs_eq, rhs_eq]
        | false =>
            have h_r : (floatingUnits t.rotateCW).isEmpty = false := by
                rw [← floatingUnits_isEmpty_rotateCW]; exact h
            have lhs_eq : processWave t.rotateCW = processWave (waveStep t.rotateCW) := by
                conv_lhs => unfold processWave
                simp only [h_r, Bool.false_eq_true, ↓reduceIte]
            have rhs_eq : processWave t = processWave (waveStep t) := by
                conv_lhs => unfold processWave
                simp only [h, Bool.false_eq_true, ↓reduceIte]
            rw [lhs_eq, rhs_eq, waveStep_rotateCW_comm t]
            exact ih (waveStep t)
                (by have := waveStep_nonGroundedLayerSum_lt t h; omega)

/-- 落下処理と 90° 時計回り回転は可換である。
    波動モデルでは layerCount 制約なしで成立する -/
theorem process_rotateCW (s : Shape) :
        (process s).map Shape.rotateCW = process s.rotateCW := by
    simp only [process]
    rw [processWave_rotateCW_comm s]
    have h := option_bind_normalize_rotateCW (some (processWave s))
    simp only [Option.bind_some, Option.map_some] at h
    exact h

end Gravity

namespace Shape

/-- 落下処理を適用する。浮遊している落下単位を下方に移動させる -/
def gravity (s : Shape) : Option Shape :=
    Gravity.process s

/-- 落下処理を適用し結果がない場合（全て空）は元のシェイプを返す便利関数 -/
def gravityOrSelf (s : Shape) : Shape :=
    s.gravity.getD s

/-- 落下処理と 180° 回転は可換である。
    波動モデルにより layerCount 制約なしで成立する -/
theorem gravity_rotate180_comm (s : Shape) :
        (s.gravity).map Shape.rotate180 = s.rotate180.gravity := by
    exact Gravity.process_rotate180 s

/-- 落下処理と 90° 時計回り回転は可換である。
    波動モデルにより layerCount 制約なしで成立する -/
theorem gravity_rotateCW_comm (s : Shape) :
        (s.gravity).map Shape.rotateCW = s.rotateCW.gravity := by
    exact Gravity.process_rotateCW s

-- ============================================================
-- 安定状態 (Settled State) の定義
-- ============================================================

/-- シェイプが安定状態: 浮遊する落下単位が存在しない -/
def IsSettled (s : Shape) : Prop :=
    Gravity.floatingUnits s = []

/-- シェイプが安定状態かどうかを判定する -/
def isSettled (s : Shape) : Bool :=
    (Gravity.floatingUnits s).isEmpty

/-- IsSettled と isSettled の同値性 -/
theorem IsSettled_iff_isSettled (s : Shape) :
        s.IsSettled ↔ s.isSettled = true := by
    simp only [IsSettled, isSettled, List.isEmpty_iff]

/-- 安定状態は rotate180 で保存される -/
theorem IsSettled_rotate180 (s : Shape) (h : s.IsSettled) :
        s.rotate180.IsSettled := by
    simp only [IsSettled] at h ⊢
    have he := Gravity.floatingUnits_isEmpty_rotate180 s
    rw [h] at he
    -- he : true = (floatingUnits s.rotate180).isEmpty
    cases hf : Gravity.floatingUnits s.rotate180 with
    | nil => rfl
    | cons a l => rw [hf] at he; simp only [List.isEmpty, Bool.true_eq_false] at he

-- ============================================================
-- SettledShape (安定状態のシェイプ)
-- ============================================================

/-- 安定状態にあるシェイプを表すサブタイプ。
    ベルトで搬送されるシェイプおよび各加工装置の入出力は常にこの型に属する。
    不安定状態は加工装置の内部処理でのみ一時的に発生し、
    落下処理 (Gravity) により安定状態に復帰した後に出力される。 -/
abbrev SettledShape := { s : Shape // s.IsSettled }

namespace SettledShape

/-- SettledShape から Shape への射影（Coe で自動適用される） -/
instance : Coe SettledShape Shape where
    coe ss := ss.val

/-- SettledShape の 180° 回転は SettledShape を保存する -/
def rotate180 (ss : SettledShape) : SettledShape :=
    ⟨ss.val.rotate180, IsSettled_rotate180 ss.val ss.property⟩

-- 追加の SettledShape 操作・Arbitrary インスタンスは S2IL/Behavior/SettledShape.lean に定義

end SettledShape

end Shape
