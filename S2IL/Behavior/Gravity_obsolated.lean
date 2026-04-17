-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Behavior.Gravity.SettleFoldlEq_obsolated
import S2IL.Behavior.Gravity.FoldlBridge_obsolated

namespace Gravity

open Shape (layers_rotate180 clearPositions_rotate180)

-- process_rotate180 の本体
-- ============================================================

/-- rotate180 側の clearPositions 入力（sorted FU positions）の等価性 -/
private theorem clearPositions_obs_eq_rotate180 (s : Shape) :
        s.rotate180.clearPositions
            ((sortFallingUnits' (floatingUnits s)).flatMap FallingUnit.positions
                |>.map QuarterPos.rotate180) =
        s.rotate180.clearPositions
            ((sortFallingUnits' (floatingUnits s.rotate180)).flatMap FallingUnit.positions) := by
    apply Shape.clearPositions_ext
    intro p
    rw [any_map_rotate180_beq]
    rw [sortFallingUnits'_any_positions (floatingUnits s)]
    rw [sortFallingUnits'_any_positions (floatingUnits s.rotate180)]
    have := falling_positions_any_rotate180 s p.rotate180
    rw [QuarterPos.rotate180_rotate180] at this
    exact this

/-- 落下処理と 180° 回転は可換である。
    layerCount ≤ 5 の制約が必要（6 レイヤ以上では反例が存在する） -/
theorem process_rotate180 (s : Shape) (h_layers : s.layerCount ≤ 5) :
        (process s).map Shape.rotate180 = process s.rotate180 := by
    simp only [process]
    rw [← floatingUnits_isEmpty_rotate180]
    split <;> rename_i h
    · -- 落下単位なし: normalize の等変性
      exact s.normalize_map_layers Layer.rotate180 Layer.isEmpty_rotate180
    · -- 落下単位あり: パイプライン全体の等変性
      -- normalize + ofLayers の交換
      rw [option_bind_normalize_rotate180, ofLayers_rotate180]
      congr 1
      -- foldl_place_rotate180 で LHS の map Lr180 を foldl 内部に移動
      rw [foldl_place_rotate180]
      -- 同一 minLayer グループ内の可換性: floatingUnits の位置素性 + ≤5L 制約から
      -- 同一 sortGroup 内の可換性: pin-pin は方角素、cluster-cluster は構造的可換
      have h_comm := settleStep_comm_mapped_perm s s.rotate180 LayerPerm.rotate180
          FallingUnit.rotate180 h_layers (fun _ => rfl) (fun _ => rfl)
          FallingUnit.sortGroup_rotate180 FallingUnit.minLayer_rotate180
      -- fallingUnitOrd は r180 等変でないため、foldl レベルの bridge を適用
      rw [sort_foldl_map_perm_bridge s.rotate180 FallingUnit.rotate180
          FallingUnit.sortGroup_rotate180 (floatingUnits s) _ h_comm]
      -- obstacle の等変性: clearPositions_rotate180 + clearPositions_ext で証明
      rw [← layers_rotate180, clearPositions_rotate180]
      rw [clearPositions_obs_eq_rotate180 s]
      -- sorted リスト foldl の等価性: settle_foldl_eq で閉じる
      exact settle_foldl_eq s _

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

-- 浮遊位置のメンバーシップ CW 等変性
-- ============================================================

/-- List.map QuarterPos.rotateCW 後の .any (rotateCW 版) -/
theorem any_map_rotateCW_beq (ps : List QuarterPos) (p : QuarterPos) :
        (ps.map QuarterPos.rotateCW).any (· == p) =
        ps.any (· == p.rotateCCW) := by
    have h := LayerPerm.list_any_map .rotateCW ps p.rotateCCW
    simpa only [QuarterPos.rotateCCW_rotateCW] using h

/-- rotateCW 後の positions の .any は元の .any と等価 -/
private theorem any_positions_rotateCW (u : FallingUnit) (p : QuarterPos) :
        u.rotateCW.positions.any (· == p.rotateCW) = u.positions.any (· == p) := by
    rw [FallingUnit.positions_rotateCW, any_map_rotateCW_beq,
        QuarterPos.rotateCW_rotateCCW]

/-- rotateCW 対応関数 g が .any 同値を保つとき、floatingUnits 上で g は単射 -/
private theorem injective_on_floatingUnits_of_any_rotateCW
        (t : Shape) (g : FallingUnit → FallingUnit)
        (hg_any : ∀ u ∈ floatingUnits t, ∀ p : QuarterPos,
            u.rotateCW.positions.any (· == p) = (g u).positions.any (· == p))
        (u1 u2 : FallingUnit)
        (hu1 : u1 ∈ floatingUnits t) (hu2 : u2 ∈ floatingUnits t)
        (h_eq : g u1 = g u2) :
        u1 = u2 := by
    by_contra h_ne
    have ⟨p, hp⟩ := floatingUnit_positions_nonempty t u1 hu1
    have h1 : u1.rotateCW.positions.any (· == p.rotateCW) = true := by
        rw [any_positions_rotateCW]
        exact List.any_eq_true.mpr ⟨p, hp, BEq.rfl⟩
    have h2 : u2.rotateCW.positions.any (· == p.rotateCW) = true := by
        rw [hg_any u2 hu2, ← h_eq, ← hg_any u1 hu1]
        exact h1
    rw [any_positions_rotateCW] at h2
    obtain ⟨i, hi, h_eq_i⟩ := List.mem_iff_getElem.mp hu1
    obtain ⟨j, hj, h_eq_j⟩ := List.mem_iff_getElem.mp hu2
    subst h_eq_i
    subst h_eq_j
    have h_ij : i ≠ j := fun h_eq_ij => h_ne (by subst h_eq_ij; rfl)
    exact absurd
        (by
            rw [List.any_eq_true] at h2 ⊢
            exact h2 : ((floatingUnits t)[j]).positions.any (· == p) = true)
        (Bool.eq_false_iff.mp
            (floatingUnits_pairwise_disjoint t i j hi hj h_ij p
                (List.any_eq_true.mpr ⟨p, hp, BEq.rfl⟩)))

/-- 浮遊位置メンバーシップは rotateCW で保存される -/
private theorem falling_positions_any_rotateCW (s : Shape) (p : QuarterPos) :
        ((floatingUnits s).flatMap FallingUnit.positions).any (· == p) =
        ((floatingUnits s.rotateCW).flatMap FallingUnit.positions).any (· == p.rotateCW) := by
    cases h : ((floatingUnits s).flatMap FallingUnit.positions).any (· == p) with
    | true =>
        symm
        obtain ⟨h_valid, ⟨q, hq, hq_ne⟩, h_ug⟩ := floatingUnits_positions_getQuarter s p h
        apply ungrounded_in_floatingUnits_positions s.rotateCW p.rotateCW
        · rw [Shape.layerCount_rotateCW]; exact h_valid
        · exact ⟨q, by rw [QuarterPos.getQuarter_rotateCW]; exact hq, hq_ne⟩
        · exact fun h => h_ug ((mem_groundedPositions_rotateCW s p).mpr h)
    | false =>
        symm
        cases h' : ((floatingUnits s.rotateCW).flatMap FallingUnit.positions).any
                (· == p.rotateCW) with
        | false => rfl
        | true =>
            exfalso
            obtain ⟨h_valid', ⟨q', hq', hq_ne'⟩, h_ug'⟩ :=
                floatingUnits_positions_getQuarter s.rotateCW p.rotateCW h'
            have h_should_be_true := ungrounded_in_floatingUnits_positions s p
                (by rw [← Shape.layerCount_rotateCW]; exact h_valid')
                ⟨q', by rw [← QuarterPos.getQuarter_rotateCW]; exact hq', hq_ne'⟩
                (fun hp => h_ug' ((mem_groundedPositions_rotateCW s p).mp hp))
            rw [h] at h_should_be_true; exact absurd h_should_be_true (by decide)

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

/-- floatingUnits の長さは rotateCW で不変 -/
private theorem floatingUnits_length_rotateCW (s : Shape) :
        (floatingUnits s).length = (floatingUnits s.rotateCW).length := by
    suffices h_le : ∀ (t : Shape),
            (floatingUnits t).length ≤ (floatingUnits t.rotateCW).length by
        apply Nat.le_antisymm (h_le s)
        -- s.rCW.rCW.rCW.rCW = s → 4 回 rCW で元に戻る
        have h1 := h_le s.rotateCW
        have h2 := h_le s.rotateCW.rotateCW
        have h3 := h_le s.rotateCW.rotateCW.rotateCW
        rw [Shape.rotateCW_four] at h3; omega
    intro t
    have hg_ex : ∀ u ∈ floatingUnits t,
            ∃ v ∈ floatingUnits t.rotateCW,
                (∀ p, u.rotateCW.positions.any (· == p) = v.positions.any (· == p))
                ∧ u.rotateCW.typeOrd = v.typeOrd :=
        floatingUnit_any_in_rotateCW t
    open Classical in
    let g : FallingUnit → FallingUnit :=
        fun u => if h : u ∈ floatingUnits t
            then (hg_ex u h).choose
            else u
    have hg_mem : ∀ u ∈ floatingUnits t, g u ∈ floatingUnits t.rotateCW := by
        intro u hu
        show (if h : u ∈ floatingUnits t then (hg_ex u h).choose else u) ∈ _
        rw [dif_pos hu]
        exact (hg_ex u hu).choose_spec.1
    have hg_any : ∀ u ∈ floatingUnits t, ∀ p : QuarterPos,
            u.rotateCW.positions.any (· == p) = (g u).positions.any (· == p) := by
        intro u hu
        show ∀ p, u.rotateCW.positions.any (· == p) =
            (if h : u ∈ floatingUnits t then (hg_ex u h).choose else u).positions.any (· == p)
        rw [dif_pos hu]
        exact (hg_ex u hu).choose_spec.2.1
    have hg_inj : ∀ u1 ∈ floatingUnits t, ∀ u2 ∈ floatingUnits t, g u1 = g u2 → u1 = u2 := by
        intro u1 hu1 u2 hu2 h_eq
        exact injective_on_floatingUnits_of_any_rotateCW t g hg_any u1 u2 hu1 hu2 h_eq
    exact length_le_of_injection (floatingUnits t) (floatingUnits t.rotateCW)
        g hg_mem hg_inj (floatingUnits_nodup t) (floatingUnits_nodup t.rotateCW)

-- process_rotateCW 本体
-- ============================================================

/-- rotateCW 側の clearPositions 入力（sorted FU positions）の等価性 -/
private theorem clearPositions_obs_eq_rotateCW (s : Shape) :
        s.rotateCW.clearPositions
            ((sortFallingUnits' (floatingUnits s)).flatMap FallingUnit.positions
                |>.map QuarterPos.rotateCW) =
        s.rotateCW.clearPositions
            ((sortFallingUnits' (floatingUnits s.rotateCW)).flatMap FallingUnit.positions) := by
    apply Shape.clearPositions_ext
    intro p
    rw [any_map_rotateCW_beq]
    rw [sortFallingUnits'_any_positions (floatingUnits s)]
    rw [sortFallingUnits'_any_positions (floatingUnits s.rotateCW)]
    have := falling_positions_any_rotateCW s p.rotateCCW
    rw [QuarterPos.rotateCCW_rotateCW] at this
    exact this

/-- 落下処理と 90° 時計回り回転は可換である。
    layerCount ≤ 5 の制約が必要（6 レイヤ以上では反例が存在する） -/
theorem process_rotateCW (s : Shape) (h_layers : s.layerCount ≤ 5) :
        (process s).map Shape.rotateCW = process s.rotateCW := by
    simp only [process]
    rw [← floatingUnits_isEmpty_rotateCW]
    split <;> rename_i h
    · -- 落下単位なし: normalize の等変性
      exact s.normalize_map_layers Layer.rotateCW Layer.isEmpty_rotateCW
    · -- 落下単位あり: パイプライン全体の等変性
      rw [option_bind_normalize_rotateCW, ofLayers_rotateCW]
      congr 1
      rw [foldl_place_rotateCW]
      -- 同一 minLayer グループ内の可換性: floatingUnits の位置素性 + ≤5L 制約から
      -- 同一 sortGroup 内の可換性: pin-pin は方角素、cluster-cluster は構造的可換
      have h_comm := settleStep_comm_mapped_perm s s.rotateCW LayerPerm.rotateCW
          FallingUnit.rotateCW h_layers (fun _ => rfl) (fun _ => rfl)
          FallingUnit.sortGroup_rotateCW FallingUnit.minLayer_rotateCW
      -- fallingUnitOrd は rCW 等変でないため、foldl レベルの bridge を適用
      rw [sort_foldl_map_perm_bridge s.rotateCW FallingUnit.rotateCW
          FallingUnit.sortGroup_rotateCW (floatingUnits s) _ h_comm]
      rw [← Shape.layers_rotateCW, Shape.clearPositions_rotateCW]
      rw [clearPositions_obs_eq_rotateCW s]
      exact settle_foldl_eq_generic s _ FallingUnit.rotateCW QuarterPos.rotateCW s.rotateCW
          (floatingUnit_any_in_rotateCW s)
          any_positions_rotateCW
          (floatingUnits_length_rotateCW s)

end Gravity

namespace Shape

/-- 落下処理を適用する。浮遊している落下単位を下方に移動させる -/
def gravity (s : Shape) : Option Shape :=
    Gravity.process s

/-- 落下処理を適用し結果がない場合（全て空）は元のシェイプを返す便利関数 -/
def gravityOrSelf (s : Shape) : Shape :=
    s.gravity.getD s

/-- 落下処理と 180° 回転は可換である。
    layerCount ≤ 5 の制約が必要（6 レイヤ以上では反例が存在する） -/
theorem gravity_rotate180_comm (s : Shape) (h : s.layerCount ≤ 5) :
        (s.gravity).map Shape.rotate180 = s.rotate180.gravity := by
    exact Gravity.process_rotate180 s h

/-- 落下処理と 90° 時計回り回転は可換である。
    layerCount ≤ 5 の制約が必要（6 レイヤ以上では反例が存在する） -/
theorem gravity_rotateCW_comm (s : Shape) (h : s.layerCount ≤ 5) :
        (s.gravity).map Shape.rotateCW = s.rotateCW.gravity := by
    exact Gravity.process_rotateCW s h

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

