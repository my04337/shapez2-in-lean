-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity.CommExt.PlaceGrounding

namespace Gravity

open _root_.QuarterPos (getQuarter_rotate180)

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


end Gravity
