-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity.CommExt.LandingDist

namespace Gravity

open _root_.QuarterPos (getQuarter_rotate180)

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

/-- `placeQuarter` は非空クォーターを配置する場合に `isOccupied` を単調保存する。

    任意の位置 `(lay, dir)` で既に占有済みなら、任意の場所に非空の `q` を配置しても
    引き続き占有されている。

    用途: Sub-lemma #5/#6 (placing_*_preserves_grounding) の核補題。
    cluster/crystal/colored は `canFormBond` から非空、pin は pin コンストラクタから非空。 -/
theorem isOccupied_placeQuarter_mono (obs : List Layer) (lay lay' : Nat)
        (dir dir' : Direction) (q : Quarter)
        (h_nonempty : q.isEmpty = false)
        (h_occ : isOccupied obs lay dir = true) :
        isOccupied (placeQuarter obs lay' dir' q) lay dir = true := by
    unfold isOccupied at h_occ ⊢
    rw [placeQuarter_getElem?_full]
    rcases hob : obs[lay]? with _ | l
    · rw [hob] at h_occ; simp at h_occ
    rw [hob] at h_occ; simp only at h_occ
    have h_lay_lt : lay < obs.length := List.getElem?_eq_some_iff.mp hob |>.1
    have h_in : lay < max obs.length (lay' + 1) := by omega
    rw [if_pos h_in]
    by_cases h_eq : lay = lay'
    · subst h_eq
      rw [if_pos rfl]
      simp only
      rw [List.getD_eq_getElem?_getD, hob, Option.getD_some]
      by_cases hd : dir = dir'
      · subst hd
        simp only [QuarterPos.getDir_setDir_same, h_nonempty, Bool.not_false]
      · rw [Gravity.getDir_setDir_ne _ _ _ _ (Ne.symm hd)]
        exact h_occ
    · rw [if_neg h_eq]
      simp only
      rw [List.getD_eq_getElem?_getD, hob, Option.getD_some]
      exact h_occ

/-- `placeFallingUnit` は全配置クォーターが非空であれば `isOccupied` を単調保存する。

    用途: Sub-lemma #5/#6 の foldl 版。cluster FU の場合は `canFormBond` から非空、
    pin FU の場合は pin コンストラクタから非空が導ける。 -/
theorem isOccupied_placeFallingUnit_mono (s : Shape) (obs : List Layer)
        (u : FallingUnit) (d : Nat) (lay : Nat) (dir : Direction)
        (h_nonempty : ∀ p ∈ u.positions, ∀ qv,
            p.getQuarter s = some qv → qv.isEmpty = false)
        (h_occ : isOccupied obs lay dir = true) :
        isOccupied (placeFallingUnit s obs u d) lay dir = true := by
    unfold placeFallingUnit
    have h : ∀ (ps : List QuarterPos) (acc : List Layer),
        (∀ p ∈ ps, ∀ qv, p.getQuarter s = some qv → qv.isEmpty = false) →
        isOccupied acc lay dir = true →
        isOccupied (ps.foldl (fun obs p =>
            match p.getQuarter s with
            | some q => placeQuarter obs (p.layer - d) p.dir q
            | none => obs) acc) lay dir = true := by
      intro ps
      induction ps with
      | nil => intros; assumption
      | cons p rest ih =>
        intro acc hne hocc
        simp only [List.foldl_cons]
        apply ih _ (fun q hq => hne q (.tail _ hq))
        cases hq : p.getQuarter s with
        | none => exact hocc
        | some qv =>
          have h_qv_ne : qv.isEmpty = false := hne p (.head _) qv hq
          exact isOccupied_placeQuarter_mono acc lay (p.layer - d) dir p.dir qv h_qv_ne hocc
    exact h u.positions obs h_nonempty h_occ

/-- `isGroundingContact` は両端点の `getQuarter` 値が等しい 2 つの Shape で一致する。

    用途: Sub-lemma #5/#6 の基礎。shape の変化が a, b での `getQuarter` を保存するなら
    grounding contact は両者で同じ。 -/
theorem isGroundingContact_congr_of_getQuarter_eq
        {s1 s2 : Shape} {a b : QuarterPos}
        (ha : a.getQuarter s1 = a.getQuarter s2)
        (hb : b.getQuarter s1 = b.getQuarter s2) :
        isGroundingContact s1 a b = isGroundingContact s2 a b := by
    simp only [isGroundingContact, ha, hb]

/-- `isStructurallyBonded` も同様に `getQuarter` 値のみに依存する。 -/
theorem isStructurallyBonded_congr_of_getQuarter_eq
        {s1 s2 : Shape} {a b : QuarterPos}
        (ha : a.getQuarter s1 = a.getQuarter s2)
        (hb : b.getQuarter s1 = b.getQuarter s2) :
        isStructurallyBonded s1 a b = isStructurallyBonded s2 a b := by
    simp only [isStructurallyBonded, ha, hb]

/-- `groundingEdge` は両端点の `getQuarter` 値のみから決まる。

    用途: `placeFallingUnit` / `clearPositions` など `getQuarter` を部分的に保存する
    shape 変換に対して、影響を受けない位置でのエッジ保存に使う。 -/
theorem groundingEdge_congr_of_getQuarter_eq
        {s1 s2 : Shape} {a b : QuarterPos}
        (ha : a.getQuarter s1 = a.getQuarter s2)
        (hb : b.getQuarter s1 = b.getQuarter s2) :
        groundingEdge s1 a b = groundingEdge s2 a b := by
    simp only [groundingEdge, isUpwardGroundingContact, isStructurallyBonded,
               isGroundingContact, ha, hb]

/-- `placeFallingUnit` の結果 layers における `getDir` は、着地位置以外で `obs` と一致する。
    `foldl_placeQuarter_getDir_preserved` を `placeFallingUnit` 展開形で包んだ再利用用補題。 -/
theorem getDir_placeFallingUnit_of_ne
        (s : Shape) (obs : List Layer) (u : FallingUnit) (d : Nat)
        (lay : Nat) (dir : Direction)
        (h_not : ∀ p ∈ u.positions, ¬(p.layer - d = lay ∧ p.dir = dir)) :
        QuarterPos.getDir ((placeFallingUnit s obs u d).getD lay Layer.empty) dir =
        QuarterPos.getDir (obs.getD lay Layer.empty) dir := by
    unfold placeFallingUnit
    exact foldl_placeQuarter_getDir_preserved s obs u.positions d lay dir h_not

/-- `placeFallingUnit` はリストの長さを減らさない。 -/
theorem placeFallingUnit_length_ge (s : Shape) (obs : List Layer)
        (u : FallingUnit) (d : Nat) :
        (placeFallingUnit s obs u d).length ≥ obs.length := by
    unfold placeFallingUnit
    suffices h : ∀ (ps : List QuarterPos) (acc : List Layer),
        acc.length ≥ obs.length →
        (ps.foldl (fun obs' p =>
            match p.getQuarter s with
            | some q => placeQuarter obs' (p.layer - d) p.dir q
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
      · rw [placeQuarter_length]; exact le_max_of_le_left h_acc
      · exact h_acc

/-- **Shape ↔ list-level 橋渡し**: 2 つの Shape で、位置 `pos` のレイヤが両方で有効範囲内 かつ
    list-level の `getDir (layers.getD pos.layer Layer.empty) pos.dir` が一致するなら、
    `QuarterPos.getQuarter` 値も一致する。

    用途: `getDir_placeFallingUnit_of_ne` (list-level) を shape-level
    `QuarterPos.getQuarter` に変換する橋渡し。 -/
theorem getQuarter_eq_of_getDir_getD_eq
        {s1 s2 : Shape} {pos : QuarterPos}
        (h_lt1 : pos.layer < s1.layerCount)
        (h_lt2 : pos.layer < s2.layerCount)
        (h : QuarterPos.getDir (s1.layers.getD pos.layer Layer.empty) pos.dir =
             QuarterPos.getDir (s2.layers.getD pos.layer Layer.empty) pos.dir) :
        QuarterPos.getQuarter s1 pos = QuarterPos.getQuarter s2 pos := by
    unfold QuarterPos.getQuarter Shape.layerCount at *
    rw [List.getElem?_eq_getElem h_lt1, List.getElem?_eq_getElem h_lt2]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h_lt1] at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h_lt2] at h
    simpa using h

/-- `groundingEdge` の list-level 合同性: 両端点 `a, b` それぞれで layer 有効範囲内 かつ
    list-level `getDir (layers.getD ...)` が一致するなら、`groundingEdge` 値が一致。

    `getQuarter_eq_of_getDir_getD_eq` + `groundingEdge_congr_of_getQuarter_eq` の合成。
    `placeFallingUnit` の結果 layers と元の obs を包む 2 Shape 間で、
    着地位置以外のエッジ保存を示す際に直接使える。 -/
theorem groundingEdge_congr_of_getDir_getD_eq
        {s1 s2 : Shape} {a b : QuarterPos}
        (ha1 : a.layer < s1.layerCount) (ha2 : a.layer < s2.layerCount)
        (hb1 : b.layer < s1.layerCount) (hb2 : b.layer < s2.layerCount)
        (ha : QuarterPos.getDir (s1.layers.getD a.layer Layer.empty) a.dir =
              QuarterPos.getDir (s2.layers.getD a.layer Layer.empty) a.dir)
        (hb : QuarterPos.getDir (s1.layers.getD b.layer Layer.empty) b.dir =
              QuarterPos.getDir (s2.layers.getD b.layer Layer.empty) b.dir) :
        groundingEdge s1 a b = groundingEdge s2 a b := by
    exact groundingEdge_congr_of_getQuarter_eq
        (getQuarter_eq_of_getDir_getD_eq ha1 ha2 ha)
        (getQuarter_eq_of_getDir_getD_eq hb1 hb2 hb)

/-- `placeFallingUnit` は着地位置以外の `groundingEdge` を保存する（shape-level）。

    前提: `s_obs.layers = obs` / `s_result.layers = placeFallingUnit s obs u d` で
    2 Shape を obs / result 双方に対応させる。両端点 `a, b` が着地位置でなく、
    かつ `s_obs` で valid なら、`groundingEdge s_obs a b = groundingEdge s_result a b`。

    用途: Sub-lemma #5/#6 主補題 — settling FU 配置後に、影響を受けない位置でのエッジ保存。 -/
theorem groundingEdge_placeFallingUnit_of_ne
        (s : Shape) (obs : List Layer) (u : FallingUnit) (d : Nat)
        (s_obs s_result : Shape)
        (h_obs : s_obs.layers = obs)
        (h_result : s_result.layers = placeFallingUnit s obs u d)
        (a b : QuarterPos)
        (h_a1 : a.layer < s_obs.layerCount)
        (h_b1 : b.layer < s_obs.layerCount)
        (h_not_a : ∀ p ∈ u.positions, ¬(p.layer - d = a.layer ∧ p.dir = a.dir))
        (h_not_b : ∀ p ∈ u.positions, ¬(p.layer - d = b.layer ∧ p.dir = b.dir)) :
        groundingEdge s_obs a b = groundingEdge s_result a b := by
    have h_len_ge : s_result.layerCount ≥ s_obs.layerCount := by
        unfold Shape.layerCount; rw [h_obs, h_result]
        exact placeFallingUnit_length_ge s obs u d
    have h_a2 : a.layer < s_result.layerCount := lt_of_lt_of_le h_a1 h_len_ge
    have h_b2 : b.layer < s_result.layerCount := lt_of_lt_of_le h_b1 h_len_ge
    have ha : QuarterPos.getDir (s_obs.layers.getD a.layer Layer.empty) a.dir =
              QuarterPos.getDir (s_result.layers.getD a.layer Layer.empty) a.dir := by
        rw [h_obs, h_result]
        exact (getDir_placeFallingUnit_of_ne s obs u d a.layer a.dir h_not_a).symm
    have hb : QuarterPos.getDir (s_obs.layers.getD b.layer Layer.empty) b.dir =
              QuarterPos.getDir (s_result.layers.getD b.layer Layer.empty) b.dir := by
        rw [h_obs, h_result]
        exact (getDir_placeFallingUnit_of_ne s obs u d b.layer b.dir h_not_b).symm
    exact groundingEdge_congr_of_getDir_getD_eq h_a1 h_a2 h_b1 h_b2 ha hb

/-- 固定 `d` での group foldl は長さを減らさない。
    個別 `placeFallingUnit_length_ge` の group 版。 -/
theorem foldl_placeFU_fixed_length_ge
        (s : Shape) (group : List FallingUnit) (obs : List Layer) (d : Nat) :
        (group.foldl (fun acc fu => placeFallingUnit s acc fu d) obs).length ≥ obs.length := by
    induction group generalizing obs with
    | nil => simp [List.foldl]
    | cons u rest ih =>
        simp only [List.foldl]
        exact le_trans (placeFallingUnit_length_ge s obs u d) (ih _)

/-- 固定 `d` での group foldl は、group 内のどの FU の着地位置でもない
    `(lay, dir)` で list-level `getDir` を保存する。

    個別版 `getDir_placeFallingUnit_of_ne` の group 版（帰納合成）。
    Sub-lemma #5/#6/#7 の placeLDGroups レベル grounding 保存を組み立てる
    中間ブロック。 -/
theorem getDir_foldl_placeFU_fixed_of_ne
        (s : Shape) (group : List FallingUnit) (obs : List Layer) (d : Nat)
        (lay : Nat) (dir : Direction)
        (h_not : ∀ u ∈ group, ∀ p ∈ u.positions,
                ¬(p.layer - d = lay ∧ p.dir = dir)) :
        QuarterPos.getDir
            ((group.foldl (fun acc fu => placeFallingUnit s acc fu d) obs).getD lay Layer.empty) dir =
        QuarterPos.getDir (obs.getD lay Layer.empty) dir := by
    induction group generalizing obs with
    | nil => simp [List.foldl]
    | cons u rest ih =>
        simp only [List.foldl]
        have h_u : ∀ p ∈ u.positions, ¬(p.layer - d = lay ∧ p.dir = dir) :=
            fun p hp => h_not u (.head _) p hp
        have h_rest : ∀ v ∈ rest, ∀ p ∈ v.positions,
                ¬(p.layer - d = lay ∧ p.dir = dir) :=
            fun v hv p hp => h_not v (.tail _ hv) p hp
        have h_step :=
            getDir_placeFallingUnit_of_ne s obs u d lay dir h_u
        exact (ih (placeFallingUnit s obs u d) h_rest).trans h_step

/-- 固定 `d` での group foldl は、group 内のどの FU の着地位置でもない
    端点 `a, b` において `groundingEdge` を保存する（shape-level）。

    前提: `s_obs.layers = obs` / `s_result.layers = group.foldl (...) obs`。
    個別版 `groundingEdge_placeFallingUnit_of_ne` の group 版。

    用途: Sub-lemma #5/#6 主補題 — placeLDGroups の 1 グループ処理後、
    影響を受けない位置でのエッジ保存。 -/
theorem groundingEdge_foldl_placeFU_fixed_of_ne
        (s : Shape) (group : List FallingUnit) (obs : List Layer) (d : Nat)
        (s_obs s_result : Shape)
        (h_obs : s_obs.layers = obs)
        (h_result : s_result.layers =
            group.foldl (fun acc fu => placeFallingUnit s acc fu d) obs)
        (a b : QuarterPos)
        (h_a1 : a.layer < s_obs.layerCount)
        (h_b1 : b.layer < s_obs.layerCount)
        (h_not_a : ∀ u ∈ group, ∀ p ∈ u.positions,
                ¬(p.layer - d = a.layer ∧ p.dir = a.dir))
        (h_not_b : ∀ u ∈ group, ∀ p ∈ u.positions,
                ¬(p.layer - d = b.layer ∧ p.dir = b.dir)) :
        groundingEdge s_obs a b = groundingEdge s_result a b := by
    have h_len_ge : s_result.layerCount ≥ s_obs.layerCount := by
        unfold Shape.layerCount; rw [h_obs, h_result]
        exact foldl_placeFU_fixed_length_ge s group obs d
    have h_a2 : a.layer < s_result.layerCount := lt_of_lt_of_le h_a1 h_len_ge
    have h_b2 : b.layer < s_result.layerCount := lt_of_lt_of_le h_b1 h_len_ge
    have ha : QuarterPos.getDir (s_obs.layers.getD a.layer Layer.empty) a.dir =
              QuarterPos.getDir (s_result.layers.getD a.layer Layer.empty) a.dir := by
        rw [h_obs, h_result]
        exact (getDir_foldl_placeFU_fixed_of_ne s group obs d a.layer a.dir h_not_a).symm
    have hb : QuarterPos.getDir (s_obs.layers.getD b.layer Layer.empty) b.dir =
              QuarterPos.getDir (s_result.layers.getD b.layer Layer.empty) b.dir := by
        rw [h_obs, h_result]
        exact (getDir_foldl_placeFU_fixed_of_ne s group obs d b.layer b.dir h_not_b).symm
    exact groundingEdge_congr_of_getDir_getD_eq h_a1 h_a2 h_b1 h_b2 ha hb

/-- placeLDGroups の実行過程で発生する全着地位置 `(lay, dir)` を列挙する。
    各グループ処理時点での obs に基づく `d = landingDistance first obs_k` を使い、
    グループ内の全 FU の全 positions を `(p.layer - d, p.dir)` に変換して収集する。

    用途: Sub-lemma #5/#6/#7 の placeLDGroups レベル `grounding` 保存で
    「影響を受けない位置」を具体的に特徴付けるために用いる。 -/
def placeLDGroupsLandings (s : Shape) :
        List FallingUnit → List Layer → List (Nat × Direction)
    | [], _ => []
    | first :: rest, obs =>
        let d := landingDistance first obs
        let group := (first :: rest).takeWhile
            (fun u => landingDistance u obs == d)
        let remaining := (first :: rest).dropWhile
            (fun u => landingDistance u obs == d)
        let obs' := group.foldl (fun acc fu =>
            placeFallingUnit s acc fu d) obs
        group.flatMap (fun u =>
            u.positions.map (fun p => (p.layer - d, p.dir))) ++
          placeLDGroupsLandings s remaining obs'
    termination_by sorted _ => sorted.length
    decreasing_by
        show ((first :: rest).dropWhile _).length < (first :: rest).length
        simp only [List.dropWhile_cons, beq_self_eq_true, ↓reduceIte, List.length_cons]
        exact Nat.lt_succ_of_le (List.dropWhile_suffix _).length_le

/-- `placeLDGroups` は obs の長さを減らさない。
    個別 `placeFallingUnit_length_ge` / グループ版 `foldl_placeFU_fixed_length_ge` の
    placeLDGroups レベル拡張（#5f → placeLDGroups）。 -/
theorem placeLDGroups_length_ge (s : Shape) (sorted : List FallingUnit) (obs : List Layer) :
        (placeLDGroups s sorted obs).length ≥ obs.length := by
    induction sorted, obs using placeLDGroups.induct s with
    | case1 obs => simp [placeLDGroups]
    | case2 obs v rest _ _ _ _ ih =>
        rw [placeLDGroups]
        exact le_trans (foldl_placeFU_fixed_length_ge s _ obs _) ih

/-- `placeLDGroups` は `placeLDGroupsLandings` に含まれない `(lay, dir)` において
    list-level `getDir` を保存する。

    個別版 `getDir_placeFallingUnit_of_ne` / グループ版 `getDir_foldl_placeFU_fixed_of_ne` の
    placeLDGroups レベル拡張（#5f → placeLDGroups）。 -/
theorem getDir_placeLDGroups_of_ne
        (s : Shape) (sorted : List FallingUnit) (obs : List Layer)
        (lay : Nat) (dir : Direction)
        (h_not : (lay, dir) ∉ placeLDGroupsLandings s sorted obs) :
        QuarterPos.getDir ((placeLDGroups s sorted obs).getD lay Layer.empty) dir =
        QuarterPos.getDir (obs.getD lay Layer.empty) dir := by
    induction sorted, obs using placeLDGroups.induct s with
    | case1 obs => simp [placeLDGroups]
    | case2 obs v rest _ _ _ _ ih =>
        rw [placeLDGroups]
        rw [placeLDGroupsLandings] at h_not
        simp only [List.mem_append, not_or] at h_not
        obtain ⟨h_not_group, h_not_rest⟩ := h_not
        rw [ih h_not_rest]
        apply getDir_foldl_placeFU_fixed_of_ne
        intro u hu p hp ⟨hp1, hp2⟩
        apply h_not_group
        rw [List.mem_flatMap]
        refine ⟨u, hu, ?_⟩
        rw [List.mem_map]
        exact ⟨p, hp, Prod.mk.injEq _ _ _ _ |>.mpr ⟨hp1, hp2⟩⟩

/-- `placeLDGroups` は `placeLDGroupsLandings` に含まれない端点 `a, b` において
    `groundingEdge` を保存する（shape-level）。

    前提: `s_obs.layers = obs` / `s_result.layers = placeLDGroups s sorted obs`。
    個別版 `groundingEdge_placeFallingUnit_of_ne` / グループ版
    `groundingEdge_foldl_placeFU_fixed_of_ne` の placeLDGroups レベル拡張。

    用途: Sub-lemma #5/#6 主補題 — `clearPositions` 後の非着地位置での
    エッジ保存を介した接地保存（#7）組立の核。 -/
theorem groundingEdge_placeLDGroups_of_ne
        (s : Shape) (sorted : List FallingUnit) (obs : List Layer)
        (s_obs s_result : Shape)
        (h_obs : s_obs.layers = obs)
        (h_result : s_result.layers = placeLDGroups s sorted obs)
        (a b : QuarterPos)
        (h_a1 : a.layer < s_obs.layerCount)
        (h_b1 : b.layer < s_obs.layerCount)
        (h_not_a : (a.layer, a.dir) ∉ placeLDGroupsLandings s sorted obs)
        (h_not_b : (b.layer, b.dir) ∉ placeLDGroupsLandings s sorted obs) :
        groundingEdge s_obs a b = groundingEdge s_result a b := by
    have h_len_ge : s_result.layerCount ≥ s_obs.layerCount := by
        unfold Shape.layerCount; rw [h_obs, h_result]
        exact placeLDGroups_length_ge s sorted obs
    have h_a2 : a.layer < s_result.layerCount := lt_of_lt_of_le h_a1 h_len_ge
    have h_b2 : b.layer < s_result.layerCount := lt_of_lt_of_le h_b1 h_len_ge
    have ha : QuarterPos.getDir (s_obs.layers.getD a.layer Layer.empty) a.dir =
              QuarterPos.getDir (s_result.layers.getD a.layer Layer.empty) a.dir := by
        rw [h_obs, h_result]
        exact (getDir_placeLDGroups_of_ne s sorted obs a.layer a.dir h_not_a).symm
    have hb : QuarterPos.getDir (s_obs.layers.getD b.layer Layer.empty) b.dir =
              QuarterPos.getDir (s_result.layers.getD b.layer Layer.empty) b.dir := by
        rw [h_obs, h_result]
        exact (getDir_placeLDGroups_of_ne s sorted obs b.layer b.dir h_not_b).symm
    exact groundingEdge_congr_of_getDir_getD_eq h_a1 h_a2 h_b1 h_b2 ha hb

/-- `takeWhile p l` の要素は述語 `p` を満たす。
    Mathlib の `List.mem_takeWhile_iff` 等価。 -/
private theorem takeWhile_pred_of_mem {α : Type _} (p : α → Bool) (l : List α) (x : α)
        (h : x ∈ l.takeWhile p) : p x = true := by
    induction l with
    | nil => simp at h
    | cons a tail ih =>
        simp only [List.takeWhile_cons] at h
        by_cases hpa : p a = true
        · rw [hpa] at h
          simp at h
          rcases h with h | h
          · subst h; exact hpa
          · exact ih h
        · simp [hpa] at h

/-- `placeLDGroupsLandings` の要素は sorted リスト内の何らかの FU の position に由来し、
    その layer 以下である。

    形式: `(lay, dir) ∈ placeLDGroupsLandings s sorted obs` ならば、
    `∃ u ∈ sorted, ∃ p ∈ u.positions, lay ≤ p.layer ∧ dir = p.dir`。

    用途: Sub-lemma #5/#6/#7 組立で「着地位置は settling FU の position 由来」を
    形式化する基礎。`lay ≤ p.layer` から `lay < s.layerCount`（p ∈ floatingUnits の位置）
    が従い、`groundingEdge` の端点妥当性が保証される。 -/
theorem placeLDGroupsLandings_mem_exists (s : Shape)
        (sorted : List FallingUnit) (obs : List Layer)
        {lay : Nat} {dir : Direction}
        (h : (lay, dir) ∈ placeLDGroupsLandings s sorted obs) :
        ∃ u ∈ sorted, ∃ p ∈ u.positions, lay ≤ p.layer ∧ dir = p.dir := by
    induction sorted, obs using placeLDGroups.induct s with
    | case1 obs => simp [placeLDGroupsLandings] at h
    | case2 obs v rest _ _ _ _ ih =>
        rw [placeLDGroupsLandings] at h
        simp only [List.mem_append] at h
        rcases h with h | h
        · rw [List.mem_flatMap] at h
          obtain ⟨u, hu, hu'⟩ := h
          rw [List.mem_map] at hu'
          obtain ⟨p, hp, hp_eq⟩ := hu'
          refine ⟨u, (List.takeWhile_sublist _).mem hu, p, hp, ?_, ?_⟩
          · have := Prod.mk.inj hp_eq; omega
          · have := Prod.mk.inj hp_eq; exact this.2.symm
        · obtain ⟨u, hu, rest_ex⟩ := ih h
          exact ⟨u, (List.dropWhile_sublist _).mem hu, rest_ex⟩

/-- `placeLDGroupsLandings` の強い版: 各着地位置は具体的な drop 距離 `d ≤ u.minLayer`
    を介して `(p.layer - d, p.dir)` と一致する。

    `d` は当該 FU が属するグループの LD（= `landingDistance first obs_k`）で、
    takeWhile 条件 `landingDistance u obs_k == landingDistance first obs_k` と
    `landingDistance_le_minLayer` から `d ≤ u.minLayer` が導かれる。

    用途: Telescoping sum (Sub-lemma #9 `sum_map_layer_landing_telescope` / `landing_sum_bound`)
    への接続時に、着地重み `(p.layer - d) + 1` の形を使うために必要。 -/
theorem placeLDGroupsLandings_mem_exists_drop (s : Shape)
        (sorted : List FallingUnit) (obs : List Layer)
        {lay : Nat} {dir : Direction}
        (h : (lay, dir) ∈ placeLDGroupsLandings s sorted obs) :
        ∃ u ∈ sorted, ∃ p ∈ u.positions, ∃ d,
            d ≤ u.minLayer ∧ lay = p.layer - d ∧ dir = p.dir := by
    induction sorted, obs using placeLDGroups.induct s with
    | case1 obs => simp [placeLDGroupsLandings] at h
    | case2 obs v rest _ _ _ _ ih =>
        rw [placeLDGroupsLandings] at h
        simp only [List.mem_append] at h
        rcases h with h | h
        · rw [List.mem_flatMap] at h
          obtain ⟨u, hu, hu'⟩ := h
          rw [List.mem_map] at hu'
          obtain ⟨p, hp, hp_eq⟩ := hu'
          have hu_mem : u ∈ v :: rest := (List.takeWhile_sublist _).mem hu
          have h_beq : (landingDistance u obs == landingDistance v obs) = true :=
              takeWhile_pred_of_mem _ (v :: rest) u hu
          have h_eq : landingDistance u obs = landingDistance v obs :=
              beq_iff_eq.mp h_beq
          have h_d_le : landingDistance u obs ≤ u.minLayer :=
              landingDistance_le_minLayer u obs
          refine ⟨u, hu_mem, p, hp, landingDistance v obs, ?_, ?_, ?_⟩
          · rw [← h_eq]; exact h_d_le
          · have := Prod.mk.inj hp_eq; exact this.1.symm
          · have := Prod.mk.inj hp_eq; exact this.2.symm
        · obtain ⟨u, hu, rest_ex⟩ := ih h
          exact ⟨u, (List.dropWhile_sublist _).mem hu, rest_ex⟩

/-- `placeLDGroupsLandings_mem_exists_drop` の強化版: FU の `minLayer ≥ 1`
    前提下で drop 距離 `d` の下限 `1 ≤ d` も得る。

    証明: `landingDistance_ge_one` で group 先頭 FU の LD `≥ 1` を取る。
    takeWhile 条件より他の FU の LD も同値なので全員 `d ≥ 1`。

    用途: Telescoping `landing_sum_bound` が要求する `1 ≤ d` を満たす形で
    着地位置由来を特徴付ける。 -/
theorem placeLDGroupsLandings_mem_exists_drop_ge_one
        (s : Shape) (sorted : List FallingUnit) (obs : List Layer)
        (h_ml : ∀ u ∈ sorted, 1 ≤ u.minLayer)
        {lay : Nat} {dir : Direction}
        (h : (lay, dir) ∈ placeLDGroupsLandings s sorted obs) :
        ∃ u ∈ sorted, ∃ p ∈ u.positions, ∃ d,
            1 ≤ d ∧ d ≤ u.minLayer ∧ lay = p.layer - d ∧ dir = p.dir := by
    induction sorted, obs using placeLDGroups.induct s with
    | case1 obs => simp [placeLDGroupsLandings] at h
    | case2 obs v rest _ _ _ _ ih =>
        rw [placeLDGroupsLandings] at h
        simp only [List.mem_append] at h
        rcases h with h | h
        · rw [List.mem_flatMap] at h
          obtain ⟨u, hu, hu'⟩ := h
          rw [List.mem_map] at hu'
          obtain ⟨p, hp, hp_eq⟩ := hu'
          have hu_mem : u ∈ v :: rest := (List.takeWhile_sublist _).mem hu
          have hv_mem : v ∈ v :: rest := List.mem_cons_self ..
          have hv_ml : 1 ≤ v.minLayer := h_ml v hv_mem
          have hv_ge : 1 ≤ landingDistance v obs := landingDistance_ge_one v obs hv_ml
          have h_beq : (landingDistance u obs == landingDistance v obs) = true :=
              takeWhile_pred_of_mem _ (v :: rest) u hu
          have h_eq : landingDistance u obs = landingDistance v obs :=
              beq_iff_eq.mp h_beq
          have h_d_le : landingDistance u obs ≤ u.minLayer :=
              landingDistance_le_minLayer u obs
          refine ⟨u, hu_mem, p, hp, landingDistance v obs, hv_ge, ?_, ?_, ?_⟩
          · rw [← h_eq]; exact h_d_le
          · have := Prod.mk.inj hp_eq; exact this.1.symm
          · have := Prod.mk.inj hp_eq; exact this.2.symm
        · have h_rest_ml : ∀ u ∈ ((v :: rest).dropWhile
                (fun u => landingDistance u obs == landingDistance v obs)),
                1 ≤ u.minLayer := fun u hu =>
              h_ml u ((List.dropWhile_sublist _).mem hu)
          obtain ⟨u, hu, rest_ex⟩ := ih h_rest_ml h
          exact ⟨u, (List.dropWhile_sublist _).mem hu, rest_ex⟩

/-- `placeLDGroupsLandings` の着地位置は元の shape のレイヤ範囲内にある。

    `sorted ⊆ floatingUnits s` の前提下で、任意の着地 `(lay, dir)` について
    `lay < s.layerCount` が保証される。

    証明: `placeLDGroupsLandings_mem_exists` で得た `p ∈ u.positions` に対し、
    `floatingUnits_positions_getQuarter` で `p.layer < s.layerCount`、
    さらに `lay ≤ p.layer` より従う。

    用途: Sub-lemma #5/#6/#7 で `groundingEdge_placeLDGroups_of_ne` を適用する
    際の端点妥当性 `a.layer < s_obs.layerCount` を満たすために必要。 -/
theorem placeLDGroupsLandings_layer_lt_layerCount (s : Shape)
        (sorted : List FallingUnit) (obs : List Layer)
        (h_sub : ∀ u ∈ sorted, u ∈ floatingUnits s)
        {lay : Nat} {dir : Direction}
        (h : (lay, dir) ∈ placeLDGroupsLandings s sorted obs) :
        lay < s.layerCount := by
    obtain ⟨u, hu, p, hp, hle, _⟩ := placeLDGroupsLandings_mem_exists s sorted obs h
    have hu_f := h_sub u hu
    have h_any : ((floatingUnits s).flatMap FallingUnit.positions).any (· == p) = true := by
        rw [List.any_eq_true]
        refine ⟨p, ?_, BEq.rfl⟩
        rw [List.mem_flatMap]
        exact ⟨u, hu_f, hp⟩
    have := (floatingUnits_positions_getQuarter s p h_any).1
    omega

/-- `placeLDGroupsLandings_mem_exists_drop_ge_one` の `sorted ⊆ floatingUnits s` 版。

    `floatingUnits_minLayer_ge_one` を介して `1 ≤ u.minLayer` を自動導出する。

    用途: waveStep 本体での settling FU リストは常に `floatingUnits s` の部分集合
    なので、この版を直接適用できる。 -/
theorem placeLDGroupsLandings_mem_exists_drop_ge_one_of_subset_fu
        (s : Shape) (sorted : List FallingUnit) (obs : List Layer)
        (h_sub : ∀ u ∈ sorted, u ∈ floatingUnits s)
        {lay : Nat} {dir : Direction}
        (h : (lay, dir) ∈ placeLDGroupsLandings s sorted obs) :
        ∃ u ∈ sorted, ∃ p ∈ u.positions, ∃ d,
            1 ≤ d ∧ d ≤ u.minLayer ∧ lay = p.layer - d ∧ dir = p.dir := by
    have h_ml : ∀ u ∈ sorted, 1 ≤ u.minLayer := fun u hu =>
        floatingUnits_minLayer_ge_one s u (h_sub u hu)
    exact placeLDGroupsLandings_mem_exists_drop_ge_one s sorted obs h_ml h

/-- `placeLDGroups` は `placeLDGroupsLandings` に含まれない位置で `QuarterPos.getQuarter`
    を保存する（shape-level）。

    前提: `s_obs.layers = obs` / `s_result.layers = placeLDGroups s sorted obs` +
    `pos.layer < s_obs.layerCount`。

    `getDir_placeLDGroups_of_ne` (list-level) を `getQuarter_eq_of_getDir_getD_eq`
    で shape-level に持ち上げる。

    用途: `groundedPositions_mono` / `groundedPositions_mono_of_edge` の仮定
    （非空象限の `getQuarter` 等しさ）を満たすために必要。Sub-lemma #5/#6/#7
    組立で obs → placeLDGroups 結果間の grounding 伝播に使う。 -/
theorem getQuarter_placeLDGroups_of_ne
        (s : Shape) (sorted : List FallingUnit) (obs : List Layer)
        (s_obs s_result : Shape)
        (h_obs : s_obs.layers = obs)
        (h_result : s_result.layers = placeLDGroups s sorted obs)
        (pos : QuarterPos)
        (h_valid : pos.layer < s_obs.layerCount)
        (h_not : (pos.layer, pos.dir) ∉ placeLDGroupsLandings s sorted obs) :
        QuarterPos.getQuarter s_result pos = QuarterPos.getQuarter s_obs pos := by
    have h_len_ge : s_result.layerCount ≥ s_obs.layerCount := by
        unfold Shape.layerCount; rw [h_obs, h_result]
        exact placeLDGroups_length_ge s sorted obs
    have h_valid2 : pos.layer < s_result.layerCount := lt_of_lt_of_le h_valid h_len_ge
    have h_gd : QuarterPos.getDir (s_obs.layers.getD pos.layer Layer.empty) pos.dir =
                QuarterPos.getDir (s_result.layers.getD pos.layer Layer.empty) pos.dir := by
        rw [h_obs, h_result]
        exact (getDir_placeLDGroups_of_ne s sorted obs pos.layer pos.dir h_not).symm
    exact getQuarter_eq_of_getDir_getD_eq h_valid2 h_valid h_gd.symm

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
-- Step 0.2 (waveStep_grounding_mono 前提): 着地スロットの非空保証
-- ============================================================

/-- `u ∈ floatingUnits s` かつ `p ∈ u.positions` なら `p.getQuarter s` が `some qv` となる
    象限は非空。`floatingUnits_positions_getQuarter` からの直接取り出し補題。 -/
theorem floatingUnits_quarter_nonEmpty (s : Shape) {u : FallingUnit}
        (hu : u ∈ floatingUnits s)
        {p : QuarterPos} (hp : p ∈ u.positions)
        {qv : Quarter} (hq : p.getQuarter s = some qv) : qv.isEmpty = false := by
    have hany : ((floatingUnits s).flatMap FallingUnit.positions).any (· == p) = true := by
        apply List.any_eq_true.mpr
        exact ⟨p, List.mem_flatMap.mpr ⟨u, hu, hp⟩, by simp⟩
    obtain ⟨_, ⟨q', hq_eq, hq_ne⟩, _⟩ := floatingUnits_positions_getQuarter s p hany
    rw [hq] at hq_eq
    cases hq_eq
    simpa using hq_ne

/-- 固定 `d` での foldl `placeFallingUnit` は、構成 FU が全て `floatingUnits s` に属するなら
    `getDir ≠ empty` を単調保存する。`isOccupied_placeFallingUnit_mono` の foldl 版。
    R-1 により `getDir ≠ empty` を基本単位として統一 (旧 `foldl_placeFU_isOccupied_mono`)。 -/
theorem foldl_placeFU_getDir_ne_empty_mono (s : Shape) (group : List FallingUnit)
        (obs : List Layer) (d : Nat)
        (h_sub : ∀ u ∈ group, u ∈ floatingUnits s)
        (lay : Nat) (dir : Direction)
        (h_ne : QuarterPos.getDir (obs.getD lay Layer.empty) dir ≠ Quarter.empty) :
        QuarterPos.getDir
            ((group.foldl (fun acc fu => placeFallingUnit s acc fu d) obs).getD lay Layer.empty)
            dir ≠ Quarter.empty := by
    -- 内部的には leaf の `isOccupied_placeFallingUnit_mono` に委譲する
    have h_occ : isOccupied obs lay dir = true :=
        isOccupied_of_getDir_ne_empty _ _ _ h_ne
    have h_occ_final :
            isOccupied (group.foldl (fun acc fu => placeFallingUnit s acc fu d) obs) lay dir
                = true := by
        clear h_ne
        induction group generalizing obs with
        | nil => simpa using h_occ
        | cons u rest ih =>
            simp only [List.foldl_cons]
            apply ih
            · intro v hv; exact h_sub v (List.mem_cons_of_mem _ hv)
            · apply isOccupied_placeFallingUnit_mono s obs u d lay dir
              · intro p hp qv hqe
                exact floatingUnits_quarter_nonEmpty s (h_sub u List.mem_cons_self) hp hqe
              · exact h_occ
    exact getDir_ne_empty_of_isOccupied _ _ _ h_occ_final

/-- `placeLDGroups` は、構成 FU が全て `floatingUnits s` に属するなら `getDir ≠ empty` を
    単調保存する。R-1 により `getDir` 形で統一 (旧 `isOccupied_placeLDGroups_mono`)。 -/
theorem placeLDGroups_getDir_ne_empty_mono (s : Shape) (sorted : List FallingUnit)
        (obs : List Layer)
        (h_sub : ∀ u ∈ sorted, u ∈ floatingUnits s)
        (lay : Nat) (dir : Direction)
        (h_ne : QuarterPos.getDir (obs.getD lay Layer.empty) dir ≠ Quarter.empty) :
        QuarterPos.getDir ((placeLDGroups s sorted obs).getD lay Layer.empty) dir
            ≠ Quarter.empty := by
    induction sorted, obs using placeLDGroups.induct s with
    | case1 obs => rw [placeLDGroups]; exact h_ne
    | case2 obs first rest _ _ _ _ ih =>
        rw [placeLDGroups]
        have h_group_sub : ∀ u ∈ (first :: rest).takeWhile
                (fun u => landingDistance u obs == landingDistance first obs),
                u ∈ floatingUnits s := by
            intro u hu; exact h_sub u ((List.takeWhile_sublist _).mem hu)
        have h_rem_sub : ∀ u ∈ (first :: rest).dropWhile
                (fun u => landingDistance u obs == landingDistance first obs),
                u ∈ floatingUnits s := by
            intro u hu; exact h_sub u ((List.dropWhile_sublist _).mem hu)
        apply ih h_rem_sub
        exact foldl_placeFU_getDir_ne_empty_mono s _ obs _ h_group_sub lay dir h_ne

/-- foldl `placeQuarter` の書き込み先で `getDir ≠ empty` が成立する。
    `foldl_placeQuarter_written_canFormBond` の `!qv.isEmpty` 版。 -/
theorem foldl_placeQuarter_written_getDir_ne_empty
        (s : Shape) (obs : List Layer) (positions : List QuarterPos) (dropDist : Nat)
        (lay : Nat) (dir : Direction)
        (h_written : ∃ p ∈ positions, p.layer - dropDist = lay ∧ p.dir = dir)
        (h_ne : ∀ p ∈ positions, ∃ qv, p.getQuarter s = some qv ∧ qv.isEmpty = false) :
        QuarterPos.getDir ((positions.foldl (fun obs p =>
            match p.getQuarter s with
            | some r => placeQuarter obs (p.layer - dropDist) p.dir r
            | none => obs) obs).getD lay Layer.empty) dir ≠ Quarter.empty := by
    induction positions generalizing obs with
    | nil => obtain ⟨p, hp, _⟩ := h_written; simp at hp
    | cons hd tl ih =>
        simp only [List.foldl_cons]
        set obs' := (match hd.getQuarter s with
                | some r => placeQuarter obs (hd.layer - dropDist) hd.dir r
                | none => obs) with h_obs'_def
        by_cases h_tl_has : ∃ p ∈ tl, p.layer - dropDist = lay ∧ p.dir = dir
        · exact ih obs' h_tl_has (fun p hp => h_ne p (List.mem_cons.mpr (Or.inr hp)))
        · obtain ⟨p, h_p_mem, h_p_lay, h_p_dir⟩ := h_written
          cases h_p_mem with
          | head =>
            obtain ⟨qv, hqv, hqv_ne⟩ := h_ne hd List.mem_cons_self
            have h_obs'_eq : obs' = placeQuarter obs (hd.layer - dropDist) hd.dir qv := by
                simp only [h_obs'_def, hqv]
            have h_tl_not : ∀ p ∈ tl, ¬(p.layer - dropDist = lay ∧ p.dir = dir) := by
                intro p hp hc; exact h_tl_has ⟨p, hp, hc.1, hc.2⟩
            have h_pres := foldl_placeQuarter_getDir_preserved s obs' tl dropDist lay dir h_tl_not
            have h_base : QuarterPos.getDir (obs'.getD lay Layer.empty) dir = qv := by
                subst h_p_lay; subst h_p_dir
                rw [h_obs'_eq, placeQuarter_getD _ _ _ _ _ (by omega), if_pos rfl,
                    QuarterPos.getDir_setDir_same]
            intro h_eq
            have h_combined : qv = Quarter.empty := by
                rw [← h_base]; rw [← h_pres]; exact h_eq
            subst h_combined
            simp [Quarter.isEmpty] at hqv_ne
          | tail _ h => exact absurd ⟨p, h, h_p_lay, h_p_dir⟩ h_tl_has

-- NOTE: `isOccupied_of_getDir_ne_empty` / `getDir_ne_empty_of_isOccupied`
-- は `Gravity/Defs.lean` (isOccupied 定義直後) に移動済み (R-2-1)。

/-- 固定 `d` の group foldl 内で、いずれかの FU の position が `(lay, dir)` に書き込むなら
    結果の `getDir` は非空。R-1 による getDir 版統一 (旧 `foldl_placeFU_written_isOccupied`)。 -/
theorem foldl_placeFU_written_getDir_ne_empty (s : Shape) (group : List FallingUnit)
        (obs : List Layer) (d : Nat)
        (h_sub : ∀ u ∈ group, u ∈ floatingUnits s)
        (lay : Nat) (dir : Direction)
        (h_written : ∃ u ∈ group, ∃ p ∈ u.positions, p.layer - d = lay ∧ p.dir = dir) :
        QuarterPos.getDir
            ((group.foldl (fun acc fu => placeFallingUnit s acc fu d) obs).getD lay Layer.empty)
            dir ≠ Quarter.empty := by
    induction group generalizing obs with
    | nil => obtain ⟨u, hu, _⟩ := h_written; simp at hu
    | cons u rest ih =>
        simp only [List.foldl_cons]
        by_cases h_rest_has :
                ∃ v ∈ rest, ∃ p ∈ v.positions, p.layer - d = lay ∧ p.dir = dir
        · exact ih _ (fun v hv => h_sub v (List.mem_cons_of_mem _ hv)) h_rest_has
        · obtain ⟨w, hw_mem, p, hp, h_p_lay, h_p_dir⟩ := h_written
          cases hw_mem with
          | head =>
            have h_u_float : u ∈ floatingUnits s := h_sub u List.mem_cons_self
            have h_ne_pos : ∀ q ∈ u.positions,
                    ∃ qv, q.getQuarter s = some qv ∧ qv.isEmpty = false := by
                intro q hq
                have hany : ((floatingUnits s).flatMap FallingUnit.positions).any (· == q)
                        = true := by
                    apply List.any_eq_true.mpr
                    exact ⟨q, List.mem_flatMap.mpr ⟨u, h_u_float, hq⟩, by simp⟩
                obtain ⟨_, hqv, _⟩ := floatingUnits_positions_getQuarter s q hany
                obtain ⟨qval, hqval_eq, hqval_ne⟩ := hqv
                exact ⟨qval, hqval_eq, by simpa using hqval_ne⟩
            have h_written_q : ∃ q ∈ u.positions, q.layer - d = lay ∧ q.dir = dir :=
                ⟨p, hp, h_p_lay, h_p_dir⟩
            have h_occ_after_u : QuarterPos.getDir
                    ((placeFallingUnit s obs u d).getD lay Layer.empty) dir
                    ≠ Quarter.empty := by
                unfold placeFallingUnit
                exact foldl_placeQuarter_written_getDir_ne_empty s obs u.positions d lay dir
                    h_written_q h_ne_pos
            exact foldl_placeFU_getDir_ne_empty_mono s rest _ d
                (fun v hv => h_sub v (List.mem_cons_of_mem _ hv)) lay dir h_occ_after_u
          | tail _ h =>
            exact absurd ⟨w, h, p, hp, h_p_lay, h_p_dir⟩ h_rest_has

/-- Step 0.2: 任意の着地位置 `(lay, dir) ∈ placeLDGroupsLandings s sorted obs` について、
    結果 `placeLDGroups s sorted obs` の当該スロットは非空象限を持つ。

    `waveStep_grounding_mono` の `h_seed_landing` 供給に直接使用される基盤補題。

    証明戦略:
    - `placeLDGroups.induct` で group 単位に分解。
    - group_landings ケースでは `foldl_placeFU_written_getDir_ne_empty` で obs' に
      `getDir ≠ empty` を立て、`placeLDGroups_getDir_ne_empty_mono` で remaining 以降も保存。
    - rest_landings ケースでは IH を適用。 -/
theorem placeLDGroups_landing_nonEmpty
        (s : Shape) (sorted : List FallingUnit) (obs : List Layer)
        (h_sub : ∀ u ∈ sorted, u ∈ floatingUnits s)
        (lay : Nat) (dir : Direction)
        (h_landing : (lay, dir) ∈ placeLDGroupsLandings s sorted obs) :
        QuarterPos.getDir ((placeLDGroups s sorted obs).getD lay Layer.empty) dir
            ≠ Quarter.empty := by
    induction sorted, obs using placeLDGroups.induct s with
    | case1 obs => simp [placeLDGroupsLandings] at h_landing
    | case2 obs first rest d group remaining obs' ih =>
        rw [placeLDGroupsLandings] at h_landing
        simp only [List.mem_append] at h_landing
        rw [placeLDGroups]
        have h_group_sub : ∀ u ∈ group, u ∈ floatingUnits s := by
            intro u hu; exact h_sub u ((List.takeWhile_sublist _).mem hu)
        have h_rem_sub : ∀ u ∈ remaining, u ∈ floatingUnits s := by
            intro u hu; exact h_sub u ((List.dropWhile_sublist _).mem hu)
        rcases h_landing with h_group | h_rest
        · rw [List.mem_flatMap] at h_group
          obtain ⟨u, hu, h_map⟩ := h_group
          rw [List.mem_map] at h_map
          obtain ⟨p, hp, h_eq⟩ := h_map
          have h_p_lay : p.layer - d = lay := (Prod.mk.inj h_eq).1
          have h_p_dir : p.dir = dir := (Prod.mk.inj h_eq).2
          have h_written :
                  ∃ u ∈ group, ∃ p ∈ u.positions, p.layer - d = lay ∧ p.dir = dir :=
              ⟨u, hu, p, hp, h_p_lay, h_p_dir⟩
          have h_ne_obs' : QuarterPos.getDir (obs'.getD lay Layer.empty) dir
                  ≠ Quarter.empty :=
              foldl_placeFU_written_getDir_ne_empty s group obs d h_group_sub lay dir h_written
          exact placeLDGroups_getDir_ne_empty_mono s remaining obs' h_rem_sub lay dir h_ne_obs'
        · exact ih h_rem_sub h_rest

-- ============================================================
-- Step B3b-α: `placeLDGroupsLandings_isOccupied_obs_false` への準備補題群
--
-- 目標: `waveStep_grounding_mono` の `h_edge_landing` 枝を exfalso で閉じるための
-- 基盤補題。`placeLDGroupsLandings` に属する任意着地 `(lay, dir)` について初期 `obs`
-- で `isOccupied obs lay dir = false` を示す。
--
-- 構成:
--   α1: `settling_position_below_empty_obs` — u ∈ sorted, p ∈ u.positions,
--        p.layer ≥ 1 で obs (clearPositions) 下の (p.layer-1, p.dir) が空
--   α2: `landingDistance_not_occupied_at_landing_d_one` — d=1 ケースで α1 適用
--   α3: `foldl_placeFU_isOccupied_antimono` — foldl mono の対偶（持続性）
--   α4: `placeLDGroupsLandings_isOccupied_obs_false` — 本丸
-- ============================================================

/-- Step B3b-α3: `foldl_placeFU_getDir_ne_empty_mono` の contrapositive 形。
    foldl 適用後に `isOccupied` が `false` なら、初期 `obs` でも `false`。

    α4 の rest case で IH（`isOccupied obs' lay dir = false`）から obs の空性を
    取り出すのに使う。`placeFallingUnit` の occupancy 単調性 (`placeFallingUnit`
    は書き込みのみ、クリアしない) に基づく。 -/
theorem foldl_placeFU_isOccupied_antimono (s : Shape) (group : List FallingUnit)
        (obs : List Layer) (d : Nat)
        (h_sub : ∀ u ∈ group, u ∈ floatingUnits s)
        (lay : Nat) (dir : Direction)
        (h : isOccupied (group.foldl (fun acc fu => placeFallingUnit s acc fu d) obs) lay dir
                = false) :
        isOccupied obs lay dir = false := by
    by_contra h_true
    rw [Bool.not_eq_false] at h_true
    have h_ne : QuarterPos.getDir (obs.getD lay Layer.empty) dir ≠ Quarter.empty :=
        getDir_ne_empty_of_isOccupied _ _ _ h_true
    have h_ne_final := foldl_placeFU_getDir_ne_empty_mono s group obs d h_sub lay dir h_ne
    have h_occ_final :=
        isOccupied_of_getDir_ne_empty
            (group.foldl (fun acc fu => placeFallingUnit s acc fu d) obs) lay dir h_ne_final
    rw [h_occ_final] at h
    exact Bool.noConfusion h

end Gravity
