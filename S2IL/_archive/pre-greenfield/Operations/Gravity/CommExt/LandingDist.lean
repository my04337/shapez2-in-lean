-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity.CommExt.FloatUnits

namespace Gravity

open _root_.QuarterPos (getQuarter_rotate180)

-- ============================================================
-- S1 Sub-lemma #9 基盤: 着地合計の望遠鏡（arithmetic）
-- ============================================================

-- `sum_map_layer_landing_telescope` / `landing_sum_bound` は
-- `S2IL/Operations/Gravity/CommExt/Arith.lean` に分離済み（2026-04-21）。

/-- cluster FU の positions の各要素は s で `canFormBond = true` の象限を持つ。

    floatingUnits の cluster は `allStructuralClustersList s` の filter から来るため
    `cluster_position_bondable` が適用できる。 -/
theorem floatingUnits_cluster_positions_canFormBond (s : Shape) (ps : List QuarterPos)
        (hps : .cluster ps ∈ floatingUnits s) (p : QuarterPos) (hp : p ∈ ps) :
        ∃ qv, p.getQuarter s = some qv ∧ qv.canFormBond = true := by
    simp only [floatingUnits] at hps
    simp only [List.mem_append, List.mem_map] at hps
    rcases hps with ⟨c, hc, hceq⟩ | ⟨_, _, h⟩
    · cases hceq
      exact cluster_position_bondable s (List.mem_of_mem_filter hc) hp
    · exact absurd h (by simp)

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

-- ============================================================
-- S1 基盤補題: minLayer 下界
-- ============================================================

/-- floatingUnits の全 FU は minLayer ≥ 1 を持つ。
    レイヤ 0 の非空位置は BFS シードで常に接地されるため、浮遊 FU はレイヤ 0 に位置を持てない -/
theorem floatingUnits_minLayer_ge_one (s : Shape) (u : FallingUnit)
        (hu : u ∈ floatingUnits s) : u.minLayer ≥ 1 := by
    by_contra h_lt
    have hml0 : u.minLayer = 0 := Nat.lt_one_iff.mp (not_le.mp h_lt)
    have h_ne := floatingUnits_positions_ne_nil s u hu
    obtain ⟨p, hp_mem, hp_layer⟩ := minLayer_witness u h_ne
    rw [hml0] at hp_layer
    have h_any : ((floatingUnits s).flatMap FallingUnit.positions).any (· == p) = true :=
        List.any_eq_true.mpr ⟨p, List.mem_flatMap.mpr ⟨u, hu, hp_mem⟩, BEq.rfl⟩
    obtain ⟨h_valid, ⟨q, hq, hq_ne⟩, h_ug⟩ := floatingUnits_positions_getQuarter s p h_any
    have h_av : p ∈ QuarterPos.allValid s := by
        rw [QuarterPos.allValid, List.mem_flatMap]
        exact ⟨p.layer, List.mem_range.mpr h_valid,
            List.mem_map.mpr ⟨p.dir, List.mem_of_elem_eq_true (by cases p.dir <;> rfl), rfl⟩⟩
    have h_ne' : q.isEmpty = false := by cases q <;> simp_all [Quarter.isEmpty]
    exact h_ug (layer_zero_nonempty_grounded s p h_av hp_layer q hq h_ne')

/-- settling FU の minLayer ≥ 1 (floatingUnits_minLayer_ge_one の filter 版) -/
theorem settling_minLayer_ge_one (s : Shape)
        {P : FallingUnit → Bool} {u : FallingUnit}
        (hu : u ∈ (floatingUnits s).filter P) : u.minLayer ≥ 1 := by
    rw [List.mem_filter] at hu
    exact floatingUnits_minLayer_ge_one s u hu.1

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

-- ============================================================
-- S1 #4: pin singleton 着地位置空性の基盤補題群
-- ============================================================

/-- `isOccupied` は `QuarterPos.getQuarter` 経由で書き換えられる。
    橋渡し補題: `isOccupied obs l d ↔ getQuarter (shape with layers = obs) ⟨l,d⟩` の空性。 -/
theorem isOccupied_eq_getQuarter (s : Shape) (l : Nat) (d : Direction) :
        isOccupied s.layers l d = (match QuarterPos.getQuarter s ⟨l, d⟩ with
            | some q => !q.isEmpty
            | none => false) := by
    simp only [isOccupied, QuarterPos.getQuarter]
    cases s.layers[l]? <;> rfl

/-- `clearPositions` は `(l, d) ∉ ps` なる位置で `isOccupied` を保存する。 -/
theorem isOccupied_clearPositions_of_not_mem
        (s : Shape) (ps : List QuarterPos) (l : Nat) (d : Direction)
        (h_nps : (ps.any (· == ⟨l, d⟩)) = false)
        (h_lt : l < s.layerCount) :
        isOccupied (s.clearPositions ps).layers l d = isOccupied s.layers l d := by
    rw [isOccupied_eq_getQuarter, isOccupied_eq_getQuarter]
    have h_gq := QuarterPos.getQuarter_clearPositions s ps ⟨l, d⟩ h_lt
    rw [h_nps] at h_gq
    simp only [Bool.false_eq_true, if_false] at h_gq
    rw [h_gq]

/-- `FallingUnit.pin p` が `floatingUnits s` に属すとき、
    `p` は有効位置でありピン象限を持ち非接地である。 -/
theorem pin_fu_properties (s : Shape) (p : QuarterPos)
        (hp_fu : FallingUnit.pin p ∈ floatingUnits s) :
        p ∈ QuarterPos.allValid s ∧ QuarterPos.getQuarter s p = some .pin
            ∧ p ∉ groundedPositions s := by
    simp only [floatingUnits, List.mem_append, List.mem_map, List.mem_filter] at hp_fu
    rcases hp_fu with ⟨c, ⟨_, _⟩, hc_eq⟩ | ⟨p', ⟨hp'_iso, h_ng⟩, hp_eq⟩
    · cases hc_eq
    · have h_p_eq : p' = p := FallingUnit.pin.inj hp_eq
      rw [h_p_eq] at hp'_iso h_ng
      unfold allIsolatedPins at hp'_iso
      rw [List.mem_filter] at hp'_iso
      obtain ⟨h_av, h_pin⟩ := hp'_iso
      refine ⟨h_av, ?_, ?_⟩
      · cases hq : QuarterPos.getQuarter s p with
        | none => rw [hq] at h_pin; simp at h_pin
        | some q =>
          rw [hq] at h_pin
          cases q <;> simp_all
      · exact decide_eq_true_eq.mp h_ng

/-- S1 #4 d ≥ 2 ケース: ピン singleton FU が `landingDistance ≥ 2` で着地する場合、
    着地位置 `(p.layer - d, p.dir)` は `obs` で空。
    `landingDistance_not_occupied_at_landing` の直接的な系。 -/
theorem pin_singleton_landing_empty_d_ge_two
        (s : Shape) (p : QuarterPos)
        (hp_fu : FallingUnit.pin p ∈ floatingUnits s)
        (obs : List Layer)
        (hd_ge : landingDistance (FallingUnit.pin p) obs ≥ 2) :
        isOccupied obs
            (p.layer - landingDistance (FallingUnit.pin p) obs) p.dir = false := by
    have h_min : (FallingUnit.pin p).minLayer ≥ 1 :=
        floatingUnits_minLayer_ge_one s _ hp_fu
    have h_ne : (FallingUnit.pin p).positions ≠ [] := by
        simp [FallingUnit.positions]
    have :=
        landingDistance_not_occupied_at_landing (FallingUnit.pin p) obs h_ne h_min hd_ge
    exact this p (by simp [FallingUnit.positions])

/-- S1 #4 d = 1 ∧ `p.layer = 1` ケース: ピン singleton FU の着地位置 `(0, p.dir)` は
    `obs = (s.clearPositions ps).layers` で空。
    `ungrounded_pin_layer_one_below_empty` + `isOccupied_clearPositions_of_not_mem` の合成。
    前提: `ps` の全位置が layer ≥ 1（settling が最小 minLayer = 1 であることから）。 -/
theorem pin_singleton_landing_empty_d_one_at_floor
        (s : Shape) (p : QuarterPos)
        (hp_fu : FallingUnit.pin p ∈ floatingUnits s)
        (h_layer : p.layer = 1)
        (ps : List QuarterPos)
        (h_ps_layer : ∀ q ∈ ps, q.layer ≥ 1) :
        isOccupied (s.clearPositions ps).layers 0 p.dir = false := by
    obtain ⟨h_av, h_pin, h_ug⟩ := pin_fu_properties s p hp_fu
    have h_lc : 0 < s.layerCount := by
        have := allValid_mem_layer_lt' h_av
        rw [h_layer] at this; omega
    have h_nps : (ps.any (· == ⟨0, p.dir⟩)) = false := by
        rw [List.any_eq_false]; intro q hq hq_eq
        have h_q_eq := eq_of_beq hq_eq
        have h_q_layer : q.layer = 0 := by rw [h_q_eq]
        have := h_ps_layer q hq; omega
    rw [isOccupied_clearPositions_of_not_mem s ps 0 p.dir h_nps h_lc]
    exact ungrounded_pin_layer_one_below_empty s p h_av h_pin h_layer h_ug

/-- S1 #4 d = 1 ∧ `p.layer ≥ 2` ケース: ピン singleton FU の着地位置 `(p.layer - 1, p.dir)` は
    `obs = (s.clearPositions ps).layers` で空。
    obstacle 接触による着地を扱う。

    証明は背理法: 着地位置が非空と仮定すると、
    - 当該位置は `ps` に含まれない（`ps` の全レイヤ ≥ p.layer > p.layer - 1）
    - よって `s` でも非空
    - 接地の場合: `grounded_of_edge` によりピン `p` が接地 → 仮定矛盾
    - 非接地の場合: `ungrounded_in_floatingUnits_positions` により何らかの FU
      `u ∈ floatingUnits s` に含まれ、`u.minLayer ≤ p.layer - 1 < p.layer`
      → `h_min_fu` の最小性と矛盾。 -/
theorem pin_singleton_landing_empty_d_one_obstacle
        (s : Shape) (p : QuarterPos)
        (hp_fu : FallingUnit.pin p ∈ floatingUnits s)
        (h_min_fu : ∀ v ∈ floatingUnits s, v.minLayer ≥ p.layer)
        (h_layer : p.layer ≥ 2)
        (ps : List QuarterPos)
        (h_ps_layer : ∀ q ∈ ps, q.layer ≥ p.layer) :
        isOccupied (s.clearPositions ps).layers (p.layer - 1) p.dir = false := by
    by_contra h_occ
    rw [Bool.not_eq_false] at h_occ
    let r : QuarterPos := ⟨p.layer - 1, p.dir⟩
    have h_r_layer : r.layer = p.layer - 1 := rfl
    have h_r_dir : r.dir = p.dir := rfl
    have h_r_nps : (ps.any (· == r)) = false := by
        rw [List.any_eq_false]; intro q hq hq_eq
        have h_q_eq := eq_of_beq hq_eq
        have : q.layer = p.layer - 1 := by rw [h_q_eq]
        have := h_ps_layer q hq; omega
    obtain ⟨h_av, h_pin, h_ug⟩ := pin_fu_properties s p hp_fu
    have h_p_lt : p.layer < s.layerCount := allValid_mem_layer_lt' h_av
    have h_r_lt : r.layer < s.layerCount := by rw [h_r_layer]; omega
    rw [isOccupied_clearPositions_of_not_mem s ps (p.layer - 1) p.dir h_r_nps h_r_lt] at h_occ
    rw [isOccupied_eq_getQuarter] at h_occ
    have h_rq : ∃ q, QuarterPos.getQuarter s r = some q ∧ q.isEmpty = false := by
        cases hq : QuarterPos.getQuarter s r with
        | none => rw [hq] at h_occ; simp at h_occ
        | some q =>
          rw [hq] at h_occ
          refine ⟨q, rfl, ?_⟩
          simp only [Bool.not_eq_true'] at h_occ; exact h_occ
    obtain ⟨qq, h_rq_eq, h_qq_ne⟩ := h_rq
    -- groundingEdge s r p = true
    have h_gc : isGroundingContact s r p = true := by
        simp only [isGroundingContact]
        rw [h_rq_eq, h_pin]
        have h_pin_ne : Quarter.isEmpty Quarter.pin = false := by decide
        have h_va : LayerIndex.verticallyAdjacent r.layer p.layer = true := by
            rw [h_r_layer]; simp [LayerIndex.verticallyAdjacent]; omega
        simp only [h_qq_ne, h_pin_ne, Bool.not_false, Bool.and_true, h_va]
        rw [h_r_dir]; simp
    have h_upw : isUpwardGroundingContact s r p = true :=
        isGroundingContact_to_isUpwardGroundingContact h_gc
            (by rw [h_r_layer]; omega)
    have h_edge : groundingEdge s r p = true :=
        groundingEdge_of_isUpwardGroundingContact h_upw
    by_cases h_r_grd : r ∈ groundedPositions s
    · exact h_ug (grounded_of_edge h_r_grd h_edge)
    · have h_rq_ne : ∃ q, QuarterPos.getQuarter s r = some q ∧ !q.isEmpty = true :=
          ⟨qq, h_rq_eq, by simp [h_qq_ne]⟩
      have h_any :=
        ungrounded_in_floatingUnits_positions s r h_r_lt h_rq_ne h_r_grd
      rw [List.any_eq_true] at h_any
      obtain ⟨r', hr'_in, hr'_eq⟩ := h_any
      have hr'_r : r' = r := eq_of_beq hr'_eq
      rw [List.mem_flatMap] at hr'_in
      obtain ⟨u, hu_in, hu_pos⟩ := hr'_in
      rw [hr'_r] at hu_pos
      have h_u_min_le : u.minLayer ≤ r.layer :=
          minLayer_le_layer hu_pos u.minLayer (le_refl _)
      have h_u_min_ge := h_min_fu u hu_in
      rw [h_r_layer] at h_u_min_le
      omega

/-- **S1 Sub-lemma #4**: ピン singleton FU の着地位置は `obs` で空である。
    三ケース合成:
    - `d ≥ 2`: `pin_singleton_landing_empty_d_ge_two`
    - `d = 1 ∧ p.layer = 1`: `pin_singleton_landing_empty_d_one_at_floor`
    - `d = 1 ∧ p.layer ≥ 2`: `pin_singleton_landing_empty_d_one_obstacle`

    前提:
    - `FallingUnit.pin p ∈ floatingUnits s`（pin が浮遊中）
    - `∀ v ∈ floatingUnits s, v.minLayer ≥ p.layer`（pin が最小 minLayer を持つ — settling 条件）
    - `∀ q ∈ ps, q.layer ≥ p.layer`（`ps` = settling 位置集合の性質） -/
theorem pin_singleton_landing_empty
        (s : Shape) (p : QuarterPos)
        (hp_fu : FallingUnit.pin p ∈ floatingUnits s)
        (h_min_fu : ∀ v ∈ floatingUnits s, v.minLayer ≥ p.layer)
        (ps : List QuarterPos)
        (h_ps_layer : ∀ q ∈ ps, q.layer ≥ p.layer) :
        isOccupied (s.clearPositions ps).layers
            (p.layer - landingDistance (FallingUnit.pin p) (s.clearPositions ps).layers)
            p.dir = false := by
    set obs := (s.clearPositions ps).layers with h_obs_def
    set d := landingDistance (FallingUnit.pin p) obs with h_d_def
    have h_min_p : p.layer ≥ 1 := by
        have h := floatingUnits_minLayer_ge_one s _ hp_fu
        simp [FallingUnit.minLayer, FallingUnit.positions] at h
        exact h
    by_cases hd2 : d ≥ 2
    · exact pin_singleton_landing_empty_d_ge_two s p hp_fu obs hd2
    · -- d ≤ 1; d ≥ 1 from minLayer ≥ 1 → d = 1
      have h_d_ge_one : d ≥ 1 := by
          have h := landingDistance_ge_one (FallingUnit.pin p) obs
          simp [FallingUnit.minLayer, FallingUnit.positions] at h
          exact h h_min_p
      have hd1 : d = 1 := by omega
      rw [hd1]
      by_cases hpl : p.layer = 1
      · have hpos : p.layer - 1 = 0 := by omega
        rw [hpos]
        exact pin_singleton_landing_empty_d_one_at_floor s p hp_fu hpl ps
            (fun q hq => le_trans h_min_p (h_ps_layer q hq))
      · have h_p_ge : p.layer ≥ 2 := by omega
        exact pin_singleton_landing_empty_d_one_obstacle s p hp_fu h_min_fu
            h_p_ge ps h_ps_layer

/-- Pin FU の landing 端点は `s_obs` 側で空な象限を持つため、`groundingEdge` が偽となる。

    Sub-lemma #6 (`placing_pin_empty_preserves_grounding`) の左端点版:
    `pin_singleton_landing_empty` (isOccupied obs landing = false) に
    `isOccupied_eq_getQuarter` + `groundingEdge_false_of_empty_quarter` を連鎖させた。

    用途: `waveStep_grounding_mono` の `h_edge_landing` で pin 側を vacuous に閉じる。 -/
theorem pin_landing_groundingEdge_false_left
        (s : Shape) (p : QuarterPos)
        (hp_fu : FallingUnit.pin p ∈ floatingUnits s)
        (h_min_fu : ∀ v ∈ floatingUnits s, v.minLayer ≥ p.layer)
        (ps : List QuarterPos)
        (h_ps_layer : ∀ q ∈ ps, q.layer ≥ p.layer)
        (s_obs : Shape) (h_obs : s_obs.layers = (s.clearPositions ps).layers)
        (b : QuarterPos) :
        groundingEdge s_obs
            ⟨p.layer - landingDistance (FallingUnit.pin p) (s.clearPositions ps).layers, p.dir⟩
            b = false := by
    apply groundingEdge_false_of_empty_quarter
    intro q hq
    have h_occ := pin_singleton_landing_empty s p hp_fu h_min_fu ps h_ps_layer
    set lay := p.layer - landingDistance (FallingUnit.pin p) (s.clearPositions ps).layers
    have h_occ' : isOccupied s_obs.layers lay p.dir = false := by rw [h_obs]; exact h_occ
    have h_bridge := isOccupied_eq_getQuarter s_obs lay p.dir
    rw [h_bridge] at h_occ'
    rw [hq] at h_occ'
    simpa using h_occ'

/-- `pin_landing_groundingEdge_false_left` の対称版（pin landing が `b` 側）。 -/
theorem pin_landing_groundingEdge_false_right
        (s : Shape) (p : QuarterPos)
        (hp_fu : FallingUnit.pin p ∈ floatingUnits s)
        (h_min_fu : ∀ v ∈ floatingUnits s, v.minLayer ≥ p.layer)
        (ps : List QuarterPos)
        (h_ps_layer : ∀ q ∈ ps, q.layer ≥ p.layer)
        (s_obs : Shape) (h_obs : s_obs.layers = (s.clearPositions ps).layers)
        (a : QuarterPos) :
        groundingEdge s_obs a
            ⟨p.layer - landingDistance (FallingUnit.pin p) (s.clearPositions ps).layers, p.dir⟩
            = false := by
    apply groundingEdge_false_of_empty_quarter_right
    intro q hq
    have h_occ := pin_singleton_landing_empty s p hp_fu h_min_fu ps h_ps_layer
    set lay := p.layer - landingDistance (FallingUnit.pin p) (s.clearPositions ps).layers
    have h_occ' : isOccupied s_obs.layers lay p.dir = false := by rw [h_obs]; exact h_occ
    have h_bridge := isOccupied_eq_getQuarter s_obs lay p.dir
    rw [h_bridge] at h_occ'
    rw [hq] at h_occ'
    simpa using h_occ'

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

/-- `foldl_placeQuarter_written_canFormBond` の shape-level 版。
    書き込み先 `(lay, dir)` で `QuarterPos.getQuarter s_result ⟨lay, dir⟩ = some qv ∧ qv.canFormBond = true`
    を得る。

    用途: Sub-lemma #6/#7 組立時の `h_seed_landing` で
    `(p.layer, p.dir) ∈ placeLDGroupsLandings` のときに `!qv.isEmpty = true` を
    直接供給する（`canFormBond = true → !isEmpty = true` は Quarter レベルで自明）。

    `foldl_placeQuarter_written_canFormBond` が返す list-level `getDir` を
    `QuarterPos.getQuarter` に持ち上げるだけの薄い橋渡し。 -/
theorem foldl_placeQuarter_written_getQuarter_canFormBond
    (s : Shape) (obs : List Layer) (positions : List QuarterPos) (dropDist : Nat)
    (lay : Nat) (dir : Direction)
    (s_result : Shape)
    (h_result : s_result.layers = positions.foldl (fun obs p =>
        match p.getQuarter s with
        | some r => placeQuarter obs (p.layer - dropDist) p.dir r
        | none => obs) obs)
    (h_valid : lay < s_result.layerCount)
    (h_written : ∃ p ∈ positions, p.layer - dropDist = lay ∧ p.dir = dir)
    (h_bond : ∀ p ∈ positions, ∃ qv, p.getQuarter s = some qv ∧ qv.canFormBond = true) :
    ∃ qv, QuarterPos.getQuarter s_result ⟨lay, dir⟩ = some qv ∧ qv.canFormBond = true := by
  obtain ⟨qv, h_getDir, h_bond_qv⟩ :=
    foldl_placeQuarter_written_canFormBond s obs positions dropDist lay dir h_written h_bond
  refine ⟨qv, ?_, h_bond_qv⟩
  have h_lt : lay < s_result.layers.length := by
    simpa [Shape.layerCount] using h_valid
  have h_getd : s_result.layers.getD lay Layer.empty = s_result.layers[lay] :=
    (List.getElem_eq_getD Layer.empty).symm
  unfold QuarterPos.getQuarter
  rw [List.getElem?_eq_getElem h_lt]
  simp only [Option.some.injEq]
  show QuarterPos.getDir s_result.layers[lay] dir = qv
  rw [← h_getd, h_result]
  exact h_getDir

end Gravity
