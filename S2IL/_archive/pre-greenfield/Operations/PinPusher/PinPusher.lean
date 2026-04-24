-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity
import S2IL.Kernel.Transform.Rotate
import S2IL.Operations.Shatter.Shatter
import S2IL.Operations.Stacker.Stacker
import S2IL.Operations.Settled
import S2IL.Shape.GameConfig

/-!
# PinPusher (ピン押し機)

ピン押し機の動作を定義する。

## 概要

ピン押し機は以下の手順でシェイプを加工する:

1. **レイヤ持ち上げ**: 全レイヤを1つ上に持ち上げる（最下層に空レイヤを挿入）
2. **ピン生成**: 元の第1レイヤ（持ち上げ後の第2レイヤ）の非空象限に対して、
   新しい最下層にピン (`P-`) を配置する
3. **レイヤ上限処理**: レイヤ数が上限を超えた場合:
   a. 超過レイヤの結晶クラスタを砕け散らせる
   b. レイヤ数を上限に切り詰める
   c. 落下処理を実行する

持ち上げとピン生成の段階では、結晶の砕け散りや落下は発生しない。
-/

namespace PinPusher

-- ============================================================
-- ステップ 1: レイヤ持ち上げ
-- ============================================================

/-- 全レイヤを1つ上に持ち上げる（最下層に空レイヤを挿入） -/
def liftUp (s : Shape) : Shape :=
    ⟨Layer.empty :: s.layers, by simp only [ne_eq, reduceCtorEq, not_false_eq_true]⟩

/-- liftUp 後のレイヤ数は元のレイヤ数 + 1 -/
theorem liftUp_layerCount (s : Shape) :
        (liftUp s).layerCount = s.layerCount + 1 := by
    simp only [Shape.layerCount, liftUp, List.length_cons]

-- ============================================================
-- ステップ 2: ピン生成
-- ============================================================

/-- 元の最下層レイヤの非空象限に対してピンを生成し、新しい最下層に配置する -/
def generatePins (lifted : Shape) (originalBottom : Layer) : Shape :=
    let pinNe := if originalBottom.ne.isEmpty then Quarter.empty else Quarter.pin
    let pinSe := if originalBottom.se.isEmpty then Quarter.empty else Quarter.pin
    let pinSw := if originalBottom.sw.isEmpty then Quarter.empty else Quarter.pin
    let pinNw := if originalBottom.nw.isEmpty then Quarter.empty else Quarter.pin
    let pinLayer : Layer := ⟨pinNe, pinSe, pinSw, pinNw⟩
    ⟨pinLayer :: lifted.layers.tail, by simp only [ne_eq, reduceCtorEq, not_false_eq_true]⟩

-- ============================================================
-- rotate180 等変性補題
-- ============================================================

/-- liftUp は rotate180 と可換 -/
@[aesop norm simp] theorem liftUp_rotate180 (s : Shape) :
        (liftUp s).rotate180 = liftUp s.rotate180 := by
    ext i
    simp only [liftUp, Shape.rotate180, Shape.mapLayers, List.map_cons]
    cases i with
    | zero =>
        simp only [List.getElem?_cons_zero, Layer.rotate180, Layer.rotateCW, Layer.empty]
    | succ n => simp only [List.getElem?_cons_succ, List.getElem?_map]

/-- generatePins は rotate180 と可換 -/
@[aesop norm simp] theorem generatePins_rotate180 (lifted : Shape) (originalBottom : Layer) :
        (generatePins lifted originalBottom).rotate180 =
        generatePins lifted.rotate180 originalBottom.rotate180 := by
    simp only [generatePins, Shape.rotate180, Shape.mapLayers,
        Layer.rotate180, Layer.rotateCW, List.map_cons]
    congr 1; congr 1
    exact List.map_tail

-- ============================================================
-- rotateCW 等変性補題
-- ============================================================

/-- liftUp は rotateCW と可換 -/
@[aesop norm simp] theorem liftUp_rotateCW (s : Shape) :
        (liftUp s).rotateCW = liftUp s.rotateCW := by
    ext i
    simp only [liftUp, Shape.rotateCW, Shape.mapLayers, List.map_cons]
    cases i with
    | zero =>
        simp only [List.getElem?_cons_zero, Layer.rotateCW, Layer.empty]
    | succ n => simp only [List.getElem?_cons_succ, List.getElem?_map]

/-- generatePins は rotateCW と可換 -/
@[aesop norm simp] theorem generatePins_rotateCW (lifted : Shape) (originalBottom : Layer) :
        (generatePins lifted originalBottom).rotateCW =
        generatePins lifted.rotateCW originalBottom.rotateCW := by
    simp only [generatePins, Shape.rotateCW, Shape.mapLayers,
        Layer.rotateCW, List.map_cons]
    congr 1; congr 1
    exact List.map_tail

end PinPusher

namespace Shape

-- ============================================================
-- メインピン押し関数
-- ============================================================

/-- ピン押し機を適用する。
    結果が全空の場合は `none` を返す。 -/
def pinPush (s : Shape) (config : GameConfig) : Option Shape := do
    -- 1. レイヤ持ち上げ
    let lifted := PinPusher.liftUp s
    -- 2. ピン生成
    let withPins := PinPusher.generatePins lifted s.bottom
    -- 3. レイヤ上限チェック
    if withPins.layerCount ≤ config.maxLayers then
        withPins.normalize
    else
        -- 4. レイヤ上限超過時の処理
        -- 4a. 超過レイヤの結晶クラスタを砕け散らせる
        let afterShatter := withPins.shatterOnTruncate config.maxLayers
        -- 4b. レイヤ数を上限に切り詰める
        let truncated := afterShatter.truncate config
        -- 4c. 落下処理
        truncated.gravity

-- ============================================================
-- rotate180 等変性
-- ============================================================

/-- bottom は rotate180 と可換 -/
private theorem bottom_rotate180 (s : Shape) :
        s.rotate180.bottom = s.bottom.rotate180 := by
    simp only [bottom, rotate180, mapLayers]
    rw [List.head_map]

/-- normalize は rotate180 と可換 -/
private theorem normalize_rotate180 (s : Shape) :
        (s.normalize).map Shape.rotate180 = s.rotate180.normalize := by
    exact s.normalize_map_layers Layer.rotate180 Layer.isEmpty_rotate180

/-- pinPush は rotate180 と可換: 回転してからピン押し = ピン押ししてから回転
    config.maxLayers ≤ 5 の場合に成立する（6 レイヤ以上では gravity に反例が存在） -/
@[aesop unsafe 80% apply] theorem pinPush_rotate180_comm (s : Shape) (config : GameConfig)
        (_h_config : config.maxLayers ≤ 5) :
        (s.pinPush config).map Shape.rotate180 =
        s.rotate180.pinPush config := by
    simp only [pinPush]
    conv_rhs =>
        rw [← PinPusher.liftUp_rotate180, bottom_rotate180,
            ← PinPusher.generatePins_rotate180]
    rw [layerCount_rotate180]
    split
    · -- レイヤ上限内: normalize と rotate180 の可換性
      exact normalize_rotate180 _
    · -- レイヤ上限超過: shatterOnTruncate → truncate → gravity の可換性
      rw [gravity_rotate180_comm _, truncate_rotate180,
          shatterOnTruncate_rotate180]

-- ============================================================
-- rotateCW 等変性
-- ============================================================

/-- bottom は rotateCW と可換 -/
private theorem bottom_rotateCW (s : Shape) :
        s.rotateCW.bottom = s.bottom.rotateCW := by
    simp only [bottom, rotateCW, mapLayers]
    rw [List.head_map]

/-- normalize は rotateCW と可換 -/
private theorem normalize_rotateCW (s : Shape) :
        (s.normalize).map Shape.rotateCW = s.rotateCW.normalize := by
    exact s.normalize_map_layers Layer.rotateCW Layer.isEmpty_rotateCW

/-- pinPush は rotateCW と可換: 回転してからピン押し = ピン押ししてから回転
    config.maxLayers ≤ 5 の場合に成立する（6 レイヤ以上では gravity に反例が存在） -/
@[aesop unsafe 80% apply] theorem pinPush_rotateCW_comm (s : Shape) (config : GameConfig)
        (_h_config : config.maxLayers ≤ 5) :
        (s.pinPush config).map Shape.rotateCW =
        s.rotateCW.pinPush config := by
    simp only [pinPush]
    conv_rhs =>
        rw [← PinPusher.liftUp_rotateCW, bottom_rotateCW,
            ← PinPusher.generatePins_rotateCW]
    rw [layerCount_rotateCW]
    split
    · -- レイヤ上限内: normalize と rotateCW の可換性
      exact normalize_rotateCW _
    · -- レイヤ上限超過: shatterOnTruncate → truncate → gravity の可換性
      rw [gravity_rotateCW_comm _, truncate_rotateCW,
          shatterOnTruncate_rotateCW]

-- ============================================================
-- rotateCCW 等変性（rCW³ コロラリー）
-- ============================================================

/-- pinPush は rotateCCW と可換: 回転してからピン押し = ピン押ししてから回転
    rotateCCW = rotateCW³ のコロラリーとして導出 -/
@[aesop unsafe 80% apply] theorem pinPush_rotateCCW_comm (s : Shape) (config : GameConfig)
        (h_config : config.maxLayers ≤ 5) :
        (s.pinPush config).map Shape.rotateCCW =
        s.rotateCCW.pinPush config := by
    conv_lhs =>
        rw [show Shape.rotateCCW = Shape.rotateCW ∘ Shape.rotateCW ∘ Shape.rotateCW from
            funext rotateCCW_eq_rotateCW_rotateCW_rotateCW,
            ← Option.map_map, ← Option.map_map]
    rw [pinPush_rotateCW_comm _ _ h_config,
        pinPush_rotateCW_comm _ _ h_config,
        pinPush_rotateCW_comm _ _ h_config,
        ← rotateCCW_eq_rotateCW_rotateCW_rotateCW]

-- ============================================================
-- IsSettled 保存定理
-- ============================================================

/-- `decide (q.isEmpty = true)` を `q.isEmpty` に正規化する -/
private theorem decide_isEmpty_eq (q : Quarter) : decide (q.isEmpty = true) = q.isEmpty := by
    cases q.isEmpty <;> rfl

open Gravity in
/-- generatePins (liftUp s) s.bottom のレイヤ k+1 は s のレイヤ k に一致する -/
private theorem getQuarter_shift (s : Shape) (k : Nat) (d : Direction) :
        QuarterPos.getQuarter (PinPusher.generatePins (PinPusher.liftUp s) s.bottom) ⟨k + 1, d⟩ =
        QuarterPos.getQuarter s ⟨k, d⟩ := by
    simp only [QuarterPos.getQuarter, PinPusher.generatePins, PinPusher.liftUp,
        List.tail_cons, List.getElem?_cons_succ]

open Gravity in
/-- s の接地辺を r = generatePins (liftUp s) で +1 シフトしても接地辺 -/
private theorem groundingEdge_shift (s : Shape) (a b : QuarterPos)
        (h : groundingEdge s a b = true) :
        groundingEdge (PinPusher.generatePins (PinPusher.liftUp s) s.bottom)
            ⟨a.layer + 1, a.dir⟩ ⟨b.layer + 1, b.dir⟩ = true := by
    simp only [groundingEdge, isUpwardGroundingContact, isGroundingContact,
        isStructurallyBonded, QuarterPos.getQuarter,
        PinPusher.generatePins, PinPusher.liftUp, List.tail_cons, List.getElem?_cons_succ,
        LayerIndex.verticallyAdjacent, beq_eq_decide, Nat.add_right_cancel_iff,
        show ∀ (a b : Nat), decide (a + 1 ≤ b + 1) = decide (a ≤ b) from
            fun a b => by simp only [Nat.add_le_add_iff_right]] at h ⊢; exact h

open Gravity in
/-- s での到達可能性を r = generatePins (liftUp s) での +1 シフト到達可能性に変換 -/
private theorem reachable_shift (s : Shape) (seed p : QuarterPos)
        (h : GenericReachable (groundingEdge s) seed p) :
        GenericReachable (groundingEdge (PinPusher.generatePins (PinPusher.liftUp s) s.bottom))
            ⟨seed.layer + 1, seed.dir⟩ ⟨p.layer + 1, p.dir⟩ := by
    induction h with
    | refl => exact .refl
    | step he _ ih => exact .step (groundingEdge_shift s _ _ he) ih

open Gravity in
/-- ピンとその上の非空象限の間に接地辺が存在する -/
private theorem pin_edge (s : Shape) (d : Direction) (q_s : Quarter)
        (hq_s : QuarterPos.getQuarter s ⟨0, d⟩ = some q_s)
        (hq_s_ne : q_s.isEmpty = false) :
        groundingEdge (PinPusher.generatePins (PinPusher.liftUp s) s.bottom)
            ⟨0, d⟩ ⟨1, d⟩ = true := by
    simp only [QuarterPos.getQuarter] at hq_s
    have h_l0 : s.layers[0]? = some s.bottom := by
        cases hl : s.layers with
        | nil => exact absurd hl s.layers_ne
        | cons a t => simp only [hl, List.getElem?_cons_zero, Shape.bottom, List.head_cons]
    rw [h_l0] at hq_s; simp only [Option.some.injEq] at hq_s
    have h01 : (decide (0 ≤ 1) : Bool) = true := rfl
    cases hd : d <;> simp only [QuarterPos.getDir, hd] at hq_s <;> subst hq_s <;>
        simp_all only [groundingEdge, isUpwardGroundingContact, isGroundingContact,
            QuarterPos.getQuarter, PinPusher.generatePins, PinPusher.liftUp,
            List.getElem?_cons_zero, List.tail_cons, List.getElem?_cons_succ,
            QuarterPos.getDir, Quarter.isEmpty, LayerIndex.verticallyAdjacent,
            Bool.false_eq_true, ite_false, Bool.not_false, Bool.and_self, BEq.rfl, Bool.true_or]

open Gravity in
/-- ピン位置は r の BFS シードに含まれる -/
private theorem pin_seed (s : Shape) (d : Direction) (q_s : Quarter)
        (hq_s : QuarterPos.getQuarter s ⟨0, d⟩ = some q_s)
        (hq_s_ne : q_s.isEmpty = false) :
        let r := PinPusher.generatePins (PinPusher.liftUp s) s.bottom
        ⟨0, d⟩ ∈ (QuarterPos.allValid r).filter (fun q =>
            q.layer == 0 && match q.getQuarter r with
            | some q => !q.isEmpty | none => false) := by
    simp only; rw [List.mem_filter]; constructor
    · simp only [QuarterPos.allValid, List.mem_flatMap, List.mem_map, List.mem_range]
      refine ⟨0, ?_, d, ?_, rfl⟩
      · simp [PinPusher.generatePins, PinPusher.liftUp, Shape.layerCount]
      · cases d <;> simp [Direction.all]
    · simp only [BEq.rfl, Bool.true_and, QuarterPos.getQuarter] at hq_s ⊢
      have h_l0 : s.layers[0]? = some s.bottom := by
          cases hl : s.layers with
          | nil => exact absurd hl s.layers_ne
          | cons a t => simp only [hl, List.getElem?_cons_zero, Shape.bottom, List.head_cons]
      rw [h_l0] at hq_s; simp only [Option.some.injEq] at hq_s
      simp only [PinPusher.generatePins, PinPusher.liftUp, List.getElem?_cons_zero,
          QuarterPos.getDir]
      cases hd : d <;> simp only [QuarterPos.getDir, hd] at hq_s <;> subst hq_s <;>
          simp_all only [Quarter.isEmpty, Bool.false_eq_true, ite_false, Bool.not_false]

open Gravity in
/-- settled 入力に対して liftUp+generatePins は settled 出力を生成する。
    ピン生成により元の接地パスが維持されるため、安定状態が保存される。
    証明戦略: 背理法により floatingUnits が非空と仮定し、浮遊位置 p について:
    - Layer 0 のピンは BFS シードなので直接接地
    - Layer k+1 の位置は s での対応位置が settled から接地済み → BFS パスを +1 シフトしてピンに接続 -/
private theorem IsSettled_liftUp_generatePins (s : Shape) (h_settled : s.IsSettled) :
        (PinPusher.generatePins (PinPusher.liftUp s) s.bottom).IsSettled := by
    let r := PinPusher.generatePins (PinPusher.liftUp s) s.bottom
    show floatingUnits r = []
    by_contra h_ne
    have h_ne_empty : (floatingUnits r).isEmpty = false := by
        rw [Bool.eq_false_iff]; exact fun h_is => h_ne (List.isEmpty_iff.mp h_is)
    obtain ⟨p, h_valid, ⟨q_r, hq_r, hq_r_ne⟩, h_ng⟩ :=
        floatingUnits_nonempty_implies_exists_ungrounded r h_ne_empty
    have hq_r_f : q_r.isEmpty = false := by
        simp only [decide_isEmpty_eq, Bool.not_eq_true'] at hq_r_ne; exact hq_r_ne
    have h_rlc : r.layerCount = s.layerCount + 1 := by
        show (PinPusher.generatePins _ _).layerCount = _
        simp [PinPusher.generatePins, PinPusher.liftUp, Shape.layerCount]
    apply h_ng; rw [show groundedPositions r = (groundedPositionsList r).toFinset from rfl]
    rw [List.mem_toFinset, ← any_beq_iff_mem]
    by_cases hp0 : p.layer = 0
    · -- Layer 0: ピンは BFS シード → .refl で接地
      apply groundedPositionsList_complete r p p _ .refl
      rw [List.mem_filter]; refine ⟨?_, ?_⟩
      · simp only [QuarterPos.allValid, List.mem_flatMap, List.mem_map, List.mem_range]
        exact ⟨0, by omega, p.dir, by cases p.dir <;> simp [Direction.all],
            by cases p; simp_all⟩
      · have hp_eq : p = ⟨0, p.dir⟩ := by cases p; simp_all
        rw [hp_eq] at hq_r ⊢
        simp only [BEq.rfl, Bool.true_and]; rw [hq_r]; simp only [hq_r_f, Bool.not_false]
    · -- Layer k+1: s での対応位置の BFS パスを +1 シフトしてピンに接続
      have hp_pos : 0 < p.layer := Nat.pos_of_ne_zero hp0
      have hq_s : (⟨p.layer - 1, p.dir⟩ : QuarterPos).getQuarter s = some q_r := by
          have h := getQuarter_shift s (p.layer - 1) p.dir
          rw [show p.layer - 1 + 1 = p.layer from by omega] at h
          rw [← h]; exact hq_r
      have h_k_valid : p.layer - 1 < s.layerCount := by omega
      have h_p'_gr : (⟨p.layer - 1, p.dir⟩ : QuarterPos) ∈ groundedPositions s := by
          by_contra h_p'_ng
          have h_ne_s := ungrounded_nonempty_implies_floatingUnits_nonempty s
              ⟨p.layer - 1, p.dir⟩ h_k_valid
              ⟨q_r, hq_s, by simp only [decide_isEmpty_eq]; simp only [hq_r_f, Bool.not_false]⟩
              h_p'_ng
          rw [show floatingUnits s = [] from h_settled] at h_ne_s; simp at h_ne_s
      rw [show groundedPositions s = (groundedPositionsList s).toFinset from rfl,
          List.mem_toFinset, ← any_beq_iff_mem] at h_p'_gr
      obtain ⟨seed, h_seed_mem, h_reach⟩ := groundedPositionsList_sound s _ h_p'_gr
      have h_sf := (List.mem_filter.mp h_seed_mem).2
      have h_seed_l0 : seed.layer = 0 := by
          simp only [Bool.and_eq_true, beq_iff_eq] at h_sf; exact h_sf.1
      have h_seed_eq : seed = ⟨0, seed.dir⟩ := by cases seed; simp_all
      have h_seed_ne : ∃ q, (⟨0, seed.dir⟩ : QuarterPos).getQuarter s = some q ∧
              q.isEmpty = false := by
          rw [h_seed_eq] at h_sf
          simp only [Bool.and_eq_true] at h_sf
          match hgq : (⟨0, seed.dir⟩ : QuarterPos).getQuarter s with
          | none => simp [hgq] at h_sf
          | some q =>
              refine ⟨q, rfl, ?_⟩
              simp [hgq] at h_sf; exact h_sf
      obtain ⟨q_seed, hq_seed, hq_seed_f⟩ := h_seed_ne
      have h_reach_r := reachable_shift s seed ⟨p.layer - 1, p.dir⟩ h_reach
      simp only [h_seed_l0, show (p.layer - 1) + 1 = p.layer from by omega] at h_reach_r
      apply groundedPositionsList_complete r ⟨0, seed.dir⟩ p
      · exact pin_seed s seed.dir q_seed hq_seed hq_seed_f
      · have h_p_eq : p = ⟨p.layer, p.dir⟩ := by cases p; rfl
        rw [h_p_eq]
        exact .step (pin_edge s seed.dir q_seed hq_seed hq_seed_f) h_reach_r

/-- settled なシェイプに gravity を適用すると normalize と同じ結果になる -/
private theorem gravity_eq_normalize_of_settled (s : Shape) (h : s.IsSettled) :
        s.gravity = s.normalize := by
    show Gravity.process s = s.normalize
    exact Gravity.process_of_isEmpty_floatingUnits s (List.isEmpty_iff.mpr h)

/-- pinPush の出力は安定状態。config.maxLayers ≤ 5 かつ入力が settled の場合に成立する。
    レイヤ上限内パスは normalize を使用し、settled 入力では gravity と等価。
    レイヤ上限超過パスは gravity を直接経由するため、gravity_IsSettled に帰着する -/
theorem IsSettled_pinPush (s : Shape) (config : GameConfig) (s' : Shape)
        (h : s.pinPush config = some s') (h_config : config.maxLayers ≤ 5)
        (h_settled : s.IsSettled) :
        s'.IsSettled := by
    simp only [pinPush] at h
    split at h
    · -- レイヤ上限内: withPins.normalize
      next h_lc =>
        have h_wp_settled := IsSettled_liftUp_generatePins s h_settled
        rw [← gravity_eq_normalize_of_settled _ h_wp_settled] at h
        exact gravity_IsSettled _ s' h (Nat.le_trans h_lc h_config)
    · -- レイヤ上限超過: truncated.gravity
      exact gravity_IsSettled _ s' h
        (Nat.le_trans (truncate_layerCount_le _ config) h_config)

end Shape
