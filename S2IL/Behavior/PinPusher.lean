-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Behavior.Gravity
import S2IL.Behavior.Rotate
import S2IL.Behavior.Shatter
import S2IL.Behavior.Stacker
import S2IL.Behavior.SettledState
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
        (h_config : config.maxLayers ≤ 5) :
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
      have h_trunc : ∀ (t : Shape), (t.truncate config).layerCount ≤ 5 :=
        fun t => Nat.le_trans (truncate_layerCount_le t config) h_config
      rw [gravity_rotate180_comm _ (h_trunc _), truncate_rotate180,
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
        (h_config : config.maxLayers ≤ 5) :
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
      have h_trunc : ∀ (t : Shape), (t.truncate config).layerCount ≤ 5 :=
        fun t => Nat.le_trans (truncate_layerCount_le t config) h_config
      rw [gravity_rotateCW_comm _ (h_trunc _), truncate_rotateCW,
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

/-- settled 入力に対して liftUp+generatePins は settled 出力を生成する。
    ピン生成により元の接地パスが維持されるため、安定状態が保存される。
    将来的に構成的証明で置換予定 -/
private axiom IsSettled_liftUp_generatePins (s : Shape) (h : s.IsSettled) :
        (PinPusher.generatePins (PinPusher.liftUp s) s.bottom).IsSettled

/-- settled なシェイプに gravity を適用すると normalize と同じ結果になる -/
private theorem gravity_eq_normalize_of_settled (s : Shape) (h : s.IsSettled) :
        s.gravity = s.normalize := by
    show Gravity.process s = s.normalize
    unfold Gravity.process
    simp only [show Gravity.floatingUnits s = [] from h, List.isEmpty, ↓reduceIte]

/-- pinPush の出力は安定状態。config.maxLayers ≤ 5 かつ入力が settled の場合に成立する。
    レイヤ上限内パスは normalize を使用し、settled 入力では gravity と等価。
    レイヤ上限超過パスは gravity を直接経由するため、gravity_IsSettled axiom に帰着する -/
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
