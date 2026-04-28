-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel
import S2IL.Operations.Common
import S2IL.Operations.Gravity
import S2IL.Operations.Stacker

/-!
# S2IL.Operations.PinPusher

ピン押し機 (A-2-5 + B-4-4)。Phase D-8 で部分的に axiom-free 化。

## セマンティクス（ゲーム仕様）

入力は常に settled（ベルト規定）。処理順は
[docs/shapez2/game-system-overview.md ピン押し節](../../docs/shapez2/game-system-overview.md)
に従い:

1. `liftUp s` — 全象限を 1 レイヤ上へ移動し、L0 を空にする
2. `generatePins (liftUp s) pinLayer` — 最下層を `pinLayer` で置換
   （ピンレイヤは元シェイプの最下層から `pinLayerOf` で導出）
3. `truncate ... config` — レイヤ上限超過分を捨てる
4. `shatterTopCrystals ... config.maxLayers` — 切り詰め境界に
   触れる結晶クラスタを砕け散らせる
5. `gravity` — 落下処理で安定化

## 公開 API

- `Shape.liftUp : Shape → Shape`
- `Shape.generatePins : Shape → Layer → Shape`
- `Shape.pinLayerOf : Shape → Layer`
- `Shape.pinPush : Shape → GameConfig → Shape`（合成 def、全関数）
- 構造的恒等式 (`liftUp.layerCount`)
- CW 等変性 (`liftUp.rotateCW_comm` 他) と 180° / CCW 1 行系

## 単一チェーン原則

CW 等変性のみを直接証明、180° / CCW は 1 行系。`generatePins` は
2 引数の equivariance（Shape × Layer の同時 CW 持ち上げ）を直接証明する。

## 残存 axiom

- `Shape.shatterTopCrystals`（`Operations.Stacker` から再エクスポート、Phase D-9）
- `Shape.gravity`（`Operations.Gravity`、Phase D-10）
-/

namespace S2IL

-- ============================================================
-- liftUp: 全レイヤを 1 段上に持ち上げ
-- ============================================================

/-- レイヤを 1 段持ち上げる（最下層に空レイヤを挿入する）。 -/
def Shape.liftUp (s : Shape) : Shape := Layer.empty :: s

@[simp] theorem Shape.liftUp_def (s : Shape) :
    Shape.liftUp s = Layer.empty :: s := rfl

/-- `liftUp` 後のレイヤ数は元 + 1。 -/
@[simp] theorem Shape.liftUp.layerCount (s : Shape) :
    (Shape.liftUp s).layerCount = s.layerCount + 1 := by
  simp [Shape.liftUp, Shape.layerCount]

private theorem Shape.empty_rotateCW : Layer.rotateCW Layer.empty = Layer.empty := by
  funext d; simp [Layer.empty, Layer.rotateCW]

/-- `liftUp` と CW 回転は可換。 -/
theorem Shape.liftUp.rotateCW_comm (s : Shape) :
    Shape.rotateCW (Shape.liftUp s) = Shape.liftUp (Shape.rotateCW s) := by
  show (Layer.empty :: s).map Layer.rotateCW = Layer.empty :: s.map Layer.rotateCW
  rw [List.map_cons, Shape.empty_rotateCW]

/-- `liftUp` と 180° 回転は可換（CW の系）。 -/
theorem Shape.liftUp.rotate180_comm (s : Shape) :
    (Shape.liftUp s).rotate180 = Shape.liftUp s.rotate180 := by
  show (Shape.liftUp s).rotateCW.rotateCW = Shape.liftUp s.rotateCW.rotateCW
  rw [Shape.liftUp.rotateCW_comm, Shape.liftUp.rotateCW_comm]

/-- `liftUp` と CCW 回転は可換（CW の系）。 -/
theorem Shape.liftUp.rotateCCW_comm (s : Shape) :
    (Shape.liftUp s).rotateCCW = Shape.liftUp s.rotateCCW := by
  show (Shape.liftUp s).rotateCW.rotateCW.rotateCW
        = Shape.liftUp s.rotateCW.rotateCW.rotateCW
  rw [Shape.liftUp.rotateCW_comm, Shape.liftUp.rotateCW_comm,
      Shape.liftUp.rotateCW_comm]

-- ============================================================
-- generatePins: 最下層を任意の pinLayer で置換
-- ============================================================

/-- `lifted` の最下層を `pinLayer` で置換する（`lifted` の旧最下層を捨てる）。
    `lifted` が空の場合は `[pinLayer]` を返す。 -/
def Shape.generatePins (lifted : Shape) (pinLayer : Layer) : Shape :=
  pinLayer :: lifted.tail

/-- `generatePins` と CW 回転は同時可換（Shape と Layer 両方を CW 化）。 -/
theorem Shape.generatePins.rotateCW_comm (lifted : Shape) (pinLayer : Layer) :
    Shape.rotateCW (Shape.generatePins lifted pinLayer) =
      Shape.generatePins (Shape.rotateCW lifted) pinLayer.rotateCW := by
  show (pinLayer :: lifted.tail).map Layer.rotateCW
        = pinLayer.rotateCW :: (lifted.map Layer.rotateCW).tail
  rw [List.map_cons, List.map_tail]

/-- `generatePins` と 180° 回転は同時可換（CW の系）。 -/
theorem Shape.generatePins.rotate180_comm (lifted : Shape) (pinLayer : Layer) :
    (Shape.generatePins lifted pinLayer).rotate180 =
      Shape.generatePins lifted.rotate180 pinLayer.rotate180 := by
  show ((Shape.generatePins lifted pinLayer).rotateCW).rotateCW
        = Shape.generatePins (lifted.rotateCW.rotateCW) pinLayer.rotateCW.rotateCW
  rw [Shape.generatePins.rotateCW_comm, Shape.generatePins.rotateCW_comm]

/-- `generatePins` と CCW 回転は同時可換（CW の系）。 -/
theorem Shape.generatePins.rotateCCW_comm (lifted : Shape) (pinLayer : Layer) :
    (Shape.generatePins lifted pinLayer).rotateCCW =
      Shape.generatePins lifted.rotateCCW pinLayer.rotateCCW := by
  show ((Shape.generatePins lifted pinLayer).rotateCW).rotateCW.rotateCW
        = Shape.generatePins
            (lifted.rotateCW.rotateCW.rotateCW)
            pinLayer.rotateCW.rotateCW.rotateCW
  rw [Shape.generatePins.rotateCW_comm, Shape.generatePins.rotateCW_comm,
      Shape.generatePins.rotateCW_comm]

-- ============================================================
-- pinLayerOf: 元シェイプの最下層から導出されるピンレイヤ
-- ============================================================

/-- 元シェイプの最下層の非空象限の下にピンを配置するためのレイヤ。
    各方角 d について: 元の `s.bottomLayer d` が空なら `Quarter.empty`、
    そうでなければ `Quarter.pin`。 -/
def Shape.pinLayerOf (s : Shape) : Layer :=
  fun d => if (s.bottomLayer d).isEmpty then Quarter.empty else Quarter.pin

/-- `pinLayerOf` は CW 回転と可換。 -/
theorem Shape.pinLayerOf.rotateCW_comm (s : Shape) :
    s.rotateCW.pinLayerOf = (s.pinLayerOf).rotateCW := by
  funext d
  show (if (s.rotateCW.bottomLayer d).isEmpty then _ else _)
        = (s.pinLayerOf) (d - 1)
  rw [Shape.bottomLayer.rotateCW_comm]
  show (if (s.bottomLayer.rotateCW d).isEmpty then _ else _)
        = if (s.bottomLayer (d - 1)).isEmpty then _ else _
  rfl

-- ============================================================
-- pinPush: パイプライン全体（全関数 def）
-- ============================================================

/-- ピン押し機（全関数）。
    `gravity ∘ shatterTopCrystals(maxLayers) ∘ truncate
       ∘ generatePins(_, pinLayerOf s) ∘ liftUp`。
    `gravity` / `shatterTopCrystals` がまだ axiom のため `noncomputable`。 -/
noncomputable def Shape.pinPush (s : Shape) (config : GameConfig) : Shape :=
  Shape.gravity
    (Shape.shatterTopCrystals
      (Shape.truncate
        (Shape.generatePins s.liftUp s.pinLayerOf)
        config)
      config.maxLayers)

/-- `pinPush` と CW 回転は可換（合成チェーン）。 -/
theorem Shape.pinPush.rotateCW_comm (s : Shape) (config : GameConfig) :
    Shape.rotateCW (Shape.pinPush s config) =
      Shape.pinPush (Shape.rotateCW s) config := by
  unfold Shape.pinPush
  rw [Shape.gravity.rotateCW_comm,
      Shape.shatterTopCrystals.rotateCW_comm,
      Shape.truncate.rotateCW_comm,
      Shape.generatePins.rotateCW_comm,
      Shape.liftUp.rotateCW_comm,
      ← Shape.pinLayerOf.rotateCW_comm]

/-- `pinPush` と 180° 回転は可換（CW の系）。 -/
theorem Shape.pinPush.rotate180_comm (s : Shape) (config : GameConfig) :
    (Shape.pinPush s config).rotate180 =
      Shape.pinPush s.rotate180 config := by
  simp [Shape.rotate180_eq_rotateCW_rotateCW, Shape.pinPush.rotateCW_comm]

/-- `pinPush` と CCW 回転は可換（CW の系）。 -/
theorem Shape.pinPush.rotateCCW_comm (s : Shape) (config : GameConfig) :
    (Shape.pinPush s config).rotateCCW =
      Shape.pinPush s.rotateCCW config := by
  simp [Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW, Shape.pinPush.rotateCW_comm]

end S2IL
