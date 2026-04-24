-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel

/-!
# S2IL.Operations.PinPusher

ピン押し機 (A-2-5 + B-4-4)（Phase C re-scaffold 済み）。
全関数化（architecture §1.9）。

## セマンティクス（ゲーム仕様）

入力は常に settled（ベルト規定）。処理順は:

1. `liftUp s` — 全象限を 1 レイヤ上へ移動し、L0 を空にする
2. `generatePins (liftUp s) pinLayer` — 最下層にピンを挿入
3. `truncate` → `shatterTopCrystals` → `gravity` で安定化して出力

## 公開 API

- `liftUp : Shape → Shape`
- `generatePins : Shape → Layer → Shape`
- `pinPush : Shape → GameConfig → Shape`（全関数）
- CW 等変性
-/

namespace S2IL

axiom Shape.liftUp : Shape → Shape
axiom Shape.generatePins : Shape → Layer → Shape

/-- ピン押し（全関数）。 -/
axiom Shape.pinPush : Shape → GameConfig → Shape

axiom Shape.liftUp.layerCount (s : Shape) :
    (Shape.liftUp s).layerCount = s.layerCount + 1

axiom Shape.liftUp.rotateCW_comm (s : Shape) :
    Shape.rotateCW (Shape.liftUp s) = Shape.liftUp (Shape.rotateCW s)

/-- `liftUp` と 180° 回転は可換（CW の系）。 -/
theorem Shape.liftUp.rotate180_comm (s : Shape) :
    (Shape.liftUp s).rotate180 = (Shape.liftUp s.rotate180) := by
  simp [Shape.rotate180_eq_rotateCW_rotateCW, Shape.liftUp.rotateCW_comm]

-- NOTE: `generatePins` の CW 等変性は signature 依存のため Phase C で整備する。

/-- `pinPush` と CW 回転は可換（全関数版、直接等式）。 -/
axiom Shape.pinPush.rotateCW_comm (s : Shape) (config : GameConfig) :
    Shape.rotateCW (Shape.pinPush s config) =
      Shape.pinPush (Shape.rotateCW s) config

end S2IL
