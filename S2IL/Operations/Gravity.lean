-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel
import S2IL.Operations.Settled

/-!
# S2IL.Operations.Gravity

落下機構 (B-1)（Phase C re-scaffold 済み）。
全関数版: `gravity : Shape → Shape`（architecture §1.9 Option 追放原則）。

## 公開 API

- `gravity : Shape → Shape` — メイン落下処理（全関数）
- `gravity_isSettled` — 出力は常に `IsSettled`
- `gravity_of_isSettled` — 安定入力に対する不動点性
- `gravity_rotateCW_comm` — CW 等変性

## 単一チェーン原則

CW 等変性のみ axiom、180° / CCW は 1 行系。
-/

namespace S2IL

/-- メイン落下処理（全関数）。0 層シェイプには恒等。 -/
axiom Shape.gravity : Shape → Shape

/-- `gravity` の出力は常に `IsSettled`。 -/
axiom Shape.gravity.isSettled (s : Shape) : IsSettled (Shape.gravity s)

/-- 安定入力に対する不動点性（Phase D で theorem へ降格予定）。 -/
axiom Shape.gravity.of_isSettled {s : Shape} :
    IsSettled s → Shape.gravity s = s

/-- `gravity` と CW 回転は可換。 -/
axiom Shape.gravity.rotateCW_comm (s : Shape) :
    Shape.rotateCW (Shape.gravity s) = Shape.gravity (Shape.rotateCW s)

/-- `gravity` と 180° 回転は可換（CW の系）。 -/
theorem Shape.gravity.rotate180_comm (s : Shape) :
    (Shape.gravity s).rotate180 = Shape.gravity s.rotate180 := by
  simp [Shape.rotate180_eq_rotateCW_rotateCW, Shape.gravity.rotateCW_comm]

/-- `gravity` と CCW 回転は可換（CW の系）。 -/
theorem Shape.gravity.rotateCCW_comm (s : Shape) :
    (Shape.gravity s).rotateCCW = Shape.gravity s.rotateCCW := by
  simp [Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW, Shape.gravity.rotateCW_comm]

end S2IL
