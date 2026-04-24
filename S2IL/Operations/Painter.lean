-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel

/-!
# S2IL.Operations.Painter

着色機 (A-2-3)。最上位レイヤの通常パーツのみを指定色で塗る。

## 公開 API

- `paint : Shape → Color → Shape`
- 冪等性・CW 等変性

## 単一チェーン原則

CW 等変性のみ axiom、180° / CCW は 1 行系。
-/

namespace S2IL

axiom Shape.paint : Shape → Color → Shape

/-- `paint` は冪等。 -/
axiom Shape.paint.idempotent (s : Shape) (c : Color) :
    (Shape.paint s c).paint c = Shape.paint s c

/-- `paint` と CW 回転は可換。 -/
axiom Shape.paint.rotateCW_comm (s : Shape) (c : Color) :
    (Shape.paint s c).rotateCW = Shape.paint s.rotateCW c

/-- `paint` と 180° 回転は可換（CW の系）。 -/
theorem Shape.paint.rotate180_comm (s : Shape) (c : Color) :
    (Shape.paint s c).rotate180 = Shape.paint s.rotate180 c := by
  simp [Shape.rotate180_eq_rotateCW_rotateCW, Shape.paint.rotateCW_comm]

/-- `paint` と CCW 回転は可換（CW の系）。 -/
theorem Shape.paint.rotateCCW_comm (s : Shape) (c : Color) :
    (Shape.paint s c).rotateCCW = Shape.paint s.rotateCCW c := by
  simp [Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW, Shape.paint.rotateCW_comm]

end S2IL
