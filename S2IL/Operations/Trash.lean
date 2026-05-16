-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel

/-!
# S2IL.Operations.Trash

ゴミ箱 (Trash)。入力 Shape を消費し、出力を持たない加工装置。

Lean 上では「出力なし」を `Unit` で表す。したがって `Shape.trash` は常に `()` を返す
全関数であり、回転や入力 Shape の違いに依存しない。
-/

namespace S2IL

/-- ゴミ箱。入力 Shape を削除し、出力を持たない。 -/
def Shape.trash (_ : Shape) : Unit := ()

/-- `trash` の出力は常に unit。 -/
@[simp] theorem Shape.trash_eq_unit (s : Shape) : Shape.trash s = () := rfl

/-- `trash` は入力 Shape に依存しない。 -/
theorem Shape.trash_eq_trash (s t : Shape) : Shape.trash s = Shape.trash t := rfl

/-- `trash` は CW 回転に依存しない。 -/
theorem Shape.trash.rotateCW_comm (s : Shape) :
    Shape.trash (Shape.rotateCW s) = Shape.trash s := rfl

/-- `trash` は 180° 回転に依存しない。 -/
theorem Shape.trash.rotate180_comm (s : Shape) :
    Shape.trash (Shape.rotate180 s) = Shape.trash s := rfl

/-- `trash` は CCW 回転に依存しない。 -/
theorem Shape.trash.rotateCCW_comm (s : Shape) :
    Shape.trash (Shape.rotateCCW s) = Shape.trash s := rfl

end S2IL
