-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations

/-!
# Test.Operations.Trash

ゴミ箱 (Trash) のテスト。
-/

open S2IL

namespace Test.Operations.Trash

private def sampleLayer : Layer :=
  Layer.mk (.colored .circle .red) (.colored .star .green)
           (.colored .windmill .blue) (.crystal .yellow)

private def sampleShape : Shape := [sampleLayer]

#guard Shape.trash sampleShape == ()
#guard Shape.trash Shape.empty == ()

example (s : Shape) : Shape.trash s = () :=
  Shape.trash_eq_unit s

example (s t : Shape) : Shape.trash s = Shape.trash t :=
  Shape.trash_eq_trash s t

example (s : Shape) : Shape.trash s.rotateCW = Shape.trash s :=
  Shape.trash.rotateCW_comm s

example (s : Shape) : Shape.trash s.rotate180 = Shape.trash s :=
  Shape.trash.rotate180_comm s

example (s : Shape) : Shape.trash s.rotateCCW = Shape.trash s :=
  Shape.trash.rotateCCW_comm s

end Test.Operations.Trash
