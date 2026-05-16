-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Flow

/-!
# Test.Flow.Examples

Layer C-1 representative Flow examples の smoke tests。
-/

open S2IL

namespace Test.Flow.Examples

private def sampleLayer : Layer :=
  Layer.mk (.colored .circle .red) (.colored .star .green)
           (.colored .windmill .blue) (.crystal .yellow)

private def sampleShape : Shape := [sampleLayer]

#guard Shape.toString sampleShape == "CrSgWbcy"

#guard Shape.toString (Flow.eval Flow.Examples.extractNE sampleShape) == "Cr------"
#guard Shape.toString (Flow.eval Flow.Examples.extractSE sampleShape) == "--Sg----"
#guard Shape.toString (Flow.eval Flow.Examples.extractSW sampleShape) == "----Wb--"
#guard Shape.toString (Flow.eval Flow.Examples.extractNW sampleShape) == "------cy"

example :
    Flow.eval Flow.Examples.extractNE sampleShape =
      Flow.Examples.shapeOnlyDirection Direction.ne sampleShape :=
  Flow.Examples.extractNE_eval sampleShape

example :
    Flow.eval Flow.Examples.extractSW sampleShape =
      Flow.Examples.shapeOnlyDirection Direction.sw sampleShape :=
  Flow.Examples.extractSW_eval sampleShape

#guard Shape.toString (Flow.eval (Flow.Examples.paintBoth .blue) (sampleShape, sampleShape)).1 ==
  Shape.toString (Shape.paint sampleShape .blue)

#guard Shape.toString (Flow.eval Flow.Examples.rotateBothCW (sampleShape, sampleShape)).2 ==
  Shape.toString (Shape.rotateCW sampleShape)

#guard Shape.toString (Flow.eval Flow.Examples.mixThenPaint (sampleShape, (.red, .green))) ==
  Shape.toString (Shape.paint sampleShape (S2IL.Operations.mix .red .green))

#guard Shape.toString (Flow.eval Flow.Examples.mixThenCrystallize (sampleShape, (.red, .blue))) ==
  Shape.toString (Shape.crystallize sampleShape (S2IL.Operations.mix .red .blue))

#guard Shape.toString (Flow.eval (Flow.Examples.cutPaintBothCombine .blue) sampleShape) ==
  Shape.toString (Shape.paint sampleShape .blue)

#guard Shape.toString (Flow.eval Flow.Examples.cutKeepEast sampleShape) ==
  Shape.toString (Shape.eastHalf sampleShape)

#guard Shape.toString (Flow.eval Flow.Examples.cutKeepWest sampleShape) ==
  Shape.toString (Shape.westHalf sampleShape)

example :
    Flow.eval (Flow.Examples.rotateThenPaint .red) sampleShape =
      Shape.paint (Shape.rotateCW sampleShape) .red := rfl

example :
    Flow.eval Flow.Examples.cutThenCombine sampleShape = sampleShape := by
  exact Flow.Examples.cutThenCombine_equivalent_id sampleShape

example :
    Flow.eval Flow.Examples.cutKeepEast sampleShape = Shape.eastHalf sampleShape :=
  Flow.Examples.cutKeepEast_eval sampleShape

example :
    Flow.eval Flow.Examples.cutKeepWest sampleShape = Shape.westHalf sampleShape :=
  Flow.Examples.cutKeepWest_eval sampleShape

noncomputable section

example :
    Flow.eval (Flow.Examples.stackThenPaint GameConfig.vanilla4 .green) (sampleShape, sampleShape) =
      Shape.paint (Shape.stack sampleShape sampleShape GameConfig.vanilla4) .green := rfl

example :
    Flow.eval (Flow.Examples.crystallizeThenGravity .cyan) sampleShape =
      Shape.gravity (Shape.crystallize sampleShape .cyan) := rfl

example : IsSettled (Flow.eval (Flow.Examples.crystallizeThenGravity .cyan) sampleShape) :=
  Flow.Examples.crystallizeThenGravity_isSettled .cyan sampleShape

example :
    Flow.eval (Flow.Examples.pinPushThenPaint GameConfig.vanilla4 .red) sampleShape =
      Shape.paint (Shape.pinPush sampleShape GameConfig.vanilla4) .red := rfl

example :
    Flow.eval (Flow.Examples.swapThenStack GameConfig.vanilla4) (sampleShape, sampleShape) =
      Shape.stack (Shape.swap sampleShape sampleShape).1
        (Shape.swap sampleShape sampleShape).2 GameConfig.vanilla4 :=
  Flow.Examples.swapThenStack_eval GameConfig.vanilla4 (sampleShape, sampleShape)

example :
    Flow.eval Flow.Examples.swapKeepFirst (sampleShape, Shape.empty) =
      (Shape.swap sampleShape Shape.empty).1 :=
  Flow.Examples.swapKeepFirst_eval (sampleShape, Shape.empty)

example :
    Flow.eval Flow.Examples.swapKeepSecond (sampleShape, Shape.empty) =
      (Shape.swap sampleShape Shape.empty).2 :=
  Flow.Examples.swapKeepSecond_eval (sampleShape, Shape.empty)

end

end Test.Flow.Examples
