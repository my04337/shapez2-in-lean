-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Flow

/-!
# Test.Flow.Defs

Layer C-1 Flow core の smoke tests。
-/

open S2IL

namespace Test.Flow.Defs

private def sampleLayer : Layer :=
  Layer.mk (.colored .circle .red) (.colored .star .green)
           (.colored .windmill .blue) (.crystal .yellow)

private def sampleShape : Shape := [sampleLayer]

#guard Flow.eval (Flow.id : Flow Nat Nat) 7 == 7

#guard Flow.eval
    (Flow.comp (Flow.prim (fun number : Nat => number + 1))
      (Flow.prim (fun number : Nat => number * 2)))
    3 == 8

#guard Flow.eval (Flow.swap : Flow (Nat × Bool) (Bool × Nat)) (3, true) == (true, 3)

#guard Flow.eval (Flow.dup : Flow Nat (Nat × Nat)) 5 == (5, 5)

#guard Flow.eval
    (Flow.pairMap (Flow.prim (fun number : Nat => number + 1))
      (Flow.prim (fun flag : Bool => !flag)))
    (3, false) == (4, true)

#guard Flow.eval (Flow.constant .blue : Flow Shape Color) sampleShape == Color.blue

#guard Flow.eval (Flow.assocRight : Flow ((Nat × Bool) × Color) (Nat × (Bool × Color)))
  ((3, true), .red) == (3, (true, .red))

#guard Flow.eval (Flow.assocLeft : Flow (Nat × (Bool × Color)) ((Nat × Bool) × Color))
  (3, (true, .red)) == ((3, true), .red)

#guard Shape.toString (Flow.eval Flow.halfDestroy sampleShape) ==
  Shape.toString (Shape.halfDestroy sampleShape)

#guard (Flow.eval Flow.cut sampleShape).1.length == 1
#guard (Flow.eval Flow.cut sampleShape).2.length == 1

#guard Shape.toString
    (Flow.eval Flow.combineHalves (Shape.eastHalf sampleShape, Shape.westHalf sampleShape)) ==
  Shape.toString sampleShape

#guard Flow.eval Flow.mix (.red, .green) == S2IL.Operations.mix .red .green

#guard Shape.toString (Flow.eval Flow.paintWith (sampleShape, .blue)) ==
  Shape.toString (Shape.paint sampleShape .blue)

#guard Shape.toString (Flow.eval Flow.crystallizeWith (sampleShape, .cyan)) ==
  Shape.toString (Shape.crystallize sampleShape .cyan)

#guard Shape.toString (Flow.eval Flow.swapShapes (sampleShape, sampleShape)).1 ==
  Shape.toString (Shape.swap sampleShape sampleShape).1

#guard Shape.toString (Flow.eval Flow.Examples.cutThenCombine sampleShape) ==
  Shape.toString sampleShape

example (color : Color) :
    Flow.eval (Flow.paint color) sampleShape = Shape.paint sampleShape color := rfl

example : Flow.Equivalent Flow.Examples.cutThenCombine (Flow.id : Flow Shape Shape) :=
  Flow.Examples.cutThenCombine_equivalent_id

example : Flow.Equivalent (Flow.comp Flow.id Flow.halfDestroy) Flow.halfDestroy :=
  Flow.Equivalent.id_left Flow.halfDestroy

example : Flow.Equivalent (Flow.comp Flow.halfDestroy Flow.id) Flow.halfDestroy :=
  Flow.Equivalent.id_right Flow.halfDestroy

example :
    Flow.Equivalent
      (Flow.comp (Flow.assocRight : Flow ((Nat × Bool) × Color) (Nat × (Bool × Color)))
        Flow.assocLeft)
      (Flow.id : Flow ((Nat × Bool) × Color) ((Nat × Bool) × Color)) :=
  Flow.Equivalent.assocRight_assocLeft

example : Flow.CWEquivariant (Flow.id : Flow Shape Shape) :=
  Flow.CWEquivariant.id

end Test.Flow.Defs
