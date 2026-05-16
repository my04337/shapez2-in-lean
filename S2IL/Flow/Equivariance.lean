-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Flow.Equivalence

/-!
# S2IL.Flow.Equivariance

Flow に対する回転等変性 predicate。

初期実装では、成立する flow にだけ性質を付与する。E/W 参照操作は CW 等変性を
持たないため、一律の `rotateCW` theorem は置かない。
-/

namespace S2IL
namespace Flow

/-- Shape 入出力 flow が CW 回転と可換であること。 -/
def CWEquivariant (flow : Flow Shape Shape) : Prop :=
  ∀ shape, Shape.rotateCW (Flow.eval flow shape) = Flow.eval flow (Shape.rotateCW shape)

/-- Shape 入出力 flow が 180° 回転と可換であること。 -/
def HalfTurnEquivariant (flow : Flow Shape Shape) : Prop :=
  ∀ shape, Shape.rotate180 (Flow.eval flow shape) = Flow.eval flow (Shape.rotate180 shape)

/-- Shape ペア出力 flow が 180° 回転で成分 swap されること。 -/
def HalfTurnSwapEquivariant (flow : Flow Shape (Shape × Shape)) : Prop :=
  ∀ shape,
    let output := Flow.eval flow shape
    Flow.eval flow (Shape.rotate180 shape) =
      (Shape.rotate180 output.2, Shape.rotate180 output.1)

/-- Shape ペア入出力 flow が 180° 回転で出力成分 swap を伴って可換であること。 -/
def HalfTurnPairSwapEquivariant (flow : Flow (Shape × Shape) (Shape × Shape)) : Prop :=
  ∀ input,
    let output := Flow.eval flow input
    Flow.eval flow (Shape.rotate180 input.1, Shape.rotate180 input.2) =
      (Shape.rotate180 output.2, Shape.rotate180 output.1)

/-- Shape ペア入力 flow が CW 回転と可換であること。 -/
def CWPairInputEquivariant (flow : Flow (Shape × Shape) Shape) : Prop :=
  ∀ input,
    Shape.rotateCW (Flow.eval flow input) =
      Flow.eval flow (Shape.rotateCW input.1, Shape.rotateCW input.2)

/-- Shape ペア入力 flow が 180° 回転と可換であること。 -/
def HalfTurnPairInputEquivariant (flow : Flow (Shape × Shape) Shape) : Prop :=
  ∀ input,
    Shape.rotate180 (Flow.eval flow input) =
      Flow.eval flow (Shape.rotate180 input.1, Shape.rotate180 input.2)

/-- Unit 出力 flow が CW 回転入力に依存しないこと。 -/
def CWUnitInvariant (flow : Flow Shape Unit) : Prop :=
  ∀ shape, Flow.eval flow (Shape.rotateCW shape) = Flow.eval flow shape

/-- Unit 出力 flow が 180° 回転入力に依存しないこと。 -/
def HalfTurnUnitInvariant (flow : Flow Shape Unit) : Prop :=
  ∀ shape, Flow.eval flow (Shape.rotate180 shape) = Flow.eval flow shape

/-- Unit 出力 flow が CCW 回転入力に依存しないこと。 -/
def CCWUnitInvariant (flow : Flow Shape Unit) : Prop :=
  ∀ shape, Flow.eval flow (Shape.rotateCCW shape) = Flow.eval flow shape

/-- `id` flow は CW 等変。 -/
theorem CWEquivariant.id : CWEquivariant (Flow.id : Flow Shape Shape) := by
  intro shape
  rfl

/-- CW 等変な flow の合成は CW 等変。 -/
theorem CWEquivariant.comp {firstFlow secondFlow : Flow Shape Shape}
    (firstEquivariant : CWEquivariant firstFlow)
    (secondEquivariant : CWEquivariant secondFlow) :
    CWEquivariant (Flow.comp firstFlow secondFlow) := by
  intro shape
  change Shape.rotateCW (Flow.eval secondFlow (Flow.eval firstFlow shape)) =
    Flow.eval secondFlow (Flow.eval firstFlow (Shape.rotateCW shape))
  rw [secondEquivariant (Flow.eval firstFlow shape), firstEquivariant shape]

/-- CW 回転 flow は CW 等変。 -/
theorem CWEquivariant.rotateCW : CWEquivariant Flow.rotateCW := by
  intro shape
  rfl

/-- Painter flow は CW 等変。 -/
theorem CWEquivariant.paint (color : Color) : CWEquivariant (Flow.paint color) := by
  intro shape
  exact Shape.paint.rotateCW_comm shape color

/-- Crystal Generator flow は CW 等変。 -/
theorem CWEquivariant.crystallize (color : Color) : CWEquivariant (Flow.crystallize color) := by
  intro shape
  exact Shape.crystallize.rotateCW_comm shape color

/-- Gravity flow は CW 等変。 -/
theorem CWEquivariant.gravity : CWEquivariant Flow.gravity := by
  intro shape
  exact Shape.gravity.rotateCW_comm shape

/-- Pin Pusher flow は CW 等変。 -/
theorem CWEquivariant.pinPush (config : GameConfig) : CWEquivariant (Flow.pinPush config) := by
  intro shape
  exact Shape.pinPush.rotateCW_comm shape config

/-- Trash flow は CW 回転入力に依存しない。 -/
theorem CWUnitInvariant.trash : CWUnitInvariant Flow.trash := by
  intro shape
  exact Shape.trash.rotateCW_comm shape

/-- `id` flow は 180° 等変。 -/
theorem HalfTurnEquivariant.id : HalfTurnEquivariant (Flow.id : Flow Shape Shape) := by
  intro shape
  rfl

/-- 180° 等変な flow の合成は 180° 等変。 -/
theorem HalfTurnEquivariant.comp {firstFlow secondFlow : Flow Shape Shape}
    (firstEquivariant : HalfTurnEquivariant firstFlow)
    (secondEquivariant : HalfTurnEquivariant secondFlow) :
    HalfTurnEquivariant (Flow.comp firstFlow secondFlow) := by
  intro shape
  change Shape.rotate180 (Flow.eval secondFlow (Flow.eval firstFlow shape)) =
    Flow.eval secondFlow (Flow.eval firstFlow (Shape.rotate180 shape))
  rw [secondEquivariant (Flow.eval firstFlow shape), firstEquivariant shape]

/-- Painter flow は 180° 等変。 -/
theorem HalfTurnEquivariant.paint (color : Color) : HalfTurnEquivariant (Flow.paint color) := by
  intro shape
  exact Shape.paint.rotate180_comm shape color

/-- Crystal Generator flow は 180° 等変。 -/
theorem HalfTurnEquivariant.crystallize (color : Color) :
    HalfTurnEquivariant (Flow.crystallize color) := by
  intro shape
  exact Shape.crystallize.rotate180_comm shape color

/-- Gravity flow は 180° 等変。 -/
theorem HalfTurnEquivariant.gravity : HalfTurnEquivariant Flow.gravity := by
  intro shape
  exact Shape.gravity.rotate180_comm shape

/-- Pin Pusher flow は 180° 等変。 -/
theorem HalfTurnEquivariant.pinPush (config : GameConfig) :
    HalfTurnEquivariant (Flow.pinPush config) := by
  intro shape
  exact Shape.pinPush.rotate180_comm shape config

/-- Trash flow は 180° 回転入力に依存しない。 -/
theorem HalfTurnUnitInvariant.trash : HalfTurnUnitInvariant Flow.trash := by
  intro shape
  exact Shape.trash.rotate180_comm shape

/-- Trash flow は CCW 回転入力に依存しない。 -/
theorem CCWUnitInvariant.trash : CCWUnitInvariant Flow.trash := by
  intro shape
  exact Shape.trash.rotateCCW_comm shape

/-- Cutter flow は 180° 回転で出力成分が swap される。 -/
theorem HalfTurnSwapEquivariant.cut : HalfTurnSwapEquivariant Flow.cut := by
  intro shape
  change Shape.cut shape.rotate180 =
    ((Shape.cut shape).2.rotate180, (Shape.cut shape).1.rotate180)
  simpa [Shape.cut] using Shape.cut.rotate180_comm shape

/-- Swapper flow は 180° 回転で出力成分が swap される。 -/
theorem HalfTurnPairSwapEquivariant.swapShapes : HalfTurnPairSwapEquivariant Flow.swapShapes := by
  intro input
  change Shape.swap input.1.rotate180 input.2.rotate180 =
    ((Shape.swap input.1 input.2).2.rotate180, (Shape.swap input.1 input.2).1.rotate180)
  exact Shape.swap.rotate180_comm input.1 input.2

/-- Stacker flow は CW 回転と可換。 -/
theorem CWPairInputEquivariant.stack (config : GameConfig) :
    CWPairInputEquivariant (Flow.stack config) := by
  intro input
  change Shape.rotateCW (Shape.stack input.1 input.2 config) =
    Shape.stack (Shape.rotateCW input.1) (Shape.rotateCW input.2) config
  exact Shape.stack.rotateCW_comm input.1 input.2 config

/-- Stacker flow は 180° 回転と可換。 -/
theorem HalfTurnPairInputEquivariant.stack (config : GameConfig) :
    HalfTurnPairInputEquivariant (Flow.stack config) := by
  intro input
  change Shape.rotate180 (Shape.stack input.1 input.2 config) =
    Shape.stack (Shape.rotate180 input.1) (Shape.rotate180 input.2) config
  exact Shape.stack.rotate180_comm input.1 input.2 config

end Flow
end S2IL
