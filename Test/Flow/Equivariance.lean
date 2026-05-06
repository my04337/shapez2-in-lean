import S2IL.Flow

/-!
# Test.Flow.Equivariance

Flow の機能的等価性と回転等変性 API の型確認。
-/

open S2IL

namespace Test.Flow.Equivariance

private def sampleObservation : FlowObservation :=
  { tick := 7, item := FlowItem.shape Flow.Examples.diagonalSplitInput }

#guard (FlowItem.shape Flow.Examples.diagonalSplitInput).rotateCW.kind == StreamKind.belt
#guard (FlowItem.fluid { color := Color.blue, amount := { units := 1 } }).rotateCW.kind == StreamKind.pipe
#guard sampleObservation.rotateCW.tick == 7
#guard Flow.Examples.diagonalSplitInputs.rotateCW.streams.length ==
  Flow.Examples.diagonalSplitInputs.streams.length

example : FlowGraph.FunctionallyEquivalent
    Flow.Examples.diagonalSplitGraph Flow.Examples.diagonalSplitGraph :=
  FlowGraph.functionallyEquivalent_refl Flow.Examples.diagonalSplitGraph

example : Prop :=
  FlowGraph.RotateCWEquivariant Flow.Examples.diagonalSplitGraph

example : Prop :=
  FlowGraph.Rotate180Equivariant Flow.Examples.diagonalSplitGraph

example : Prop :=
  FlowGraph.RotateCCWEquivariant Flow.Examples.diagonalSplitGraph

example : FlowOutputs.empty.rotateCW = FlowOutputs.empty :=
  FlowOutputs.rotateCW_empty

end Test.Flow.Equivariance
