import S2IL.Flow

/-!
# Test.Flow.Examples

Shape Processing Flow の代表固定フロー例のテスト。
-/

open S2IL

namespace Test.Flow.Examples

-- ============================================================
-- Diagonal-Split internal graph
-- ============================================================

#guard Flow.Examples.diagonalSplitGraph.nodes.length == 7
#guard Flow.Examples.diagonalSplitGraph.edges.length == 7
#guard Flow.Examples.diagonalSplitGraph.wellFormed
#guard Flow.Examples.diagonalSplitInputs.wellFormed
#guard Flow.Examples.diagonalSplitInputs.compatibleWithGraph Flow.Examples.diagonalSplitGraph
#guard (Flow.Examples.diagonalSplitGraph.evaluate 1 Flow.Examples.diagonalSplitInputs).isSome

#guard Shape.toString Flow.Examples.diagonalSplitInput == "RbRbRbRb"
#guard Shape.toString Flow.Examples.diagonalSplitExpected == "Rb--Rb--"
#guard Shape.toString (Flow.Examples.diagonalSplitOutputs Flow.Examples.diagonalSplitInput).1 ==
  "Rb--Rb--"
#guard Shape.toString (Flow.Examples.diagonalSplitOutputs Flow.Examples.diagonalSplitInput).2 ==
  "Rb--Rb--"

example : FlowGraph.WellFormed Flow.Examples.diagonalSplitGraph := rfl

-- ============================================================
-- 4-layer end-to-end decomposed graph
-- ============================================================

#guard Flow.Examples.fourLayerEndToEndGraph.nodes.length == 18
#guard Flow.Examples.fourLayerEndToEndGraph.edges.length == 22
#guard Flow.Examples.fourLayerEndToEndGraph.wellFormed
#guard Flow.Examples.fourLayerInputs.wellFormed
#guard Flow.Examples.fourLayerInputs.compatibleWithGraph Flow.Examples.fourLayerEndToEndGraph
#guard (Flow.Examples.fourLayerEndToEndGraph.evaluate 1 Flow.Examples.fourLayerInputs).isSome

#guard Shape.toString Flow.Examples.paintedRectangles == "RbRbRbRb"
#guard Shape.toString Flow.Examples.fourLayerStructuralOutput ==
  "Rb--Rb--:RuRuRuRu:Rb--Rb--:SuSuSuSu"
#guard Shape.toString Flow.Examples.fourLayerExpected ==
  "Rb--Rb--:RuRuRuRu:Rb--Rb--:SuSuSuSu"

example : FlowGraph.WellFormed Flow.Examples.fourLayerEndToEndGraph := rfl

end Test.Flow.Examples
