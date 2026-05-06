import S2IL.Flow.Eval

/-!
# S2IL.Flow.Examples

Shape Processing Flow の代表固定フロー例。

現段階では、graph 構造の well-formed 検証と Operations 直呼びの代表値検証を
分離して扱う。`FlowGraph.evaluate` へのマシン意味論接続は後続フェーズで追加する。
-/

namespace S2IL
namespace Flow
namespace Examples

private def shapeCodeOrEmpty (code : String) : Shape :=
  match Shape.ofString? code with
  | some shape => shape
  | none => []

private def amount1 : FlowAmount := { units := 1 }

private def beltThroughput : Throughput :=
  { kind := StreamKind.belt, amount := amount1 }

private def beltCapacity : Capacity :=
  { kind := StreamKind.belt, amount := amount1 }

private def capability : Capability :=
  { throughput := beltThroughput,
    inputCapacity := beltCapacity,
    outputCapacity := beltCapacity,
    requires := [], consumes := [], produces := [] }

private def node (id : NodeId) (kind : MachineKind) : MachineNode :=
  { id := id, spec := kind.machineSpec capability }

private def edge (sourceNode sourcePort targetNode targetPort : Nat) : FlowEdge :=
  { source := { node := sourceNode, port := sourcePort },
    target := { node := targetNode, port := targetPort } }

private def beltStream (shape : Shape) : FlowStream :=
  { kind := StreamKind.belt,
    observations := [{ tick := 0, item := FlowItem.shape shape }] }

private def pipeStream (fluid : Fluid) : FlowStream :=
  { kind := StreamKind.pipe,
    observations := [{ tick := 0, item := FlowItem.fluid fluid }] }

private def diagonalSplitNodesAt (offset : Nat) : List MachineNode :=
  [ node (offset + 0) MachineKind.cutter,
    node (offset + 1) MachineKind.cutter,
    node (offset + 2) MachineKind.rotator,
    node (offset + 3) MachineKind.rotator,
    node (offset + 4) MachineKind.swapper,
    node (offset + 5) MachineKind.swapper,
    node (offset + 6) MachineKind.rotator ]

private def diagonalSplitEdgesAt (offset : Nat) : List FlowEdge :=
  [ edge (offset + 0) 0 (offset + 2) 0,
    edge (offset + 1) 1 (offset + 3) 0,
    edge (offset + 3) 0 (offset + 4) 0,
    edge (offset + 2) 0 (offset + 4) 1,
    edge (offset + 3) 0 (offset + 5) 0,
    edge (offset + 2) 0 (offset + 5) 1,
    edge (offset + 5) 1 (offset + 6) 0 ]

/-- Diagonal-Split 代表入力 `RbRbRbRb`。 -/
def diagonalSplitInput : Shape := shapeCodeOrEmpty "RbRbRbRb"

/-- Diagonal-Split の期待出力 `Rb--Rb--`。 -/
def diagonalSplitExpected : Shape := shapeCodeOrEmpty "Rb--Rb--"

/-- 4 レイヤ代表フローで使う未着色 rectangle 入力。 -/
def fullUncoloredRectangles : Shape := shapeCodeOrEmpty "RuRuRuRu"

/-- 4 レイヤ代表フローで使う未着色 star 入力。 -/
def fullUncoloredStars : Shape := shapeCodeOrEmpty "SuSuSuSu"

/-- Diagonal-Split 1 セットを Operations 直呼びで表した出力ペア。

第 1 出力と、追加回転後の第 2 出力はいずれも同じ対角形 `Rb--Rb--` を表す。 -/
def diagonalSplitOutputs (input : Shape) : Shape × Shape :=
  let cutPair := Shape.cut input
  let rotatedEast := Shape.rotateCW cutPair.1
  let rotatedWest := Shape.rotateCW cutPair.2
  let swapped := Shape.swap rotatedWest rotatedEast
  (swapped.1, Shape.rotateCW swapped.2)

/-- Diagonal-Split 1 セットの内部 graph。

Cutter x2、Rotator x2、Swapper x2、2 本目の対角出力を揃える Rotator x1 からなる。 -/
def diagonalSplitGraph : FlowGraph :=
  { nodes := diagonalSplitNodesAt 0,
    edges := diagonalSplitEdgesAt 0 }

/-- Diagonal-Split graph に与える代表外部入力 stream。 -/
def diagonalSplitInputs : FlowInputs :=
  { streams :=
      [ { target := { node := 0, port := 0 }, stream := beltStream diagonalSplitInput },
        { target := { node := 1, port := 0 }, stream := beltStream diagonalSplitInput } ] }

/-- `RuRuRuRu` を青に塗った中間 shape。 -/
def paintedRectangles : Shape :=
  Shape.paint fullUncoloredRectangles Color.blue

/-- 4 レイヤ end-to-end 代表フローの構造的な出力 shape。

`Shape.stack` 本体は後続の評価意味論で接続するため、ここでは stacker の下から上への
レイヤ順を `Shape.placeAbove` で固定する。 -/
def fourLayerStructuralOutput : Shape :=
  let diagonalA := (diagonalSplitOutputs paintedRectangles).1
  let diagonalB := (diagonalSplitOutputs paintedRectangles).1
  Shape.placeAbove (Shape.placeAbove (Shape.placeAbove diagonalA fullUncoloredRectangles) diagonalB)
    fullUncoloredStars

/-- 4 レイヤ end-to-end 代表フローの期待 Shape Code。 -/
def fourLayerExpected : Shape :=
  shapeCodeOrEmpty "Rb--Rb--:RuRuRuRu:Rb--Rb--:SuSuSuSu"

/-- Painter、Diagonal-Split x2、Stacker x3 を展開した end-to-end graph。 -/
def fourLayerEndToEndGraph : FlowGraph :=
  { nodes :=
      [node 0 MachineKind.painter] ++
      diagonalSplitNodesAt 1 ++
      diagonalSplitNodesAt 8 ++
      [ node 15 MachineKind.stacker,
        node 16 MachineKind.stacker,
        node 17 MachineKind.stacker ],
    edges :=
      [ edge 0 0 1 0,
        edge 0 0 2 0,
        edge 0 0 8 0,
        edge 0 0 9 0 ] ++
      diagonalSplitEdgesAt 1 ++
      diagonalSplitEdgesAt 8 ++
      [ edge 5 0 15 0,
        edge 15 0 16 0,
        edge 12 0 16 1,
        edge 16 0 17 0 ] }

/-- 4 レイヤ end-to-end graph に与える代表外部入力 stream。 -/
def fourLayerInputs : FlowInputs :=
  { streams :=
      [ { target := { node := 0, port := 0 }, stream := beltStream fullUncoloredRectangles },
        { target := { node := 0, port := 1 },
          stream := pipeStream { color := Color.blue, amount := { units := 1200 } } },
        { target := { node := 15, port := 1 }, stream := beltStream fullUncoloredRectangles },
        { target := { node := 17, port := 1 }, stream := beltStream fullUncoloredStars } ] }

end Examples
end Flow
end S2IL
