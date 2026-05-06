import S2IL.Flow.Eval

/-!
# S2IL.Flow.Equivariance

Flow 評価の機能的等価性と回転等変性の型。

現段階では `FlowGraph.evaluate` の具体的なマシン意味論は未接続なので、等価性と
等変性を後続 theorem の受け皿となる Prop として固定する。
-/

namespace S2IL

namespace FlowItem

/-- Flow item に CW 回転を作用させる。液剤は回転で変化しない。 -/
def rotateCW : FlowItem -> FlowItem
  | shape value => shape value.rotateCW
  | fluid value => fluid value

/-- Flow item に 180° 回転を作用させる。液剤は回転で変化しない。 -/
def rotate180 : FlowItem -> FlowItem
  | shape value => shape value.rotate180
  | fluid value => fluid value

/-- Flow item に CCW 回転を作用させる。液剤は回転で変化しない。 -/
def rotateCCW : FlowItem -> FlowItem
  | shape value => shape value.rotateCCW
  | fluid value => fluid value

/-- CW 回転は Flow item のストリーム種別を変えない。 -/
theorem kind_rotateCW (item : FlowItem) : item.rotateCW.kind = item.kind := by
  cases item <;> rfl

/-- 180° 回転は Flow item のストリーム種別を変えない。 -/
theorem kind_rotate180 (item : FlowItem) : item.rotate180.kind = item.kind := by
  cases item <;> rfl

/-- CCW 回転は Flow item のストリーム種別を変えない。 -/
theorem kind_rotateCCW (item : FlowItem) : item.rotateCCW.kind = item.kind := by
  cases item <;> rfl

end FlowItem

namespace FlowObservation

/-- 観測 tick を保ったまま Flow item を CW 回転する。 -/
def rotateCW (observation : FlowObservation) : FlowObservation :=
  { observation with item := observation.item.rotateCW }

/-- 観測 tick を保ったまま Flow item を 180° 回転する。 -/
def rotate180 (observation : FlowObservation) : FlowObservation :=
  { observation with item := observation.item.rotate180 }

/-- 観測 tick を保ったまま Flow item を CCW 回転する。 -/
def rotateCCW (observation : FlowObservation) : FlowObservation :=
  { observation with item := observation.item.rotateCCW }

end FlowObservation

namespace FlowStream

/-- stream の全観測 item を CW 回転する。 -/
def rotateCW (stream : FlowStream) : FlowStream :=
  { stream with observations := stream.observations.map FlowObservation.rotateCW }

/-- stream の全観測 item を 180° 回転する。 -/
def rotate180 (stream : FlowStream) : FlowStream :=
  { stream with observations := stream.observations.map FlowObservation.rotate180 }

/-- stream の全観測 item を CCW 回転する。 -/
def rotateCCW (stream : FlowStream) : FlowStream :=
  { stream with observations := stream.observations.map FlowObservation.rotateCCW }

end FlowStream

namespace FlowInput

/-- graph 入力 stream を CW 回転する。入力先ポートは変えない。 -/
def rotateCW (input : FlowInput) : FlowInput :=
  { input with stream := input.stream.rotateCW }

/-- graph 入力 stream を 180° 回転する。入力先ポートは変えない。 -/
def rotate180 (input : FlowInput) : FlowInput :=
  { input with stream := input.stream.rotate180 }

/-- graph 入力 stream を CCW 回転する。入力先ポートは変えない。 -/
def rotateCCW (input : FlowInput) : FlowInput :=
  { input with stream := input.stream.rotateCCW }

end FlowInput

namespace FlowOutput

/-- graph 出力 stream を CW 回転する。出力元ポートは変えない。 -/
def rotateCW (output : FlowOutput) : FlowOutput :=
  { output with stream := output.stream.rotateCW }

/-- graph 出力 stream を 180° 回転する。出力元ポートは変えない。 -/
def rotate180 (output : FlowOutput) : FlowOutput :=
  { output with stream := output.stream.rotate180 }

/-- graph 出力 stream を CCW 回転する。出力元ポートは変えない。 -/
def rotateCCW (output : FlowOutput) : FlowOutput :=
  { output with stream := output.stream.rotateCCW }

end FlowOutput

namespace FlowInputs

/-- graph 入力群を CW 回転する。 -/
def rotateCW (inputs : FlowInputs) : FlowInputs :=
  { streams := inputs.streams.map FlowInput.rotateCW }

/-- graph 入力群を 180° 回転する。 -/
def rotate180 (inputs : FlowInputs) : FlowInputs :=
  { streams := inputs.streams.map FlowInput.rotate180 }

/-- graph 入力群を CCW 回転する。 -/
def rotateCCW (inputs : FlowInputs) : FlowInputs :=
  { streams := inputs.streams.map FlowInput.rotateCCW }

end FlowInputs

namespace FlowOutputs

/-- graph 出力群を CW 回転する。 -/
def rotateCW (outputs : FlowOutputs) : FlowOutputs :=
  { streams := outputs.streams.map FlowOutput.rotateCW }

/-- graph 出力群を 180° 回転する。 -/
def rotate180 (outputs : FlowOutputs) : FlowOutputs :=
  { streams := outputs.streams.map FlowOutput.rotate180 }

/-- graph 出力群を CCW 回転する。 -/
def rotateCCW (outputs : FlowOutputs) : FlowOutputs :=
  { streams := outputs.streams.map FlowOutput.rotateCCW }

/-- 空出力は CW 回転で不変。 -/
theorem rotateCW_empty : FlowOutputs.empty.rotateCW = FlowOutputs.empty := rfl

/-- 空出力は 180° 回転で不変。 -/
theorem rotate180_empty : FlowOutputs.empty.rotate180 = FlowOutputs.empty := rfl

/-- 空出力は CCW 回転で不変。 -/
theorem rotateCCW_empty : FlowOutputs.empty.rotateCCW = FlowOutputs.empty := rfl

end FlowOutputs

namespace FlowGraph

/-- 2 つの FlowGraph が全入力・全 window で同じ評価結果を返すこと。 -/
def FunctionallyEquivalent (left right : FlowGraph) : Prop :=
  ∀ window inputs, left.evaluate window inputs = right.evaluate window inputs

/-- FlowGraph の CW 回転等変性。

入力を CW 回転してから評価することと、評価結果を CW 回転することが一致する。 -/
def RotateCWEquivariant (graph : FlowGraph) : Prop :=
  ∀ window inputs,
    graph.evaluate window inputs.rotateCW =
      (graph.evaluate window inputs).map FlowOutputs.rotateCW

/-- FlowGraph の 180° 回転等変性。 -/
def Rotate180Equivariant (graph : FlowGraph) : Prop :=
  ∀ window inputs,
    graph.evaluate window inputs.rotate180 =
      (graph.evaluate window inputs).map FlowOutputs.rotate180

/-- FlowGraph の CCW 回転等変性。 -/
def RotateCCWEquivariant (graph : FlowGraph) : Prop :=
  ∀ window inputs,
    graph.evaluate window inputs.rotateCCW =
      (graph.evaluate window inputs).map FlowOutputs.rotateCCW

/-- 機能的等価性は反射的。 -/
theorem functionallyEquivalent_refl (graph : FlowGraph) :
    graph.FunctionallyEquivalent graph := by
  intro window inputs
  rfl

/-- 機能的等価性は対称的。 -/
theorem FunctionallyEquivalent.symm {left right : FlowGraph}
    (h : left.FunctionallyEquivalent right) :
    right.FunctionallyEquivalent left := by
  intro window inputs
  exact (h window inputs).symm

/-- 機能的等価性は推移的。 -/
theorem FunctionallyEquivalent.trans {left middle right : FlowGraph}
    (hLeft : left.FunctionallyEquivalent middle)
    (hRight : middle.FunctionallyEquivalent right) :
    left.FunctionallyEquivalent right := by
  intro window inputs
  exact Eq.trans (hLeft window inputs) (hRight window inputs)

end FlowGraph

end S2IL
