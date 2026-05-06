import S2IL.Flow.Graph

/-!
# S2IL.Flow.Eval

Shape Processing Flow の finite observation window 評価 API。

本モジュールでは、評価関数の入出力境界と観測 window の形を先に固定する。
各 `MachineKind` の具体的なストリーム意味論は後続フェーズで接続する。
-/

namespace S2IL

/-- Flow stream 上で観測される 1 アイテム。 -/
inductive FlowItem where
  | shape (value : Shape)
  | fluid (value : Fluid)
deriving Repr

namespace FlowItem

/-- Flow item が属するストリーム種別。 -/
def kind : FlowItem -> StreamKind
  | shape _ => StreamKind.belt
  | fluid _ => StreamKind.pipe

end FlowItem

/-- 1 tick 上で観測された Flow item。 -/
structure FlowObservation where
  /-- 観測 tick。 -/
  tick : Nat
  /-- 観測された item。 -/
  item : FlowItem
deriving Repr

namespace FlowObservation

/-- 観測 item が指定ストリーム種別と一致するかを判定する。 -/
def matchesKind (kind : StreamKind) (observation : FlowObservation) : Bool :=
  observation.item.kind == kind

/-- 観測 tick が有限観測 window 内に入るかを判定する。 -/
def inWindow (window : Nat) (observation : FlowObservation) : Bool :=
  decide (observation.tick < window)

end FlowObservation

/-- 有限 tick 列として表した Flow stream。 -/
structure FlowStream where
  /-- この stream の種別。 -/
  kind : StreamKind
  /-- tick ごとの観測値。 -/
  observations : List FlowObservation
deriving Repr

namespace FlowStream

/-- stream 内の全観測値が stream 種別と一致するかを判定する。 -/
def wellFormed (stream : FlowStream) : Bool :=
  stream.observations.all (FlowObservation.matchesKind stream.kind)

/-- 指定された有限観測 window に stream を切り詰める。 -/
def takeWindow (window : Nat) (stream : FlowStream) : FlowStream :=
  { stream with observations := stream.observations.filter (FlowObservation.inWindow window) }

end FlowStream

/-- graph 境界の入力ポートに与える stream。 -/
structure FlowInput where
  /-- 入力先ポート。 -/
  target : PortRef
  /-- 入力 stream。 -/
  stream : FlowStream
deriving Repr

namespace FlowInput

/-- 入力 stream が graph 上の実在入力ポートとストリーム種別で一致するかを判定する。 -/
def compatibleWithGraph (graph : FlowGraph) (input : FlowInput) : Bool :=
  match graph.inputPort? input.target with
  | some port => port.kind == input.stream.kind
  | none => false

end FlowInput

/-- graph 境界の出力ポートから観測する stream。 -/
structure FlowOutput where
  /-- 出力元ポート。 -/
  source : PortRef
  /-- 出力 stream。 -/
  stream : FlowStream
deriving Repr

/-- FlowGraph 評価に与える外部入力 stream 群。 -/
structure FlowInputs where
  /-- graph 境界へ流し込む入力 stream。 -/
  streams : List FlowInput
deriving Repr

namespace FlowInputs

/-- 入力 stream 群がそれぞれ自分の stream 種別と整合するかを判定する。 -/
def wellFormed (inputs : FlowInputs) : Bool :=
  inputs.streams.all (fun input => input.stream.wellFormed)

/-- 入力 stream 群が graph 境界の入力ポートと整合するかを判定する。 -/
def compatibleWithGraph (graph : FlowGraph) (inputs : FlowInputs) : Bool :=
  inputs.streams.all (FlowInput.compatibleWithGraph graph)

/-- すべての入力 stream を有限観測 window に切り詰める。 -/
def takeWindow (window : Nat) (inputs : FlowInputs) : FlowInputs :=
  { streams := inputs.streams.map (fun input => { input with stream := input.stream.takeWindow window }) }

end FlowInputs

/-- FlowGraph 評価で得られる外部出力 stream 群。 -/
structure FlowOutputs where
  /-- graph 境界から観測された出力 stream。 -/
  streams : List FlowOutput
deriving Repr

namespace FlowOutputs

/-- 空の出力 stream 群。意味論未接続の graph 評価で使う初期値。 -/
def empty : FlowOutputs :=
  { streams := [] }

end FlowOutputs

namespace FlowGraph

/-- finite observation window で FlowGraph を評価する。

現段階では API の形を固定し、graph と入力 stream の基本整合性だけ確認する。
具体的なマシン意味論は `MachineKind.semantics` と接続する後続フェーズで追加する。 -/
def evaluate (graph : FlowGraph) (window : Nat) (inputs : FlowInputs) : Option FlowOutputs :=
  let windowedInputs := inputs.takeWindow window
  if graph.wellFormed && windowedInputs.wellFormed && windowedInputs.compatibleWithGraph graph then
    some FlowOutputs.empty
  else
    none

end FlowGraph

end S2IL
