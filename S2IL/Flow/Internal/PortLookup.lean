import S2IL.Flow.Graph.Basic

/-!
# S2IL.Flow.Internal.PortLookup

FlowGraph の node / port lookup と、その基本補題。
-/

namespace S2IL

namespace MachineNode

/-- ノードの入力ポートを ID で取得する。 -/
def inputPort? (node : MachineNode) (port : PortId) : Option PortSpec :=
  node.spec.ports.inputs[port]?

/-- ノードの出力ポートを ID で取得する。 -/
def outputPort? (node : MachineNode) (port : PortId) : Option PortSpec :=
  node.spec.ports.outputs[port]?

/-- `inputPort?` は `MachineSpec` の入力ポート列への lookup。 -/
theorem inputPort?_eq_getElem? (node : MachineNode) (port : PortId) :
    node.inputPort? port = node.spec.ports.inputs[port]? := rfl

/-- `outputPort?` は `MachineSpec` の出力ポート列への lookup。 -/
theorem outputPort?_eq_getElem? (node : MachineNode) (port : PortId) :
    node.outputPort? port = node.spec.ports.outputs[port]? := rfl

end MachineNode

namespace FlowGraph

/-- graph 内のノードを ID で取得する。 -/
def node? (graph : FlowGraph) (id : NodeId) : Option MachineNode :=
  graph.nodes.find? (fun node => node.id == id)

/-- graph 上の入力ポート参照を解決する。 -/
def inputPort? (graph : FlowGraph) (ref : PortRef) : Option PortSpec :=
  match graph.node? ref.node with
  | none => none
  | some node => node.inputPort? ref.port

/-- graph 上の出力ポート参照を解決する。 -/
def outputPort? (graph : FlowGraph) (ref : PortRef) : Option PortSpec :=
  match graph.node? ref.node with
  | none => none
  | some node => node.outputPort? ref.port

/-- ノード ID が graph 内で一意かを判定する。 -/
def nodeIdsUnique (graph : FlowGraph) : Bool :=
  let ids := graph.nodes.map (fun node => node.id)
  ids.length == ids.eraseDups.length

/-- edge の参照端点が実在するポートかを判定する。 -/
def edgePortsExist (graph : FlowGraph) (edge : FlowEdge) : Bool :=
  (graph.outputPort? edge.source).isSome && (graph.inputPort? edge.target).isSome

/-- edge の出力ポートと入力ポートのストリーム種別が一致するかを判定する。 -/
def edgeKindsMatch (graph : FlowGraph) (edge : FlowEdge) : Bool :=
  match graph.outputPort? edge.source, graph.inputPort? edge.target with
  | some sourcePort, some targetPort => sourcePort.kind == targetPort.kind
  | _, _ => false

/-- graph にノードが存在しなければ、入力ポート参照は解決できない。 -/
theorem inputPort?_eq_none_of_node?_eq_none
    {graph : FlowGraph} {ref : PortRef}
    (hNode : graph.node? ref.node = none) :
    graph.inputPort? ref = none := by
  unfold inputPort?
  rw [hNode]

/-- graph にノードが存在しなければ、出力ポート参照は解決できない。 -/
theorem outputPort?_eq_none_of_node?_eq_none
    {graph : FlowGraph} {ref : PortRef}
    (hNode : graph.node? ref.node = none) :
    graph.outputPort? ref = none := by
  unfold outputPort?
  rw [hNode]

/-- 入出力ポート参照が解決できる edge は、端点存在判定を満たす。 -/
theorem edgePortsExist_eq_true_of_output_input
    {graph : FlowGraph} {edge : FlowEdge} {sourcePort targetPort : PortSpec}
    (hSource : graph.outputPort? edge.source = some sourcePort)
    (hTarget : graph.inputPort? edge.target = some targetPort) :
    graph.edgePortsExist edge = true := by
  unfold edgePortsExist
  rw [hSource, hTarget]
  rfl

/-- 入出力ポート参照が解決でき、種別が等しい edge は、種別一致判定を満たす。 -/
theorem edgeKindsMatch_eq_true_of_output_input
    {graph : FlowGraph} {edge : FlowEdge} {sourcePort targetPort : PortSpec}
    (hSource : graph.outputPort? edge.source = some sourcePort)
    (hTarget : graph.inputPort? edge.target = some targetPort)
    (hKind : sourcePort.kind = targetPort.kind) :
    graph.edgeKindsMatch edge = true := by
  unfold edgeKindsMatch
  rw [hSource, hTarget]
  cases sourcePort with
  | mk sourceKind sourceName =>
  cases targetPort with
  | mk targetKind targetName =>
  cases hKind
  cases sourceKind
  · change (StreamKind.belt == StreamKind.belt) = true
    rfl
  · change (StreamKind.pipe == StreamKind.pipe) = true
    rfl

end FlowGraph

end S2IL
