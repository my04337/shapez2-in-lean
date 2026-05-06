-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Flow.MachineSpec

/-!
# S2IL.Flow.Graph

Shape Processing Flow の加工ライン graph。

初期実装では、DAG 性を `NodeId` の昇順 edge という十分条件で近似し、
端点存在とポート種別一致を computable な `wellFormed` 判定で確認する。
-/

namespace S2IL

/-- FlowGraph 内のマシンノード。 -/
structure MachineNode where
  /-- graph 内で一意に参照するノード ID。 -/
  id : NodeId
  /-- このノードのマシン仕様。 -/
  spec : MachineSpec
deriving Repr, DecidableEq, BEq

/-- マシンノード上のポート参照。 -/
structure PortRef where
  /-- 参照先ノード ID。 -/
  node : NodeId
  /-- 参照先ポート ID。 -/
  port : PortId
deriving Repr, DecidableEq, BEq

/-- 出力ポートから入力ポートへ向かう Flow edge。 -/
structure FlowEdge where
  /-- 接続元の出力ポート。 -/
  source : PortRef
  /-- 接続先の入力ポート。 -/
  target : PortRef
deriving Repr, DecidableEq, BEq

/-- マシンノードと接続からなる加工ライン graph。 -/
structure FlowGraph where
  /-- graph に含まれるマシンノード。 -/
  nodes : List MachineNode
  /-- graph に含まれる接続。 -/
  edges : List FlowEdge
deriving Repr, DecidableEq, BEq

namespace MachineNode

/-- ノードの入力ポートを ID で取得する。 -/
def inputPort? (node : MachineNode) (port : PortId) : Option PortSpec :=
  node.spec.ports.inputs[port]?

/-- ノードの出力ポートを ID で取得する。 -/
def outputPort? (node : MachineNode) (port : PortId) : Option PortSpec :=
  node.spec.ports.outputs[port]?

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

/-- edge が `NodeId` 昇順に従うかを判定する。

初期 DAG 判定として、接続元ノード ID が接続先ノード ID より小さいことを要求する。 -/
def edgeRespectsNodeOrder (_graph : FlowGraph) (edge : FlowEdge) : Bool :=
  decide (edge.source.node < edge.target.node)

/-- FlowGraph の初期 well-formed 判定。 -/
def wellFormed (graph : FlowGraph) : Bool :=
  graph.nodeIdsUnique && graph.edges.all (fun edge =>
    graph.edgePortsExist edge && graph.edgeKindsMatch edge && graph.edgeRespectsNodeOrder edge)

/-- `wellFormed` を Prop として使うための述語。 -/
def WellFormed (graph : FlowGraph) : Prop :=
  graph.wellFormed = true

end FlowGraph

end S2IL
