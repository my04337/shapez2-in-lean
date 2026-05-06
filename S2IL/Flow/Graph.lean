-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Flow.Graph.Basic
import S2IL.Flow.Internal.PortLookup
import S2IL.Flow.Internal.GraphAcyclic

/-!
# S2IL.Flow.Graph

Shape Processing Flow の加工ライン graph。

端点存在、ポート種別一致、ノード ID 一意性、一般 DAG 性を computable な
`wellFormed` 判定で確認する。
-/

namespace S2IL

namespace FlowGraph

/-- FlowGraph の well-formed 判定。 -/
def wellFormed (graph : FlowGraph) : Bool :=
  graph.nodeIdsUnique && graph.edges.all (fun edge =>
    graph.edgePortsExist edge && graph.edgeKindsMatch edge) && graph.acyclic

/-- `wellFormed` を Prop として使うための述語。 -/
def WellFormed (graph : FlowGraph) : Prop :=
  graph.wellFormed = true

end FlowGraph

end S2IL
