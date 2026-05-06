import S2IL.Flow.Graph.Basic

/-!
# S2IL.Flow.Internal.GraphAcyclic

FlowGraph の computable な DAG 判定。

初期実装の `NodeId` 昇順 edge 近似を残しつつ、`wellFormed` から使う判定は
edge 向きに沿った到達可能性ベースの cycle 検出へ拡張する。
-/

namespace S2IL
namespace FlowGraph

/-- edge が `NodeId` 昇順に従うかを判定する。

互換用の十分条件として残す。一般 DAG 判定には `acyclic` を使う。 -/
def edgeRespectsNodeOrder (_graph : FlowGraph) (edge : FlowEdge) : Bool :=
  decide (edge.source.node < edge.target.node)

/-- 指定ノードから 1 edge で到達できるノード ID の一覧。 -/
def successors (graph : FlowGraph) (id : NodeId) : List NodeId :=
  graph.edges.foldr
    (fun edge acc => if edge.source.node == id then edge.target.node :: acc else acc)
    []

/-- 有限 fuel 付きの到達可能性判定。

`fuel` は graph が有限であることを computable recursion に伝えるための上限。 -/
def hasPathFrom (graph : FlowGraph) : Nat → List NodeId → NodeId → NodeId → Bool
  | 0, _, _, _ => false
  | fuel + 1, visited, source, target =>
      if source == target then
        true
      else if visited.contains source then
        false
      else
        (graph.successors source).any
          (fun next => graph.hasPathFrom fuel (source :: visited) next target)

/-- graph 内で使う到達可能性判定。 -/
def reaches (graph : FlowGraph) (source target : NodeId) : Bool :=
  graph.hasPathFrom (graph.nodes.length + graph.edges.length + 1) [] source target

/-- edge を 1 本選んだとき、target から source へ戻れるなら cycle が存在する。 -/
def edgeClosesCycle (graph : FlowGraph) (edge : FlowEdge) : Bool :=
  graph.reaches edge.target.node edge.source.node

/-- graph に cycle が存在するかを判定する。 -/
def hasCycle (graph : FlowGraph) : Bool :=
  graph.edges.any (graph.edgeClosesCycle)

/-- FlowGraph の一般 DAG 判定。 -/
def acyclic (graph : FlowGraph) : Bool :=
  !graph.hasCycle

end FlowGraph
end S2IL
