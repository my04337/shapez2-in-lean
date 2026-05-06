import S2IL.Flow.MachineSpec

/-!
# S2IL.Flow.Graph.Basic

Shape Processing Flow の graph 基礎型。

lookup や DAG 判定は `S2IL.Flow.Internal.*` に分離し、本モジュールは
型定義だけを保持する。
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

end S2IL
