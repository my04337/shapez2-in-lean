-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Flow.Types
import S2IL.Flow.Capability
import S2IL.Flow.MachineSpec
import S2IL.Flow.Graph

/-!
# S2IL.Flow facade

Shape Processing Flow（Layer C-1）の公開 API 集約点。

## 公開 API（Types 経由）

- 型: `FlowAmount` / `StreamKind` / `Fluid` / `PortSpec` / `NodeId` / `PortId`

## 公開 API（Capability 経由）

- 型: `Throughput` / `Capacity` / `ThroughputRequirement` / `Capability`

## 公開 API（MachineSpec / Graph 経由）

- 型: `NodeSpec` / `MachineKind` / `MachineSemantics` / `MachineSpec`
- 型: `MachineNode` / `PortRef` / `FlowEdge` / `FlowGraph`
- 判定: `FlowGraph.wellFormed` / `FlowGraph.WellFormed`

## サブモジュール（公開）

- `S2IL.Flow.Types` — ストリーム、液剤、ポートの基礎型
- `S2IL.Flow.Capability` — スループット、容量、処理能力の抽象型
- `S2IL.Flow.MachineSpec` — Operations facade と対応するマシン仕様
- `S2IL.Flow.Graph` — FlowGraph と初期 well-formed 判定
-/
