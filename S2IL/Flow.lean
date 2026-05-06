-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Flow.Types
import S2IL.Flow.Capability
import S2IL.Flow.Internal.CapabilityAlgebra
import S2IL.Flow.MachineSpec
import S2IL.Flow.Graph
import S2IL.Flow.Eval
import S2IL.Flow.Equivariance
import S2IL.Flow.Config
import S2IL.Flow.Examples

/-!
# S2IL.Flow facade

Shape Processing Flow（Layer C-1）の公開 API 集約点。

## 公開 API（Types 経由）

- 型: `FlowAmount` / `StreamKind` / `Fluid` / `PortSpec` / `NodeId` / `PortId`

## 公開 API（Capability 経由）

- 型: `Throughput` / `Capacity` / `ThroughputRequirement` / `Capability`
- 計算: `ceilDiv` / `minMachineCount`

## 公開 API（MachineSpec / Graph 経由）

- 型: `NodeSpec` / `MachineKind` / `MachineSemantics` / `MachineSpec`
- 型: `MachineNode` / `PortRef` / `FlowEdge` / `FlowGraph`
- 判定: `FlowGraph.wellFormed` / `FlowGraph.WellFormed` / `FlowGraph.acyclic`
- lookup: `FlowGraph.node?` / `inputPort?` / `outputPort?`

## 公開 API（Eval 経由）

- 型: `FlowItem` / `FlowObservation` / `FlowStream` / `FlowInput` / `FlowOutput` /
  `FlowInputs` / `FlowOutputs`
- 評価: `FlowGraph.evaluate`

## 公開 API（Equivariance / Config 経由）

- 等価性: `FlowGraph.FunctionallyEquivalent`
- 等変性: `FlowGraph.RotateCWEquivariant` / `Rotate180Equivariant` / `RotateCCWEquivariant`
- 設定: `SpeedTier` / `FlowConfig` / `FlowConfig.basic`

## 公開 API（Examples 経由）

- 代表 graph: `Flow.Examples.diagonalSplitGraph` / `fourLayerEndToEndGraph`
- 代表出力: `Flow.Examples.diagonalSplitOutputs` / `fourLayerStructuralOutput`

## サブモジュール（公開）

- `S2IL.Flow.Types` — ストリーム、液剤、ポートの基礎型
- `S2IL.Flow.Capability` — スループット、容量、処理能力の抽象型
- `S2IL.Flow.Internal.CapabilityAlgebra` — 必要台数下界計算の補助 API
- `S2IL.Flow.MachineSpec` — Operations facade と対応するマシン仕様
- `S2IL.Flow.Graph` — FlowGraph と well-formed 判定
- `S2IL.Flow.Graph.Basic` — FlowGraph の基礎型
- `S2IL.Flow.Internal.PortLookup` — node / port lookup と基本補題
- `S2IL.Flow.Internal.GraphAcyclic` — 到達可能性ベースの DAG 判定
- `S2IL.Flow.Eval` — finite observation window 評価 API
- `S2IL.Flow.Equivariance` — 機能的等価性と回転等変性の型
- `S2IL.Flow.Config` — 具体スループット値の設定層
- `S2IL.Flow.Examples` — Diagonal-Split / 4 レイヤ end-to-end の代表 graph
-/
