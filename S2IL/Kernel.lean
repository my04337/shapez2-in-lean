-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel.Cluster
import S2IL.Kernel.Bond
import S2IL.Kernel.Transform

/-!
# S2IL.Kernel facade

Gravity 非依存の横断基盤 (Layer A)。Phase C re-scaffold 済み。

## 公開 API

- Cluster: `ClusterRel` (Prop, `Relation.ReflTransGen IsBonded`) / `clusterSet` (Finset, noncomputable) / 反射・対称律 / CW 等変性 (`ClusterRel.rotateCW`, `clusterSet.rotateCW_comm`)
- Bond: `IsBonded` (Prop) / `isBonded` (Bool := decide) / 対称性 / CW 等変性
- Transform: `Shape.rotateCW` (def) / `rotate180` / `rotateCCW` + 4 周性（全て theorem）

## サブモジュール（公開）

- `S2IL.Kernel.Cluster`    — クラスタ表現（Relation.ReflTransGen + Finset, axiom-free）
- `S2IL.Kernel.Bond`       — IsBonded（結合判定、Prop/Bool 二層規約, axiom-free）
- `S2IL.Kernel.Transform`  — rotateCW / rotate180 / rotateCCW

## Internal（外部 import 禁止）

- `S2IL.Kernel.Internal.BondImpl`
- `S2IL.Kernel.Internal.Rotate180Lemmas`

NOTE: `clusterList` / `allClusters` 等の計算的 List API および
`S2IL.Kernel.Internal.ClusterImpl` は Phase D で MAM/Shatter が必要に
なってから追加する（[architecture §1.10](../docs/plans/architecture-layer-ab.md)）。
-/
