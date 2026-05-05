-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel.CrystalBondCluster
import S2IL.Kernel.CrystalBond
import S2IL.Kernel.Transform

/-!
# S2IL.Kernel facade

Gravity 非依存の横断基盤 (Layer A)。

## 公開 API

- CrystalBondCluster: `CrystalBondClusterRel` (Prop, `Relation.ReflTransGen IsCrystalBonded`) / `crystalBondClusterSet` (Finset, noncomputable) / 反射・対称律 / CW 等変性 (`CrystalBondClusterRel.rotateCW`, `crystalBondClusterSet.rotateCW_comm`)
- CrystalBond: `IsCrystalBonded` (Prop) / `isCrystalBonded` (Bool := decide) / 対称性 / CW 等変性
- Transform: `Shape.rotateCW` (def) / `rotate180` / `rotateCCW` + 4 周性、`Shape.normalize.rotateCW_comm`、`QuarterPos.down_rotateCW`（全て theorem）

## サブモジュール（公開）

- `S2IL.Kernel.CrystalBondCluster` — 結晶結合クラスタ表現（Relation.ReflTransGen + Finset, axiom-free）
- `S2IL.Kernel.CrystalBond` — IsCrystalBonded（結晶結合判定、Prop/Bool 二層規約, axiom-free）
- `S2IL.Kernel.Transform`  — rotateCW / rotate180 / rotateCCW

## Internal（外部 import 禁止）

- `S2IL.Kernel.Internal.CrystalBondImpl`
- `S2IL.Kernel.Internal.Rotate180Lemmas`

NOTE: `crystalBondClusterList` / `allCrystalBondClusters` 等の計算的 List API および
`S2IL.Kernel.Internal.CrystalBondClusterImpl` は 今後 MAM/Shatter が必要になってから追加する（[architecture §1.10](../docs/s2il/architecture-layer-ab.md)）。
-/
