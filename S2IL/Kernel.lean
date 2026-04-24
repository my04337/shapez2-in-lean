-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel.BFS
import S2IL.Kernel.Bond
import S2IL.Kernel.Transform

/-!
# S2IL.Kernel facade

Gravity 非依存の横断基盤 (Layer A)。Phase B では axiom scaffold。

## 公開 API

- BFS: `genericBfs` / `GenericReachable` / 健全性・完全性
- Bond: `isBonded` / `cluster` / `allClusters` / CW 等変性
- Transform: `Shape.rotateCW` （中心）+ `rotate180` / `rotateCCW` （派生）

## サブモジュール（公開）

- `S2IL.Kernel.BFS`        — 汎用 BFS と完全性定理
- `S2IL.Kernel.Bond`       — CrystalBond（構造結合判定）
- `S2IL.Kernel.Transform`  — rotateCW / rotate180 / rotateCCW

## Internal（外部 import 禁止）

- `S2IL.Kernel.Internal.BFSImpl`
- `S2IL.Kernel.Internal.BondImpl`
- `S2IL.Kernel.Internal.Rotate180Lemmas`
-/
