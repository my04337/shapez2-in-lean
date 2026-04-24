-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

/-!
# S2IL.Kernel facade

Gravity 非依存の横断基盤 (Layer A)。

## 公開 API

Phase A 時点では空。Phase B で axiom scaffold を追加予定。

## サブモジュール（公開）

- `S2IL.Kernel.BFS`        — genericBFS と完全性定理
- `S2IL.Kernel.Bond`       — CrystalBond
- `S2IL.Kernel.Transform`  — rotateCW / rotate180 / rotateCCW

## Internal（外部 import 禁止）

- `S2IL.Kernel.Internal.*`
-/

namespace S2IL.Kernel
end S2IL.Kernel
