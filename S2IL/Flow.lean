-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Flow.Defs
import S2IL.Flow.Equivalence
import S2IL.Flow.Equivariance
import S2IL.Flow.Examples

/-!
# S2IL.Flow facade

Layer C-1 Shape Processing Flow の統合入口。

## 公開 API（主要）

- `Flow α β` — 型付きフロー DSL
- `Flow.eval` — フローの純粋評価関数
- product combinators: `Flow.swap` / `Flow.dup` / `Flow.pairMap` /
  `Flow.assocLeft` / `Flow.assocRight`
- source/helper: `Flow.constant`
- primitive wrappers: `Flow.rotateCW` / `Flow.rotate180` / `Flow.rotateCCW` /
  `Flow.halfDestroy` / `Flow.cut` / `Flow.swapShapes` / `Flow.combineHalves` /
  `Flow.mix` / `Flow.paintWith` / `Flow.crystallizeWith` / `Flow.paint` /
  `Flow.crystallize` / `Flow.gravity` / `Flow.stack` / `Flow.pinPush`
- `Flow.Equivalent` — `Flow.eval` による外延的等価性
- `Flow.CWEquivariant` / `Flow.HalfTurnEquivariant` / `Flow.HalfTurnSwapEquivariant`
- `Flow.CWPairInputEquivariant` / `Flow.HalfTurnPairInputEquivariant`
- `Flow.Examples.*` — 代表フロー

## サブモジュール（公開）

- `S2IL.Flow.Defs`         — Flow 型、評価、primitive wrappers
- `S2IL.Flow.Equivalence`  — 外延的等価性と congruence
- `S2IL.Flow.Equivariance` — 回転等変性 predicate と合成補題
- `S2IL.Flow.Examples`     — 代表フロー

## Internal（外部 import 禁止）

- `S2IL.Flow.Internal.*`（今後作成予定）
-/
