-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Settled.Defs
import S2IL.Operations.Settled.Equivariance
import S2IL.Operations.Settled.Normalize

/-!
# S2IL.Operations.Settled

Settled (安定状態、B-3) の facade。

## 数学的設計

`docs/shapez2/falling.md §4.2` に従い、接地 (`IsGrounded`) を Mathlib
`Relation.ReflTransGen` ベースで定義する。

## 公開 API

- Prop 層: `IsContact`, `IsUpwardGroundingContact`, `IsStructurallyBonded`,
  `IsGroundingEdge`, `IsGrounded`, `IsSettled`
- Bool 層: `isSettled := decide IsSettled` (noncomputable), `isSettled.iff`
- 基本保存: `IsContact.of_getQuarter_eq`, `IsGroundingEdge.of_getQuarter_eq`,
  `IsGroundingEdge.right_nonempty`, `IsGrounded.nonempty`
- 正規化保存: `IsSettled.normalize`
- 等変性: `IsContact.rotateCW`, `IsGroundingEdge.rotateCW`, `IsGrounded.rotateCW`,
  `IsSettled.rotateCW`; `rotate180` / `rotateCCW` は CW の 1 行系

## サブモジュール（公開）

- `S2IL.Operations.Settled.Defs` — 接地・安定の Prop/Bool 定義層
- `S2IL.Operations.Settled.Equivariance` — CW 等変性と 1 行系
- `S2IL.Operations.Settled.Normalize` — 末尾空レイヤ正規化の保存性

## 単一チェーン原則

CW 等変性のみを直接証明、180° / CCW は 1 行系。
-/

namespace S2IL

end S2IL
