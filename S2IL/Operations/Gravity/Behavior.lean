-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity.Behavior.SettledCore

/-!
# S2IL.Operations.Gravity.Behavior

Wave Gravity の振る舞い層 facade。

## 公開 API

- `IsGroundingEdge.waveStep_of_static`
- `IsGrounded.not_floating`
- `IsGrounded.grounding_path_avoids_floating`
- `IsGrounded.waveStep_static`
- `IsGrounded.waveStep_mono`
- `Shape.waveStep_nonempty_origin`
- `FloatingPos.waveStep_origin`
- `floatingHeight_waveStep_lt`
- `waveStep_iter_no_floating`
- `IsSettled.floatingPositions_eq_nil`
- `IsSettled.waveStep_fixed`
- `no_floating_iff_isSettled`
- `Shape.waveStep_eq_self_of_no_floating`
- `floatingPositions_eq_nil_iff_isSettled`
- `waveGravityCore_eq_self_of_IsSettled`
- `waveGravityCore_isSettled`
- `Shape.gravity.isSettled`
- `Shape.gravity.of_isSettled`

## サブモジュール（公開）

- `S2IL.Operations.Gravity.Behavior.Grounded` — 接地保存
- `S2IL.Operations.Gravity.Behavior.Origin` — `waveStep` 後の由来分解
- `S2IL.Operations.Gravity.Behavior.FloatingHeight` — height 減少と fixed fuel 終端性
- `S2IL.Operations.Gravity.Behavior.SettledCore` — no-floating / settled bridge と gravity 安定性

## 実装状況

Behavior A/B/C は theorem 化済み。
-/

namespace S2IL

end S2IL
