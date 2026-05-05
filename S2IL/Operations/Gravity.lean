-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity.Defs
import S2IL.Operations.Gravity.Behavior
import S2IL.Operations.Gravity.Equivariance

/-!
# S2IL.Operations.Gravity

落下機構 (B-1) の facade。
Wave Gravity の定義層、Behavior A/B/C の接地・終端性・不動点定理、等変性定理を集約する。

## 公開 API

- `FloatingPos`
- `floatingMask` / `floatingPositions`
- `Shape.waveStep`
- `Shape.waveGravityCore`
- `Shape.waveGravityCoreFast`
- `Shape.gravity`
- `FloatingPos.rotateCW`
- `Shape.waveStep.rotateCW_comm`
- `Shape.waveGravityCore.rotateCW_comm`
- `IsGrounded.waveStep_static`
- `IsGrounded.waveStep_mono`
- `Shape.waveStep_nonempty_origin`
- `FloatingPos.waveStep_origin`
- `floatingHeight`
- `floatingHeight_waveStep_lt`
- `waveStep_iter_no_floating`
- `IsSettled.floatingPositions_eq_nil`
- `IsSettled.waveStep_fixed`
- `no_floating_iff_isSettled`
- `floatingPositions_eq_nil_iff_isSettled`
- `Shape.waveStep_eq_self_of_no_floating`
- `Shape.waveStep_eq_self_of_floatingPositions_eq_nil`
- `waveGravityCore_eq_self_of_IsSettled`
- `Shape.waveGravityCoreFast_eq_waveGravityCore`
- `waveGravityCore_isSettled`
- `waveGravityCoreFast_isSettled`
- `Shape.gravity.isSettled`
- `Shape.gravity.of_isSettled`
- `Shape.gravity.rotateCW_comm`

## サブモジュール（公開）

- `S2IL.Operations.Gravity.Defs` — Wave Gravity の定義層
- `S2IL.Operations.Gravity.Behavior` — 接地・終端性・不動点性の振る舞い層
- `S2IL.Operations.Gravity.Equivariance` — CW 等変性と 1 行系

## Internal（外部 import 禁止）

- `S2IL.Operations.Gravity.Internal.Shift`
- `S2IL.Operations.Gravity.Internal.Floating`
- `S2IL.Operations.Gravity.Internal.FinsetClosure`
- `S2IL.Operations.Gravity.Internal.GroundingBool`
- `S2IL.Operations.Gravity.Internal.GroundingClosure`

## 実装状況

| 内容 | 状態 |
|---|---|---|
| 反例検証先行 | 完了 |
| Layer A/B 定義群 | Wave 定義実装済み |
| Behavior A: 接地保存・安定 1 tick 不動点 | theorem 化済み |
| Behavior B-1: `waveStep` の由来分解 | theorem 化済み |
| Behavior B-2/B-3: `floatingHeight` と減少補題 | theorem 化済み |
| Behavior B-4: fixed fuel 終端性 | theorem 化済み |
| Behavior B-5: settled bridge | theorem 化済み |
| Behavior B-6: `Shape.gravity.isSettled` | theorem 化済み |
| Behavior C: normalize 不動点 | theorem 化済み |
| Equivariance-2: `FloatingPos.rotateCW` / `down_rotateCW` | theorem 化済み |
| Equivariance-3: `waveStep.rotateCW_comm` / `waveGravityCore.rotateCW_comm` | theorem 化済み |
| Equivariance-4: `Shape.gravity.rotateCW_comm` | theorem 化済み |

## 単一チェーン原則

CW 等変性のみを主証明とし、180° / CCW は 1 行系。
-/
