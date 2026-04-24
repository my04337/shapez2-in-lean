-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape
import S2IL.Kernel
import S2IL.Wires
import S2IL.Operations
import S2IL.Machine

/-!
# S2IL ルート facade

Layer A/B Greenfield Rewrite の Phase A: 空 facade。
各サブ facade を再エクスポートする唯一の入口。

## サブモジュール（公開）

- `S2IL.Shape`        — Shape 型系
- `S2IL.Kernel`       — 共通理論（BFS / Bond / Transform）
- `S2IL.Wires`        — ワイヤー系（スケルトン）
- `S2IL.Operations`   — 加工操作（Layer A 純粋部 + Layer B 振る舞い）
- `S2IL.Machine`      — Machine 統合層

Phase A 時点ではいずれも空 namespace のみ。Phase B で axiom による公開 API scaffold を追加予定。
詳細: `docs/plans/layer-ab-rewrite-plan.md`
-/
