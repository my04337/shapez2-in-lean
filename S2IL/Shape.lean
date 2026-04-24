-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

/-!
# S2IL.Shape facade

Shape 型系（Layer A-1）の公開 API 集約点。

## 公開 API

Phase A 時点では空。Phase B で axiom scaffold を追加予定。

## サブモジュール（公開）

- `S2IL.Shape.Types`       — Color / PartCode / Quarter / QuarterPos / Layer / Shape
- `S2IL.Shape.GameConfig`  — ゲーム設定
- `S2IL.Shape.Arbitrary`   — Plausible インスタンス
- `S2IL.Shape.Notation`    — Shape Code parse/serialize + round-trip 定理

## Internal（外部 import 禁止）

- `S2IL.Shape.Internal.*`
-/

namespace S2IL.Shape
end S2IL.Shape
