-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

/-!
# S2IL.Operations facade

全加工操作 (Layer A-2 純粋部 + Layer B 振る舞い系) の統合入口。
Layer C からは本 facade のみを参照すればよい。

## 公開 API

Phase A 時点では空。Phase B で axiom scaffold を追加予定。

## サブモジュール（公開）

- `S2IL.Operations.Common`            — 操作共通ユーティリティ
- `S2IL.Operations.HalfDestroyer`     — A-2-1
- `S2IL.Operations.Cutter`            — A-2-1 + B-4-2
- `S2IL.Operations.Swapper`           — A-2-1 + B-4-3
- `S2IL.Operations.Rotator`           — A-2-2
- `S2IL.Operations.Painter`           — A-2-3
- `S2IL.Operations.ColorMixer`        — A-2-3
- `S2IL.Operations.CrystalGenerator`  — A-2-6
- `S2IL.Operations.Stacker`           — A-2-4 + B-4-1
- `S2IL.Operations.PinPusher`         — A-2-5 + B-4-4
- `S2IL.Operations.Gravity`           — B-1
- `S2IL.Operations.Shatter`           — B-2
- `S2IL.Operations.Settled`           — B-3

## Internal（外部 import 禁止）

各 `S2IL.Operations.<Op>.Internal.*`
-/

namespace S2IL.Operations
end S2IL.Operations
