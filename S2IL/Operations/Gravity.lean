-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel
import S2IL.Operations.Settled
import S2IL.Operations.Gravity.Defs
import S2IL.Operations.Gravity.Internal.ShareDirection

/-!
# S2IL.Operations.Gravity

落下機構 (B-1)（Phase D-10B 進行中: Layer A 部 `def` 化済み）。
全関数版: `gravity : Shape → Shape`（architecture §1.9 Option 追放原則）。

## 公開 API

- `Shape.gravity : Shape → Shape` — 計算可能な実装（`Defs.lean`）
- `Shape.gravity.isSettled` — 出力は常に `IsSettled`（D-10D で theorem 化予定）
- `Shape.gravity.of_isSettled` — 安定入力に対する不動点性（D-10C で theorem 化予定）
- `Shape.gravity.rotateCW_comm` — CW 等変性（D-10E で theorem 化予定）

## Phase 状況

| Phase | 内容 | 状態 |
|---|---|---|
| D-10A | 反例検証先行 | ✅ 完了 |
| D-10B | Layer A 定義群 | 🔧 本ファイル |
| D-10C | 不動点・終端性 | ⏳ |
| D-10D | 安定性主定理 | ⏳ |
| D-10E | 等変性主定理 | ⏳ |

## 単一チェーン原則

CW 等変性のみ axiom（一時）、180° / CCW は 1 行系。
-/

namespace S2IL

/-- `gravity` の出力は常に `IsSettled`。Phase D-10D で theorem 化。 -/
axiom Shape.gravity.isSettled (s : Shape) : IsSettled (Shape.gravity s)

/-- 安定入力に対する不動点性。Phase D-10C で theorem 化。 -/
axiom Shape.gravity.of_isSettled {s : Shape} :
    IsSettled s → Shape.gravity s = s

/-- `gravity` と CW 回転は可換。Phase D-10E で theorem 化。 -/
axiom Shape.gravity.rotateCW_comm (s : Shape) :
    Shape.rotateCW (Shape.gravity s) = Shape.gravity (Shape.rotateCW s)

/-- `gravity` と 180° 回転は可換（CW の系）。 -/
theorem Shape.gravity.rotate180_comm (s : Shape) :
    (Shape.gravity s).rotate180 = Shape.gravity s.rotate180 := by
  simp [Shape.rotate180_eq_rotateCW_rotateCW, Shape.gravity.rotateCW_comm]

/-- `gravity` と CCW 回転は可換（CW の系）。 -/
theorem Shape.gravity.rotateCCW_comm (s : Shape) :
    (Shape.gravity s).rotateCCW = Shape.gravity s.rotateCCW := by
  simp [Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW, Shape.gravity.rotateCW_comm]

end S2IL
