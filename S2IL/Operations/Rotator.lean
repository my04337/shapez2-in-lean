-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel
import S2IL.Operations.Common

/-!
# S2IL.Operations.Rotator

回転機 (A-2-2)。`Kernel.Transform` の `Shape.rotateCW` を 1 ターン 1 回の操作として公開する。

## 公開 API

- `rotator : Shape → Shape` — `Shape.rotateCW` の別名

Rotator は Layer A のみの操作（Behavior なし）。CW 等変性は自明。
-/

namespace S2IL.Operations

/-- 回転機の 1 ターン処理（時計回り 90°）。 -/
noncomputable def rotator (s : Shape) : Shape := s.rotateCW

end S2IL.Operations
