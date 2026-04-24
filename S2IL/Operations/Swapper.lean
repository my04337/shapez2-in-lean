-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel
import S2IL.Operations.Cutter

/-!
# S2IL.Operations.Swapper

スワップ機 (A-2-1 + B-4-3)（Phase C re-scaffold 済み）。
`swap` は `eastHalf` + `westHalf` + `combineHalves` の `def` 合成（§8.1.4）。

## 公開 API

- `Shape.swap : Shape → Shape → Shape × Shape`（全関数）
- 180° 回転等変性（theorem、primitive の系）
-/

namespace S2IL

/-- スワップ: 2 つのシェイプの西半分を入れ替える（全関数）。 -/
noncomputable def Shape.swap (s1 s2 : Shape) : Shape × Shape :=
  (Shape.combineHalves (Shape.eastHalf s1) (Shape.westHalf s2),
   Shape.combineHalves (Shape.eastHalf s2) (Shape.westHalf s1))

/-- `swap` と 180° 回転（theorem、eastHalf/westHalf の系）。 -/
theorem Shape.swap.rotate180_comm (s1 s2 : Shape) :
    Shape.swap s1.rotate180 s2.rotate180 =
      ((Shape.swap s1 s2).2.rotate180, (Shape.swap s1 s2).1.rotate180) := by
  sorry -- Phase C/D で証明。combineHalves_rotate180 axiom が必要

end S2IL
