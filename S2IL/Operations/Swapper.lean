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

/-- スワップ: 2 つのシェイプの西半分を入れ替える（全関数）。

    出力タプル `(out1, out2)`:
    - `out1 = combineHalves (eastHalf s1) (westHalf s2)` — `s1` の東半分 + `s2` の西半分
    - `out2 = combineHalves (eastHalf s2) (westHalf s1)` — `s2` の東半分 + `s1` の西半分

    `Shape.combineHalves` は `List.zipWith` 実装のため、出力長は両入力の短い方に揃う。 -/
def Shape.swap (s1 s2 : Shape) : Shape × Shape :=
  (Shape.combineHalves (Shape.eastHalf s1) (Shape.westHalf s2),
   Shape.combineHalves (Shape.eastHalf s2) (Shape.westHalf s1))

/-- `swap` と 180° 回転（theorem、`combineHalves` / `eastHalf` / `westHalf` の系）。

    180° 回転下では E↔W が swap されるため、出力タプルの成分も swap される:
    - `eastHalf s.rotate180 = (westHalf s).rotate180`
    - `westHalf s.rotate180 = (eastHalf s).rotate180`
    - `(combineHalves a b).rotate180 = combineHalves b.rotate180 a.rotate180` -/
theorem Shape.swap.rotate180_comm (s1 s2 : Shape) :
    Shape.swap s1.rotate180 s2.rotate180 =
      ((Shape.swap s1 s2).2.rotate180, (Shape.swap s1 s2).1.rotate180) := by
  simp only [Shape.swap,
    Shape.eastHalf.rotate180_comm, Shape.westHalf.rotate180_comm,
    Shape.combineHalves.rotate180_comm]

end S2IL
