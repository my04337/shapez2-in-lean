-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel
import S2IL.Operations.Cutter

/-!
# S2IL.Operations.Swapper

スワップ機 (A-2-1 + B-4-3)。2 つのシェイプの西半分を入れ替える。

## 公開 API

- `Shape.swap : Shape → Shape → Option Shape × Option Shape`
- 180° 回転等変性

## 単一チェーン原則の例外

`swap` は `cut` と同じく絶対方角 E/W に依存するため CW 等変性を持たない。
rotate180 下では E↔W の入れ替えが起こるため、出力タプルの成分も swap される
（Cutter.lean の冒頭コメント参照）。
-/

namespace S2IL

axiom Shape.swap : Shape → Shape → Option Shape × Option Shape

/-- `swap` と 180° 回転: 2 つの入力を独立に 180° 回転しても、
    出力は元の swap 出力タプルの成分を swap してから 180° 回転したものに等しい。 -/
axiom Shape.swap_rotate180_comm (s1 s2 : Shape) :
    s1.rotate180.swap s2.rotate180 =
      ((s1.swap s2).2.map Shape.rotate180, (s1.swap s2).1.map Shape.rotate180)

end S2IL
