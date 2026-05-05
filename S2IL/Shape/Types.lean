-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.Types.Atom
import S2IL.Shape.Types.Direction
import S2IL.Shape.Types.Quarter
import S2IL.Shape.Types.Layer
import S2IL.Shape.Types.Shape
import S2IL.Shape.Types.QuarterPos

/-!
# S2IL.Shape.Types

Shape 型系の公開型定義 facade。

| 型 | 定義 | 実装 |
|---|---|---|
| `Color` / `PartCode` / `RegularPartCode` | inductive | `S2IL.Shape.Types.Atom` |
| `Direction`        | `abbrev := Fin 4`                   | `S2IL.Shape.Types.Direction` |
| `Quarter`          | `inductive` (empty/pin/crystal/colored) | `S2IL.Shape.Types.Quarter` |
| `Layer`            | `abbrev := Fin 4 → Quarter`         | `S2IL.Shape.Types.Layer` |
| `Shape`            | `abbrev := List Layer`              | `S2IL.Shape.Types.Shape` |
| `QuarterPos`       | `abbrev := Nat × Fin 4`             | `S2IL.Shape.Types.QuarterPos` |

`toString` / `ofString?` は `S2IL.Shape.Notation` に分離。
-/

namespace S2IL

end S2IL