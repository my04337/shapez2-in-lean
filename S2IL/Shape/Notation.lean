-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.Types

/-!
# S2IL.Shape.Notation

シェイプコード文字列表現（`toString` / `ofString?`）と round-trip 定理。

例: `CuCuCuCu:RrRrRrRr` は下層がサークル（アンカラード）、上層がレクタングル（レッド）
の 2 レイヤシェイプを表す。

## 公開 API

- `Quarter.toString` / `Quarter.ofString?`
- `Layer.toString` / `Layer.ofString?`
- `Shape.toString` / `Shape.ofString?`
- 各 round-trip 定理

## Internal

- `S2IL.Shape.Internal.Parse`     — パーサ実装
- `S2IL.Shape.Internal.Serialize` — シリアライザ実装
-/

namespace S2IL

-- ============================================================
-- Quarter
-- ============================================================

axiom Quarter.toString : Quarter → String
axiom Quarter.ofString? : String → Option Quarter

/-- Quarter の round-trip: `ofString? q.toString = some q`。 -/
axiom Quarter.ofString_toString (q : Quarter) :
    Quarter.ofString? (Quarter.toString q) = some q

-- ============================================================
-- Layer
-- ============================================================

axiom Layer.toString : Layer → String
axiom Layer.ofString? : String → Option Layer

/-- Layer の round-trip。 -/
axiom Layer.ofString_toString (l : Layer) :
    Layer.ofString? (Layer.toString l) = some l

-- ============================================================
-- Shape
-- ============================================================

axiom Shape.toString : Shape → String
axiom Shape.ofString? : String → Option Shape

/-- Shape の round-trip（正規化済みに限る）。 -/
axiom Shape.ofString_toString (s : Shape) :
    s.IsNormalized → Shape.ofString? (Shape.toString s) = some s

end S2IL
