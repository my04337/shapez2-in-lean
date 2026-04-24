-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

/-!
# S2IL.Shape.Types

Shape 型系の公開型定義（Phase B scaffold）。
すべての型は `axiom` で opaque に宣言する。Phase C で具体実装に置換する。

## 公開型

- `Color` — 象限のカラーコード
- `PartCode` / `RegularPartCode` — パーツコード
- `Direction` — 方角（NE / SE / SW / NW）
- `Quarter` — 象限（空・ピン・結晶・通常パーツ）
- `Layer` — 4 象限の組
- `Shape` — 1 枚以上のレイヤの積み重ね
- `QuarterPos` — 象限の絶対位置

## Internal

Phase C 着手まで Internal なし。
-/

namespace S2IL

/-- 象限の色情報を示すカラーコード。 -/
axiom Color : Type

namespace Color
axiom uncolored : Color
axiom red : Color
axiom green : Color
axiom blue : Color
axiom yellow : Color
axiom magenta : Color
axiom cyan : Color
axiom white : Color
axiom all : List Color
axiom toChar : Color → Char
axiom ofChar? : Char → Option Color
axiom mix : Color → Color → Color
axiom decEq : DecidableEq Color
end Color

/-- パーツコード。 -/
axiom PartCode : Type

namespace PartCode
axiom circle : PartCode
axiom rectangle : PartCode
axiom star : PartCode
axiom windmill : PartCode
axiom pin : PartCode
axiom crystal : PartCode
axiom all : List PartCode
axiom toChar : PartCode → Char
axiom ofChar? : Char → Option PartCode
axiom decEq : DecidableEq PartCode
end PartCode

/-- 通常パーツ（ピン・結晶を除く）。 -/
axiom RegularPartCode : Type

namespace RegularPartCode
axiom all : List RegularPartCode
axiom toChar : RegularPartCode → Char
axiom ofChar? : Char → Option RegularPartCode
axiom toPartCode : RegularPartCode → PartCode
axiom ofPartCode? : PartCode → Option RegularPartCode
end RegularPartCode

/-- 方角（North-East / South-East / South-West / North-West）。 -/
axiom Direction : Type

namespace Direction
axiom ne : Direction
axiom se : Direction
axiom sw : Direction
axiom nw : Direction
axiom all : List Direction
axiom rotateCW : Direction → Direction
axiom isEast : Direction → Bool
axiom isWest : Direction → Bool
axiom adjacent : Direction → Direction → Bool
axiom toFin : Direction → Fin 4
axiom decEq : DecidableEq Direction
end Direction

/-- 象限。 -/
axiom Quarter : Type

namespace Quarter
axiom empty : Quarter
axiom pin : Quarter
axiom crystal : Color → Quarter
axiom colored : RegularPartCode → Color → Quarter
axiom isEmpty : Quarter → Bool
axiom canFormBond : Quarter → Bool
axiom isFragile : Quarter → Bool
axiom partCode? : Quarter → Option PartCode
axiom color? : Quarter → Option Color
axiom decEq : DecidableEq Quarter
end Quarter

/-- 4 象限の組（1 枚のレイヤ）。 -/
axiom Layer : Type

namespace Layer
axiom mk : (ne se sw nw : Quarter) → Layer
axiom empty : Layer
axiom isEmpty : Layer → Bool
axiom rotateCW : Layer → Layer
axiom decEq : DecidableEq Layer
end Layer

/-- シェイプ（1 枚以上のレイヤを下から順に積み重ねた構造）。 -/
axiom Shape : Type

namespace Shape
axiom layers : Shape → List Layer
axiom ofLayers : List Layer → Option Shape
axiom single : Layer → Shape
axiom double : Layer → Layer → Shape
axiom triple : Layer → Layer → Layer → Shape
axiom quadruple : Layer → Layer → Layer → Layer → Shape
axiom layerCount : Shape → Nat
axiom bottomLayer : Shape → Layer
axiom topLayer : Shape → Layer
axiom mapLayers : Shape → (Layer → Layer) → Shape
axiom IsNormalized : Shape → Prop
axiom normalize : Shape → Option Shape
axiom decEq : DecidableEq Shape
end Shape

/-- 象限の絶対位置（レイヤ番号 + 方角）。 -/
axiom QuarterPos : Type

namespace QuarterPos
axiom mk : (layer : Nat) → (dir : Direction) → QuarterPos
axiom layer : QuarterPos → Nat
axiom dir : QuarterPos → Direction
axiom getDir : Layer → Direction → Quarter
axiom setDir : Layer → Direction → Quarter → Layer
axiom getQuarter : Shape → QuarterPos → Option Quarter
axiom setQuarter : Shape → QuarterPos → Quarter → Shape
axiom isValid : Shape → QuarterPos → Bool
axiom allValid : Shape → List QuarterPos
axiom rotateCW : QuarterPos → QuarterPos
axiom decEq : DecidableEq QuarterPos
end QuarterPos

/-- シェイプの指定位置リストを空象限に置換する。 -/
axiom Shape.clearPositions : Shape → List QuarterPos → Shape

end S2IL
