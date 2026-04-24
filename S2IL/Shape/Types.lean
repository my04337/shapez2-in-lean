-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

/-!
# S2IL.Shape.Types

Shape 型系の公開型定義。Phase C re-scaffold 済み。
主要型は Lean 標準型で具体化されている（architecture-layer-ab.md §1.8）。

## 公開型

- `Color` — 象限のカラーコード（`axiom`; Phase C で `inductive` に置換予定）
- `PartCode` / `RegularPartCode` — パーツコード（同上）
- `Direction := Fin 4` — 方角（NE=0 / SE=1 / SW=2 / NW=3）
- `Quarter` — 象限（`axiom`; Phase C で `inductive` に置換予定）
- `Layer := Fin 4 → Quarter` — 4 象限の組
- `Shape := List Layer` — 0 枚以上のレイヤの積み重ね（0 層 = 空シェイプ）
- `QuarterPos := Nat × Fin 4` — 象限の絶対位置

## 具象型の設計根拠

- `Direction := Fin 4`: 回転は `+1 (mod 4)`。4 周性は `omega` で即閉じ。
- `Layer := Fin 4 → Quarter`: 象限アクセスは `l d`。回転は index shift。
- `Shape := List Layer`: 0 層許容により全操作から `Option Shape` を追放。
- `QuarterPos := Nat × Fin 4`: レイヤ番号 × 方角。

## Internal

Phase C 着手まで Internal なし。
-/

namespace S2IL

-- ============================================================
-- Color（Phase C で inductive に置換予定）
-- ============================================================

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

-- ============================================================
-- PartCode / RegularPartCode（Phase C で inductive に置換予定）
-- ============================================================

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

-- ============================================================
-- Direction := Fin 4（具象型）
-- ============================================================

/-- 方角。NE=0, SE=1, SW=2, NW=3 の巡回順で `Fin 4` に埋め込む。
    回転は `+1 (mod 4)` で表現される。 -/
abbrev Direction := Fin 4

namespace Direction
def ne : Direction := 0
def se : Direction := 1
def sw : Direction := 2
def nw : Direction := 3

def all : List Direction := [0, 1, 2, 3]

/-- 時計回り 90° 回転 = +1 (mod 4)。 -/
def rotateCW (d : Direction) : Direction := d + 1

/-- 方角が東側（NE=0, SE=1）か判定。 -/
def isEast (d : Direction) : Bool := d.val < 2

/-- 方角が西側（SW=2, NW=3）か判定。 -/
def isWest (d : Direction) : Bool := 2 ≤ d.val

/-- 同レイヤ内隣接: 円環上で ±1 の位置。 -/
def isAdjacent (d1 d2 : Direction) : Bool :=
  d1 - d2 = 1 || d2 - d1 = 1

end Direction

-- ============================================================
-- Quarter（Phase C で inductive に置換予定）
-- ============================================================

/-- 象限。 -/
axiom Quarter : Type

namespace Quarter
axiom empty : Quarter
axiom pin : Quarter
axiom crystal : Color → Quarter
axiom colored : RegularPartCode → Color → Quarter
axiom isEmpty : Quarter → Bool
axiom isBondable : Quarter → Bool
axiom isFragile : Quarter → Bool
axiom partCode? : Quarter → Option PartCode
axiom color? : Quarter → Option Color
axiom decEq : DecidableEq Quarter
end Quarter

-- ============================================================
-- Layer := Fin 4 → Quarter（具象型）
-- ============================================================

/-- 4 象限の組（1 枚のレイヤ）。`Fin 4 → Quarter` として Direction で直接アクセス。 -/
abbrev Layer := Fin 4 → Quarter

namespace Layer

/-- 4 方角を指定してレイヤを構成する。 -/
def mk (ne se sw nw : Quarter) : Layer := fun d =>
  if d = 0 then ne else if d = 1 then se else if d = 2 then sw else nw

/-- 空レイヤ（全象限が空）。 -/
noncomputable def empty : Layer := fun _ => Quarter.empty

/-- レイヤが空か判定。 -/
noncomputable def isEmpty (l : Layer) : Bool :=
  (Quarter.isEmpty (l 0)) && (Quarter.isEmpty (l 1)) &&
  (Quarter.isEmpty (l 2)) && (Quarter.isEmpty (l 3))

/-- 時計回り 90° 回転。index を -1 シフトする。 -/
def rotateCW (l : Layer) : Layer := fun d => l (d - 1)

/-- レイヤから指定方角の象限を取得。 -/
def getDir (l : Layer) (d : Direction) : Quarter := l d

/-- レイヤの指定方角の象限を設定。 -/
def setDir (l : Layer) (d : Direction) (q : Quarter) : Layer :=
  fun d' => if d' = d then q else l d'

end Layer

-- ============================================================
-- Shape := List Layer（具象型、0 層許容）
-- ============================================================

/-- シェイプ。0 枚以上のレイヤを下から順に積み重ねた構造。
    0 層シェイプ（`[]`）を許容し、全操作を全関数化する
    （architecture-layer-ab.md §1.9）。 -/
abbrev Shape := List Layer

namespace Shape

/-- 空シェイプ（0 層）。 -/
def empty : Shape := []

/-- レイヤのリストをそのまま返す（`Shape = List Layer` なので恒等）。 -/
def layers (s : Shape) : List Layer := s

/-- レイヤ数。 -/
def layerCount (s : Shape) : Nat := s.length

/-- 1 レイヤのシェイプを構成。 -/
def single (l : Layer) : Shape := [l]

/-- 2 レイヤのシェイプを構成。 -/
def double (l1 l2 : Layer) : Shape := [l1, l2]

/-- 3 レイヤのシェイプを構成。 -/
def triple (l1 l2 l3 : Layer) : Shape := [l1, l2, l3]

/-- 4 レイヤのシェイプを構成。 -/
def quadruple (l1 l2 l3 l4 : Layer) : Shape := [l1, l2, l3, l4]

/-- 最下層（0 層シェイプの場合は空レイヤ）。 -/
noncomputable def bottomLayer (s : Shape) : Layer :=
  s.head?.getD Layer.empty

/-- 最上層（0 層シェイプの場合は空レイヤ）。 -/
noncomputable def topLayer (s : Shape) : Layer :=
  s.getLast?.getD Layer.empty

/-- 各レイヤに関数を適用。 -/
def mapLayers (s : Shape) (f : Layer → Layer) : Shape := s.map f

/-- 正規化されたシェイプか（Prop 層; §1.11 規約）。 -/
axiom IsNormalized : Shape → Prop

/-- `IsNormalized` の決定可能性。 -/
axiom instDecidableIsNormalized : DecidablePred IsNormalized
noncomputable instance : DecidablePred IsNormalized := instDecidableIsNormalized

/-- 正規化（全関数; §1.9 規約）。 -/
axiom normalize : Shape → Shape

end Shape

-- ============================================================
-- QuarterPos := Nat × Fin 4（具象型）
-- ============================================================

/-- 象限の絶対位置（レイヤ番号 × 方角）。 -/
abbrev QuarterPos := Nat × Fin 4

namespace QuarterPos

/-- コンストラクタ。 -/
def mk (layer : Nat) (dir : Direction) : QuarterPos := (layer, dir)

/-- レイヤ番号。 -/
def layer (pos : QuarterPos) : Nat := pos.1

/-- 方角。 -/
def dir (pos : QuarterPos) : Direction := pos.2

/-- シェイプの指定位置の象限を取得（範囲外は空）。 -/
noncomputable def getQuarter (s : Shape) (pos : QuarterPos) : Quarter :=
  if h : pos.1 < s.length then s[pos.1] pos.2 else Quarter.empty

/-- シェイプの指定位置の象限を設定。 -/
axiom setQuarter : Shape → QuarterPos → Quarter → Shape

/-- 位置が有効か判定。 -/
def isValid (s : Shape) (pos : QuarterPos) : Bool := decide (pos.1 < s.length)

/-- シェイプの全有効位置を列挙。 -/
axiom allValid : Shape → List QuarterPos

/-- 時計回り 90° 回転: レイヤ番号は保持、方角を +1。 -/
def rotateCW (pos : QuarterPos) : QuarterPos := (pos.1, pos.2 + 1)

end QuarterPos

/-- シェイプの指定位置リストを空象限に置換する。 -/
axiom Shape.clearPositions : Shape → List QuarterPos → Shape

end S2IL
