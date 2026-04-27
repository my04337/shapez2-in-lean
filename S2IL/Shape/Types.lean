-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.Types.Atom

/-!
# S2IL.Shape.Types

Shape 型系の公開型定義（Phase C 完了形）。

| 型 | 定義 | 備考 |
|---|---|---|
| `Color` / `PartCode` / `RegularPartCode` | (Atom.lean) | inductive |
| `Direction`        | `abbrev := Fin 4`                   | NE=0 / SE=1 / SW=2 / NW=3 |
| `Quarter`          | `inductive` (empty/pin/crystal/colored) | 着色は `RegularPartCode × Color` |
| `Layer`            | `abbrev := Fin 4 → Quarter`         | 関数型 |
| `Shape`            | `abbrev := List Layer`              | 0 層許容（§1.9） |
| `QuarterPos`       | `abbrev := Nat × Fin 4`             | レイヤ番号 × 方角 |

`toString` / `ofString?` は `S2IL.Shape.Notation` に分離。
-/

namespace S2IL

-- ============================================================
-- Direction := Fin 4
-- ============================================================

/-- 方角。NE=0, SE=1, SW=2, NW=3。回転は `+1 (mod 4)`。 -/
abbrev Direction := Fin 4

namespace Direction

def ne : Direction := 0
def se : Direction := 1
def sw : Direction := 2
def nw : Direction := 3

def all : List Direction := [0, 1, 2, 3]

/-- 時計回り 90° 回転 = +1 (mod 4)。 -/
def rotateCW (d : Direction) : Direction := d + 1

/-- 方角が東半分（NE / SE）か。 -/
def isEast (d : Direction) : Bool := d.val < 2

/-- 方角が西半分（SW / NW）か。 -/
def isWest (d : Direction) : Bool := 2 ≤ d.val

/-- 同レイヤ内での隣接判定（円環上 ±1）。 -/
def isAdjacent (d1 d2 : Direction) : Bool :=
  d1 - d2 = 1 || d2 - d1 = 1

/-- 隣接判定の対称性。 -/
theorem isAdjacent_symm (d1 d2 : Direction) :
    isAdjacent d1 d2 = isAdjacent d2 d1 := by
  simp only [isAdjacent, Bool.or_comm]

end Direction

-- ============================================================
-- Quarter
-- ============================================================

/-- 1 象限の状態。空 / ピン / 結晶 / 着色通常パーツ。 -/
inductive Quarter where
  /-- 空の象限（シェイプが存在しない）。 -/
  | empty
  /-- ピン（色を持たない支持パーツ）。 -/
  | pin
  /-- 結晶（脆弱、色を持つ）。 -/
  | crystal (color : Color)
  /-- 着色通常パーツ。 -/
  | colored (part : RegularPartCode) (color : Color)
  deriving Repr, DecidableEq, BEq

namespace Quarter

/-- 象限が空か。 -/
def isEmpty : Quarter → Bool
  | empty => true
  | _     => false

/-- 象限が結合能力を持つ（空とピン以外）。 -/
def canFormBond : Quarter → Bool
  | empty | pin => false
  | _           => true

/-- 結晶のみが脆弱（Fragile）。 -/
def isFragile : Quarter → Bool
  | crystal _ => true
  | _         => false

/-- 結晶判定（Bool）。 -/
def isCrystal : Quarter → Bool
  | crystal _ => true
  | _         => false

/-- 結晶判定（Prop）。`isCrystal` の Prop 層（§1.11 規約）。 -/
def IsCrystal (q : Quarter) : Prop := q.isCrystal = true

instance : DecidablePred IsCrystal := fun q =>
  inferInstanceAs (Decidable (q.isCrystal = true))

@[simp] theorem isCrystal_crystal (c : Color) : isCrystal (crystal c) = true := rfl
@[simp] theorem isCrystal_empty : isCrystal empty = false := rfl
@[simp] theorem isCrystal_pin : isCrystal pin = false := rfl
@[simp] theorem isCrystal_colored (p : RegularPartCode) (c : Color) :
    isCrystal (colored p c) = false := rfl

/-- 象限のパーツコード（空は `none`）。 -/
def partCode? : Quarter → Option PartCode
  | empty       => none
  | pin         => some .pin
  | crystal _   => some .crystal
  | colored p _ => some p.toPartCode

/-- 象限の色（空・ピンは `none`）。 -/
def color? : Quarter → Option Color
  | crystal c   => some c
  | colored _ c => some c
  | _           => none

end Quarter

-- ============================================================
-- Layer := Fin 4 → Quarter
-- ============================================================

/-- 4 象限の組（1 レイヤ）。`Direction` で関数アクセスする。 -/
abbrev Layer := Fin 4 → Quarter

namespace Layer

/-- 4 方角を指定してレイヤを構成。 -/
def mk (ne se sw nw : Quarter) : Layer := fun d =>
  match d.val with
  | 0 => ne
  | 1 => se
  | 2 => sw
  | _ => nw

@[simp] theorem mk_apply_zero (ne se sw nw : Quarter) : mk ne se sw nw 0 = ne := rfl
@[simp] theorem mk_apply_one  (ne se sw nw : Quarter) : mk ne se sw nw 1 = se := rfl
@[simp] theorem mk_apply_two  (ne se sw nw : Quarter) : mk ne se sw nw 2 = sw := rfl
@[simp] theorem mk_apply_three (ne se sw nw : Quarter) : mk ne se sw nw 3 = nw := rfl

/-- レイヤを 4 象限への分解として復元する。 -/
@[simp] theorem mk_eta (l : Layer) : mk (l 0) (l 1) (l 2) (l 3) = l := by
  funext ⟨d, hd⟩
  match d, hd with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

/-- 全象限が空のレイヤ。 -/
def empty : Layer := fun _ => Quarter.empty

/-- 全象限が空か。 -/
def isEmpty (l : Layer) : Bool :=
  (l 0).isEmpty && (l 1).isEmpty && (l 2).isEmpty && (l 3).isEmpty

/-- 時計回り 90° 回転（index を -1 シフト）。 -/
def rotateCW (l : Layer) : Layer := fun d => l (d - 1)

/-- 指定方角の象限を取得。 -/
def getDir (l : Layer) (d : Direction) : Quarter := l d

/-- 指定方角の象限を設定。 -/
def setDir (l : Layer) (d : Direction) (q : Quarter) : Layer :=
  fun d' => if d' = d then q else l d'

end Layer

-- ============================================================
-- Shape := List Layer
-- ============================================================

/-- シェイプ。0 枚以上のレイヤを下から積み重ねた構造（`List Layer`）。 -/
abbrev Shape := List Layer

namespace Shape

/-- 0 層シェイプ（空）。 -/
def empty : Shape := []

/-- 識別関数（旧 API 互換）。 -/
def layers (s : Shape) : List Layer := s

/-- レイヤ数。 -/
def layerCount (s : Shape) : Nat := s.length

def single     (l1 : Layer)                 : Shape := [l1]
def double     (l1 l2 : Layer)              : Shape := [l1, l2]
def triple     (l1 l2 l3 : Layer)           : Shape := [l1, l2, l3]
def quadruple  (l1 l2 l3 l4 : Layer)        : Shape := [l1, l2, l3, l4]

/-- 最下層レイヤ（0 層なら空レイヤ）。 -/
def bottomLayer (s : Shape) : Layer :=
  s.head?.getD Layer.empty

/-- 最上層レイヤ（0 層なら空レイヤ）。 -/
def topLayer (s : Shape) : Layer :=
  s.getLast?.getD Layer.empty

/-- 各レイヤに関数を適用。 -/
def mapLayers (s : Shape) (f : Layer → Layer) : Shape := s.map f

-- ----------------------
-- 正規化（§1.11 規約）
-- ----------------------

/-- 末尾から連続する空レイヤを除去する補助関数。
    `reverse + dropWhile + reverse` で簡潔に実装する。 -/
def dropTrailingEmpty (s : List Layer) : List Layer :=
  (s.reverse.dropWhile Layer.isEmpty).reverse

/-- シェイプが正規化されている（末尾が空レイヤでない）ことを表す述語。
    0 層シェイプは正規化済みとみなす。 -/
def IsNormalized (s : Shape) : Prop :=
  s.getLast?.all (fun l => !l.isEmpty) = true

instance instDecidableIsNormalized : DecidablePred IsNormalized := fun _ =>
  inferInstanceAs (Decidable (_ = _))

/-- 末尾の空レイヤをストリップして正規化する。0 層なら 0 層を返す。 -/
def normalize (s : Shape) : Shape := dropTrailingEmpty s

end Shape

-- ============================================================
-- QuarterPos := Nat × Fin 4
-- ============================================================

/-- 象限の絶対位置（レイヤ番号 × 方角）。 -/
abbrev QuarterPos := Nat × Fin 4

namespace QuarterPos

def mk (layer : Nat) (dir : Direction) : QuarterPos := (layer, dir)
def layer (pos : QuarterPos) : Nat := pos.1
def dir   (pos : QuarterPos) : Direction := pos.2

/-- 指定位置の象限を取得（範囲外は空）。 -/
def getQuarter (s : Shape) (pos : QuarterPos) : Quarter :=
  if h : pos.1 < s.length then s[pos.1] pos.2 else Quarter.empty

/-- 指定位置の象限を設定。範囲外は変更しない。 -/
def setQuarter (s : Shape) (pos : QuarterPos) (q : Quarter) : Shape :=
  if h : pos.1 < s.length then
    s.set pos.1 ((s[pos.1]'h).setDir pos.2 q)
  else s

/-- 位置がシェイプ範囲内か。 -/
def isValid (s : Shape) (pos : QuarterPos) : Bool := decide (pos.1 < s.length)

/-- シェイプの全有効位置を列挙する（レイヤ昇順 × 4 方角）。 -/
def allValid (s : Shape) : List QuarterPos :=
  (List.range s.length).flatMap (fun n => Direction.all.map (fun d => (n, d)))

/-- 時計回り 90° 回転: 方角を +1。 -/
def rotateCW (pos : QuarterPos) : QuarterPos := (pos.1, pos.2 + 1)

/-- 反時計回り 90° 回転: 方角を -1。 -/
def rotateCCW (pos : QuarterPos) : QuarterPos := (pos.1, pos.2 - 1)

end QuarterPos

namespace Shape

/-- 指定位置リストを空象限に置換する。 -/
def clearPositions (s : Shape) (positions : List QuarterPos) : Shape :=
  positions.foldl (fun acc p => QuarterPos.setQuarter acc p Quarter.empty) s

end Shape

end S2IL
