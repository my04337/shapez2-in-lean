-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.Shape

/-!
# QuarterPos (象限位置)

シェイプ内の象限の絶対位置を表す型。
レイヤインデックスと方角の組で構成される。

## Direction (方角)

レイヤ内の4象限の方角。

| バリアント | 方角 | 位置 |
|---|---|---|
| `ne` | Northeast | 右上 |
| `se` | Southeast | 右下 |
| `sw` | Southwest | 左下 |
| `nw` | Northwest | 左上 |

### 同レイヤ内の隣接関係

4象限を円環状に並べた隣り合いとして定義される:

```
    NW ── NE
    │      │
    SW ── SE
```

隣接ペア: NE↔SE, SE↔SW, SW↔NW, NW↔NE

### 東西の半分

| 半分 | 含まれる方角 |
|---|---|
| East Half (東側の半分) | `ne`, `se` |
| West Half (西側の半分) | `sw`, `nw` |

## LayerIndex (レイヤインデックス)

シェイプ内のレイヤ位置。`l1` が最下層、`l4` が最上層。
上下に隣接するレイヤ間で結晶の結合が発生しうる。

## QuarterPos (象限位置)

`LayerIndex` と `Direction` の組でシェイプ内の象限の絶対位置を表す。
-/

-- ============================================================
-- Direction (方角)
-- ============================================================

/-- レイヤ内の4象限の方角 -/
inductive Direction where
    | ne | se | sw | nw
    deriving Repr, DecidableEq, BEq

namespace Direction

/-- 同レイヤ内で方角が隣接しているかを判定する（円環状の4ペア） -/
def adjacent : Direction → Direction → Bool
    | ne, se | se, ne => true
    | se, sw | sw, se => true
    | sw, nw | nw, sw => true
    | nw, ne | ne, nw => true
    | _, _             => false

/-- 方角が東側の半分 (East Half) に属するかを判定する -/
def isEast : Direction → Bool
    | ne | se => true
    | sw | nw => false

/-- 方角が西側の半分 (West Half) に属するかを判定する -/
def isWest : Direction → Bool
    | ne | se => false
    | sw | nw => true

/-- 全ての方角のリスト -/
def all : List Direction := [ne, se, sw, nw]

/-- 方角を 180° 回転させる (NE↔SW, SE↔NW) -/
def rotate180 : Direction → Direction
    | ne => sw
    | se => nw
    | sw => ne
    | nw => se

-- ============================================================
-- Direction の定理
-- ============================================================

/-- 隣接関係は対称的である -/
theorem adjacent_symm (d1 d2 : Direction) : d1.adjacent d2 = d2.adjacent d1 := by
    cases d1 <;> cases d2 <;> rfl

/-- 隣接関係は反射的でない -/
theorem not_adjacent_self (d : Direction) : d.adjacent d = false := by
    cases d <;> rfl

/-- 東側でなければ西側である -/
theorem isWest_eq_not_isEast (d : Direction) : d.isWest = !d.isEast := by
    cases d <;> rfl

/-- 180° 回転は対合である (2 回適用で元に戻る) -/
@[simp] theorem rotate180_rotate180 (d : Direction) : d.rotate180.rotate180 = d := by
    cases d <;> rfl

/-- 180° 回転後の isEast は元の isWest と等しい -/
theorem isEast_rotate180 (d : Direction) : d.rotate180.isEast = d.isWest := by
    cases d <;> rfl

/-- 180° 回転後の isWest は元の isEast と等しい -/
theorem isWest_rotate180 (d : Direction) : d.rotate180.isWest = d.isEast := by
    cases d <;> rfl

/-- 隣接関係は 180° 回転で保存される -/
theorem adjacent_rotate180 (d1 d2 : Direction) :
        d1.rotate180.adjacent d2.rotate180 = d1.adjacent d2 := by
    cases d1 <;> cases d2 <;> rfl

end Direction

-- ============================================================
-- LayerIndex (レイヤインデックス)
-- ============================================================

/-- シェイプ内のレイヤの位置を表すインデックス。l1 が最下層、l4 が最上層 -/
inductive LayerIndex where
    | l1 | l2 | l3 | l4
    deriving Repr, DecidableEq, BEq

namespace LayerIndex

/-- 上下レイヤが垂直に隣接しているかを判定する -/
def verticallyAdjacent : LayerIndex → LayerIndex → Bool
    | l1, l2 | l2, l1 => true
    | l2, l3 | l3, l2 => true
    | l3, l4 | l4, l3 => true
    | _, _             => false

/-- 全てのレイヤインデックスのリスト -/
def all : List LayerIndex := [l1, l2, l3, l4]

-- ============================================================
-- LayerIndex の定理
-- ============================================================

/-- 垂直隣接関係は対称的である -/
theorem verticallyAdjacent_symm (i j : LayerIndex) :
        i.verticallyAdjacent j = j.verticallyAdjacent i := by
    cases i <;> cases j <;> rfl

/-- 垂直隣接関係は反射的でない -/
theorem not_verticallyAdjacent_self (i : LayerIndex) :
        i.verticallyAdjacent i = false := by
    cases i <;> rfl

end LayerIndex

-- ============================================================
-- QuarterPos (象限位置)
-- ============================================================

/-- シェイプ内の象限の絶対位置。レイヤインデックスと方角の組 -/
structure QuarterPos where
    /-- レイヤの位置 -/
    layer : LayerIndex
    /-- レイヤ内の方角 -/
    dir : Direction
    deriving Repr, DecidableEq, BEq

namespace QuarterPos

/-- レイヤから方角に対応する象限を取得する -/
def getDir (l : Layer) : Direction → Quarter
    | .ne => l.ne
    | .se => l.se
    | .sw => l.sw
    | .nw => l.nw

/-- シェイプから指定位置の象限を取得する。レイヤ数を超えた位置の場合は `none` -/
def getQuarter (s : Shape) (pos : QuarterPos) : Option Quarter :=
    match s, pos.layer with
    | Shape.single l1,           .l1 => some (getDir l1 pos.dir)
    | Shape.double l1 _,         .l1 => some (getDir l1 pos.dir)
    | Shape.double _ l2,         .l2 => some (getDir l2 pos.dir)
    | Shape.triple l1 _ _,       .l1 => some (getDir l1 pos.dir)
    | Shape.triple _ l2 _,       .l2 => some (getDir l2 pos.dir)
    | Shape.triple _ _ l3,       .l3 => some (getDir l3 pos.dir)
    | Shape.quadruple l1 _ _ _,  .l1 => some (getDir l1 pos.dir)
    | Shape.quadruple _ l2 _ _,  .l2 => some (getDir l2 pos.dir)
    | Shape.quadruple _ _ l3 _,  .l3 => some (getDir l3 pos.dir)
    | Shape.quadruple _ _ _ l4,  .l4 => some (getDir l4 pos.dir)
    | _, _ => none

/-- レイヤの方角に対応する象限を置き換える -/
def setDir (l : Layer) (d : Direction) (q : Quarter) : Layer :=
    match d with
    | .ne => { l with ne := q }
    | .se => { l with se := q }
    | .sw => { l with sw := q }
    | .nw => { l with nw := q }

/-- シェイプの指定位置の象限を置き換える。レイヤ数を超えた位置の場合は元のシェイプを返す -/
def setQuarter (s : Shape) (pos : QuarterPos) (q : Quarter) : Shape :=
    match s, pos.layer with
    | Shape.single l1,              .l1 => Shape.single (setDir l1 pos.dir q)
    | Shape.double l1 l2,           .l1 => Shape.double (setDir l1 pos.dir q) l2
    | Shape.double l1 l2,           .l2 => Shape.double l1 (setDir l2 pos.dir q)
    | Shape.triple l1 l2 l3,        .l1 => Shape.triple (setDir l1 pos.dir q) l2 l3
    | Shape.triple l1 l2 l3,        .l2 => Shape.triple l1 (setDir l2 pos.dir q) l3
    | Shape.triple l1 l2 l3,        .l3 => Shape.triple l1 l2 (setDir l3 pos.dir q)
    | Shape.quadruple l1 l2 l3 l4,  .l1 => Shape.quadruple (setDir l1 pos.dir q) l2 l3 l4
    | Shape.quadruple l1 l2 l3 l4,  .l2 => Shape.quadruple l1 (setDir l2 pos.dir q) l3 l4
    | Shape.quadruple l1 l2 l3 l4,  .l3 => Shape.quadruple l1 l2 (setDir l3 pos.dir q) l4
    | Shape.quadruple l1 l2 l3 l4,  .l4 => Shape.quadruple l1 l2 l3 (setDir l4 pos.dir q)
    | s, _ => s

/-- シェイプ内で有効な位置（レイヤ数の範囲内）かを判定する -/
def isValid (s : Shape) (pos : QuarterPos) : Bool :=
    match s, pos.layer with
    | Shape.single _,      .l1 => true
    | Shape.double _ _,    .l1 | Shape.double _ _,    .l2 => true
    | Shape.triple _ _ _,  .l1 | Shape.triple _ _ _,  .l2 | Shape.triple _ _ _,  .l3 => true
    | Shape.quadruple ..,  _   => true
    | _, _ => false

/-- シェイプで有効な全位置のリストを返す -/
def allValid (s : Shape) : List QuarterPos :=
    let layers : List LayerIndex := match s with
        | Shape.single _      => [LayerIndex.l1]
        | Shape.double _ _    => [.l1, .l2]
        | Shape.triple _ _ _  => [.l1, .l2, .l3]
        | Shape.quadruple ..  => [.l1, .l2, .l3, .l4]
    layers.flatMap fun li => Direction.all.map fun d => ⟨li, d⟩

/-- 象限位置を 180° 回転させる（方角のみ回転、レイヤは変わらない） -/
def rotate180 (p : QuarterPos) : QuarterPos :=
    { layer := p.layer, dir := p.dir.rotate180 }

end QuarterPos
