-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.Shape

/-!
# QuarterPos (象限位置)

シェイプ内の象限の絶対位置を表す型。
レイヤインデックス（0-indexed の `Nat`）と方角の組で構成される。

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

## レイヤインデックス

シェイプ内のレイヤ位置は 0-indexed の `Nat` で表す。
0 が最下層、値が大きいほど上層。
上下に隣接するレイヤ間で結晶の結合が発生しうる。

## QuarterPos (象限位置)

レイヤインデックス (`Nat`) と `Direction` の組でシェイプ内の象限の絶対位置を表す。
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

instance : LawfulBEq Direction where
    eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | contradiction
    rfl {a} := by cases a <;> rfl

end Direction

-- ============================================================
-- レイヤインデックスのユーティリティ関数（Nat ベース）
-- ============================================================

namespace LayerIndex

/-- 上下レイヤが垂直に隣接しているかを判定する（0-indexed） -/
def verticallyAdjacent (i j : Nat) : Bool :=
    i + 1 == j || j + 1 == i

-- ============================================================
-- レイヤインデックスの定理
-- ============================================================

/-- 垂直隣接関係は対称的である -/
theorem verticallyAdjacent_symm (i j : Nat) :
        verticallyAdjacent i j = verticallyAdjacent j i := by
    simp only [verticallyAdjacent, Bool.or_comm]

/-- 垂直隣接関係は反射的でない -/
theorem not_verticallyAdjacent_self (i : Nat) :
        verticallyAdjacent i i = false := by
    simp only [verticallyAdjacent, Bool.or_self]
    exact decide_eq_false_iff_not.mpr (by omega)

end LayerIndex

-- ============================================================
-- QuarterPos (象限位置)
-- ============================================================

/-- シェイプ内の象限の絶対位置。レイヤインデックス (0-indexed Nat) と方角の組 -/
structure QuarterPos where
    /-- レイヤの位置 (0-indexed、0 が最下層) -/
    layer : Nat
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
    match s.layers[pos.layer]? with
    | some l => some (getDir l pos.dir)
    | none   => none

/-- レイヤの方角に対応する象限を置き換える -/
def setDir (l : Layer) (d : Direction) (q : Quarter) : Layer :=
    match d with
    | .ne => { l with ne := q }
    | .se => { l with se := q }
    | .sw => { l with sw := q }
    | .nw => { l with nw := q }

/-- シェイプの指定位置の象限を置き換える。レイヤ数を超えた位置の場合は元のシェイプを返す -/
def setQuarter (s : Shape) (pos : QuarterPos) (q : Quarter) : Shape :=
    let layers := s.layers
    match layers[pos.layer]? with
    | none   => s
    | some l =>
        let newLayer := setDir l pos.dir q
        let newLayers := layers.set pos.layer newLayer
        match h : newLayers with
        | []      => s  -- ありえないが安全策
        | _ :: _  => ⟨newLayers, by simp only [h, ne_eq, reduceCtorEq, not_false_eq_true]⟩

/-- シェイプ内で有効な位置（レイヤ数の範囲内）かを判定する -/
def isValid (s : Shape) (pos : QuarterPos) : Bool :=
    pos.layer < s.layerCount

/-- シェイプで有効な全位置のリストを返す -/
def allValid (s : Shape) : List QuarterPos :=
    let layerIndices := List.range s.layerCount
    layerIndices.flatMap fun li => Direction.all.map fun d => ⟨li, d⟩

/-- 象限位置を 180° 回転させる（方角のみ回転、レイヤは変わらない） -/
def rotate180 (p : QuarterPos) : QuarterPos :=
    { layer := p.layer, dir := p.dir.rotate180 }

/-- 180° 回転を 2 回適用すると元に戻る -/
@[simp] theorem rotate180_rotate180 (p : QuarterPos) : p.rotate180.rotate180 = p := by
    simp only [rotate180, Direction.rotate180_rotate180]

instance : LawfulBEq QuarterPos where
    eq_of_beq {a b} h := by
        cases a with | mk la da =>
        cases b with | mk lb db =>
        change (la == lb && da == db) = true at h
        rw [Bool.and_eq_true] at h
        congr
        · exact eq_of_beq h.1
        · exact eq_of_beq h.2
    rfl {a} := by
        cases a with | mk l d =>
        change (l == l && d == d) = true
        simp only [BEq.rfl, Bool.and_self]

end QuarterPos

namespace Shape

/-- 指定された位置のリストに含まれる全象限を `Quarter.empty` に置き換える -/
def clearPositions (s : Shape) (positions : List QuarterPos) : Shape :=
    positions.foldl (fun acc pos => pos.setQuarter acc .empty) s

end Shape

-- ============================================================
-- setDir / setQuarter の等式的性質
-- ============================================================

namespace QuarterPos

/-- Layer.empty の任意方角に .empty を設定しても変わらない -/
private theorem setDir_empty_empty (d : Direction) :
        setDir Layer.empty d .empty = Layer.empty := by
    cases d <;> rfl

/-- setDir (.empty) は方角の順序によらず可換 -/
theorem setDir_empty_comm (l : Layer) (d1 d2 : Direction) :
        setDir (setDir l d1 .empty) d2 .empty =
        setDir (setDir l d2 .empty) d1 .empty := by
    cases d1 <;> cases d2 <;> rfl

/-- setQuarter (.empty) の結果の .layers は List.set で表現できる。
    範囲外でも成り立つ（List.set と getD の範囲外動作による） -/
theorem setQuarter_empty_layers (s : Shape) (pos : QuarterPos) :
        (setQuarter s pos .empty).layers =
        s.layers.set pos.layer
            (setDir (s.layers.getD pos.layer Layer.empty) pos.dir .empty) := by
    unfold setQuarter
    cases hl : s.layers[pos.layer]? with
    | none =>
        have h_ge : s.layers.length ≤ pos.layer :=
            List.getElem?_eq_none_iff.mp hl
        simp only [hl]
        rw [List.set_eq_of_length_le h_ge]
    | some l =>
        have hgetD : s.layers.getD pos.layer Layer.empty = l := by
            simp only [List.getD_eq_getElem?_getD, hl, Option.getD_some]
        rw [hgetD]
        simp only [hl]
        split
        · exfalso
          rename_i h_nil
          have h_len := congrArg List.length h_nil
          simp only [List.length_nil, List.length_set] at h_len
          cases hl : s.layers with
          | nil => exact s.layers_ne hl
          | cons _ tl =>
            simp only [hl, List.length_cons] at h_len
            omega
        · rfl

/-- setQuarter .empty は layerCount を保存する -/
theorem layerCount_setQuarter_empty (s : Shape) (pos : QuarterPos) :
        (setQuarter s pos .empty).layerCount = s.layerCount := by
    show (setQuarter s pos .empty).layers.length = s.layers.length
    rw [setQuarter_empty_layers, List.length_set]

/-- setQuarter (.empty) は位置の順序によらず可換 -/
theorem setQuarter_empty_comm (s : Shape) (p q : QuarterPos) :
        setQuarter (setQuarter s q .empty) p .empty =
        setQuarter (setQuarter s p .empty) q .empty := by
    apply Shape.ext
    show (setQuarter (setQuarter s q .empty) p .empty).layers =
         (setQuarter (setQuarter s p .empty) q .empty).layers
    rw [setQuarter_empty_layers, setQuarter_empty_layers,
        setQuarter_empty_layers, setQuarter_empty_layers]
    have getD_set (l : List Layer) (i j : Nat) (a : Layer) :
            (l.set i a).getD j Layer.empty =
            if i = j ∧ i < l.length then a else l.getD j Layer.empty := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
        split <;> split <;> simp_all <;> omega
    simp only [getD_set]
    by_cases h_layer : p.layer = q.layer
    · rw [h_layer]
      by_cases h_lt : q.layer < s.layers.length
      · simp only [h_lt, and_self, ↓reduceIte, List.set_set, setDir_empty_comm]
      · simp only [h_lt, and_false, ↓reduceIte, List.getD_eq_getElem?_getD,
            not_false_eq_true, getElem?_neg, Option.getD_none, List.set_set,
            setDir_empty_empty]
    · have h_ne' : q.layer ≠ p.layer := fun h => h_layer h.symm
      simp only [List.getD_eq_getElem?_getD, h_ne', false_and, ↓reduceIte, h_layer]
      exact List.set_comm _ _ h_ne'

/-- setQuarter (.empty) は同位置で冪等 -/
theorem setQuarter_empty_idem (s : Shape) (pos : QuarterPos) :
        setQuarter (setQuarter s pos .empty) pos .empty =
        setQuarter s pos .empty := by
    apply Shape.ext
    rw [setQuarter_empty_layers, setQuarter_empty_layers]
    by_cases h_lt : pos.layer < s.layers.length
    · simp only [List.getD_eq_getElem?_getD, h_lt, getElem?_pos, Option.getD_some,
          List.length_set, List.getElem_set_self, List.set_set]
      cases pos.dir <;> rfl
    · have h_ge : s.layers.length ≤ pos.layer := by omega
      simp only [List.getD_eq_getElem?_getD, List.set_eq_of_length_le h_ge]

/-- getDir と setDir の関係（同方角） -/
theorem getDir_setDir_same (l : Layer) (d : Direction) (q : Quarter) :
        getDir (setDir l d q) d = q := by
    cases d <;> rfl

/-- getDir と setDir の関係（異方角） -/
theorem getDir_setDir_ne (l : Layer) (d1 d2 : Direction) (q : Quarter)
        (h : d1 ≠ d2) :
        getDir (setDir l d1 q) d2 = getDir l d2 := by
    cases d1 <;> cases d2 <;> first | exact absurd rfl h | rfl

/-- getQuarter と setQuarter (.empty) の関係（同位置・範囲内） -/
theorem getQuarter_setQuarter_empty_eq (s : Shape) (pos : QuarterPos)
        (h_lt : pos.layer < s.layerCount) :
        getQuarter (setQuarter s pos .empty) pos = some .empty := by
    simp only [getQuarter, setQuarter_empty_layers]
    have h_lt' : pos.layer < s.layers.length := h_lt
    rw [List.getElem?_set, if_pos h_lt']
    simp only [↓reduceIte, List.getD_eq_getElem?_getD, getDir_setDir_same]

/-- getQuarter と setQuarter (.empty) の関係（異位置） -/
theorem getQuarter_setQuarter_empty_ne (s : Shape) (pos1 pos2 : QuarterPos)
        (h : ¬((pos1 == pos2) = true)) :
        getQuarter (setQuarter s pos1 .empty) pos2 = getQuarter s pos2 := by
    have h_ne : pos1 ≠ pos2 := fun heq => h (heq ▸ beq_self_eq_true pos2)
    simp only [getQuarter, setQuarter_empty_layers]
    by_cases h_layer : pos1.layer = pos2.layer
    · -- 同レイヤ・異方角
      have h_dir : pos1.dir ≠ pos2.dir := by
          intro h_d; apply h_ne; cases pos1; cases pos2; subst h_d; subst h_layer; rfl
      by_cases h_lt : pos1.layer < s.layers.length
      · -- 範囲内
        rw [List.getElem?_set, if_pos h_layer, if_pos h_lt]
        rw [h_layer] at h_lt
        cases hl : s.layers[pos2.layer]? with
        | none => exact absurd (List.getElem?_eq_none_iff.mp hl) (by omega)
        | some l =>
          -- match some l の iota reduction
          show some _ = some (getDir l pos2.dir)
          congr 1
          have h_getD : s.layers.getD pos1.layer Layer.empty = l := by
              simp only [List.getD_eq_getElem?_getD, h_layer, hl, Option.getD_some]
          rw [h_getD]
          exact getDir_setDir_ne l pos1.dir pos2.dir .empty h_dir
      · -- 範囲外
        rw [List.getElem?_set, if_pos h_layer, if_neg h_lt]
        rw [h_layer] at h_lt
        rw [List.getElem?_eq_none_iff.mpr (by omega)]
    · -- 異レイヤ
      rw [List.getElem?_set_ne h_layer]

/-- clearPositions の getQuarter 特徴づけ（範囲内の位置） -/
theorem getQuarter_clearPositions (s : Shape) (ps : List QuarterPos)
        (pos : QuarterPos) (h_lt : pos.layer < s.layerCount) :
        getQuarter (s.clearPositions ps) pos =
        if ps.any (· == pos) then some .empty
        else getQuarter s pos := by
    induction ps generalizing s with
    | nil => simp only [Shape.clearPositions, List.foldl_nil, List.any, Bool.false_eq_true,
            ↓reduceIte]
    | cons p rest ih =>
        have h_lt' : pos.layer < (setQuarter s p .empty).layerCount := by
            rw [layerCount_setQuarter_empty]; exact h_lt
        -- clearPositions s (p :: rest) = clearPositions (setQuarter s p .empty) rest
        show getQuarter ((p.setQuarter s .empty).clearPositions rest) pos =
             if ((p :: rest).any (· == pos)) then some .empty
             else getQuarter s pos
        rw [ih (p.setQuarter s .empty) h_lt']
        simp only [List.any]
        by_cases h_eq : (p == pos) = true
        · -- p == pos: setQuarter で pos が empty 化済み
          simp only [h_eq, Bool.true_or, ↓reduceIte]
          rw [show p = pos from eq_of_beq h_eq]
          simp only [List.any_eq_true, beq_iff_eq, exists_eq_right,
              getQuarter_setQuarter_empty_eq s pos h_lt, ite_self]
        · -- p ≠ pos: setQuarter は pos に影響しない
          simp only [h_eq, Bool.false_or]
          rw [getQuarter_setQuarter_empty_ne s p pos h_eq]

end QuarterPos

-- ============================================================
-- clearPositions の順序不変性
-- ============================================================

namespace Shape

/-- clearPositions は layerCount を保存する -/
theorem layerCount_clearPositions (s : Shape) (ps : List QuarterPos) :
        (clearPositions s ps).layerCount = s.layerCount := by
    induction ps generalizing s with
    | nil => rfl
    | cons p rest ih =>
        exact (ih (p.setQuarter s .empty)).trans
            (QuarterPos.layerCount_setQuarter_empty s p)

/-- clearPositions で隣接する2要素を入れ替えても結果は同じ -/
theorem clearPositions_swap (s : Shape) (p q : QuarterPos)
        (ps : List QuarterPos) :
        clearPositions s (p :: q :: ps) = clearPositions s (q :: p :: ps) := by
    show ps.foldl (fun acc pos => pos.setQuarter acc .empty)
            (q.setQuarter (p.setQuarter s .empty) .empty) =
         ps.foldl (fun acc pos => pos.setQuarter acc .empty)
            (p.setQuarter (q.setQuarter s .empty) .empty)
    rw [QuarterPos.setQuarter_empty_comm]

/-- clearPositions は同じ位置集合（any 判定で同値）なら同結果 -/
theorem clearPositions_ext (s : Shape) (ps1 ps2 : List QuarterPos)
        (h : ∀ p, ps1.any (· == p) = ps2.any (· == p)) :
        clearPositions s ps1 = clearPositions s ps2 := by
    apply Shape.ext
    have h_len : (clearPositions s ps1).layers.length =
                 (clearPositions s ps2).layers.length := by
        rw [show (clearPositions s ps1).layers.length = s.layers.length from
                layerCount_clearPositions s ps1,
            show (clearPositions s ps2).layers.length = s.layers.length from
                layerCount_clearPositions s ps2]
    apply List.ext_getElem h_len
    intro i h1 h2
    have h_lt : i < s.layerCount := by
        rw [← layerCount_clearPositions s ps1]; exact h1
    -- 自然数 i と全方角 d について、getQuarter の結果が一致することを示す
    have dir_eq : ∀ d : Direction,
        QuarterPos.getDir (clearPositions s ps1).layers[i] d =
        QuarterPos.getDir (clearPositions s ps2).layers[i] d := by
      intro d
      have gq1 := QuarterPos.getQuarter_clearPositions s ps1 ⟨i, d⟩ h_lt
      have gq2 := QuarterPos.getQuarter_clearPositions s ps2 ⟨i, d⟩ h_lt
      rw [h ⟨i, d⟩] at gq1
      -- gq1 と gq2 は同じ RHS を持つ
      simp only [QuarterPos.getQuarter,
                 List.getElem?_eq_getElem h1,
                 List.getElem?_eq_getElem h2,
                 List.getElem?_eq_getElem h_lt] at gq1 gq2
      -- some (getDir l1 d) = rhs かつ some (getDir l2 d) = rhs
      exact Option.some.inj (gq1.trans gq2.symm)
    -- Layer の等価性: getDir 全方角の一致から導出
    suffices ∀ (l1 l2 : Layer),
        (∀ d, QuarterPos.getDir l1 d = QuarterPos.getDir l2 d) → l1 = l2 from
      this _ _ dir_eq
    intro ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ hd
    have := hd .ne; have := hd .se; have := hd .sw; have := hd .nw
    simp only [QuarterPos.getDir] at *
    subst_vars; rfl

end Shape
