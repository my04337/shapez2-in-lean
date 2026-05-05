-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

/-!
# S2IL.Shape.Types.Atom

象限を構成する原子型: `Color` / `PartCode` / `RegularPartCode`。

| 型 | 概要 |
|---|---|
| `Color` | 象限のカラー（無色 + 1 原色 3 種 + 2 原色 3 種 + 3 原色 2 種） |
| `PartCode` | 全パーツ種別（ピン・結晶含む） |
| `RegularPartCode` | 通常パーツ（ピン・結晶を除く） |

文字列表現は `S2IL.Shape.Notation.Atom` に分離。混色規則は
`docs/shapez2/game-system-overview.md` を参照。
-/

namespace S2IL

-- ============================================================
-- Color
-- ============================================================

/-- 象限のカラーコード。

`r`/`g`/`b` を 1 原色、`y`/`c`/`m` を 2 原色、`w`（明）と `k`（暗）を
3 原色、`u` を無色とする。 -/
inductive Color where
  | red | green | blue
  | yellow | cyan | magenta
  | white | black
  | uncolored
  deriving Repr, DecidableEq, BEq

namespace Color

/-- 全カラーのリスト。 -/
def all : List Color :=
  [red, green, blue, yellow, cyan, magenta, white, black, uncolored]

/-- 2 色を等体積で混合する。

新仕様（`docs/shapez2/game-system-overview.md` 参照）。
可換だが結合則は成立しない（2 入力演算）。

* `u + x = x + u = x`（無色は恒等元）
* `w + w = k`、`k + k = k`、`w + k = k + w = u`（3 原色同士）
* `w` / `k` は非無色・非 3 原色色を相手に取ると、その相手をそのまま返す
* 1 原色 + 1 原色（異）→ ビット OR（2 原色）
* 1 原色 + 2 原色 → 共通成分があればその 1 原色、なければ `w`
* 2 原色 + 2 原色（異）→ `w`（旧 AND 仕様は廃止）
-/
def mix : Color → Color → Color
  -- 無色は恒等元
  | uncolored, x => x
  | x, uncolored => x
  -- 3 原色同士
  | white,  white => black
  | black,  black => black
  | white,  black => uncolored
  | black,  white => uncolored
  -- 3 原色 + 非 3 原色（非無色）→ 相手側
  | white, x => x
  | black, x => x
  | x, white => x
  | x, black => x
  -- 1 原色・2 原色 同色 → そのまま
  | red,     red     => red
  | green,   green   => green
  | blue,    blue    => blue
  | yellow,  yellow  => yellow
  | cyan,    cyan    => cyan
  | magenta, magenta => magenta
  -- 1 原色 + 1 原色（異）→ OR（2 原色）
  | red,   green => yellow
  | green, red   => yellow
  | green, blue  => cyan
  | blue,  green => cyan
  | red,   blue  => magenta
  | blue,  red   => magenta
  -- 1 原色 + 2 原色（含む）→ 1 原色（AND）
  | red,     yellow  => red
  | yellow,  red     => red
  | red,     magenta => red
  | magenta, red     => red
  | green,   yellow  => green
  | yellow,  green   => green
  | green,   cyan    => green
  | cyan,    green   => green
  | blue,    cyan    => blue
  | cyan,    blue    => blue
  | blue,    magenta => blue
  | magenta, blue    => blue
  -- 1 原色 + 2 原色（含まない）→ white
  | red,     cyan    => white
  | cyan,    red     => white
  | green,   magenta => white
  | magenta, green   => white
  | blue,    yellow  => white
  | yellow,  blue    => white
  -- 2 原色 + 2 原色（異）→ white
  | yellow,  cyan    => white
  | cyan,    yellow  => white
  | yellow,  magenta => white
  | magenta, yellow  => white
  | cyan,    magenta => white
  | magenta, cyan    => white

theorem mix_comm (a b : Color) : mix a b = mix b a := by
  cases a <;> cases b <;> rfl

@[simp] theorem mix_uncolored_left (a : Color) : mix uncolored a = a := by
  cases a <;> rfl

@[simp] theorem mix_uncolored_right (a : Color) : mix a uncolored = a := by
  cases a <;> rfl

instance : Std.Commutative mix := ⟨mix_comm⟩
instance : Std.LeftIdentity mix uncolored := ⟨⟩
instance : Std.LawfulLeftIdentity mix uncolored := ⟨mix_uncolored_left⟩
instance : Std.RightIdentity mix uncolored := ⟨⟩
instance : Std.LawfulRightIdentity mix uncolored := ⟨mix_uncolored_right⟩

end Color

-- ============================================================
-- PartCode
-- ============================================================

/-- 象限のシェイプ種別。 -/
inductive PartCode where
  | circle | rectangle | star | windmill | pin | crystal
  deriving Repr, DecidableEq, BEq

namespace PartCode

def all : List PartCode := [circle, rectangle, star, windmill, pin, crystal]

end PartCode

-- ============================================================
-- RegularPartCode（ピン・結晶を除く）
-- ============================================================

/-- ピン・結晶を除いた通常パーツのコード。`Quarter.colored` の制約に使う。 -/
inductive RegularPartCode where
  | circle | rectangle | star | windmill
  deriving Repr, DecidableEq, BEq

namespace RegularPartCode

def all : List RegularPartCode := [circle, rectangle, star, windmill]

/-- 通常パーツコードを `PartCode` に持ち上げる。 -/
def toPartCode : RegularPartCode → PartCode
  | circle    => .circle
  | rectangle => .rectangle
  | star      => .star
  | windmill  => .windmill

/-- `PartCode` から通常パーツコードへ。ピン・結晶は `none`。 -/
def ofPartCode? : PartCode → Option RegularPartCode
  | .circle    => some circle
  | .rectangle => some rectangle
  | .star      => some star
  | .windmill  => some windmill
  | .pin | .crystal => none

@[simp] theorem ofPartCode_toPartCode (p : RegularPartCode) :
    ofPartCode? p.toPartCode = some p := by
  cases p <;> rfl

end RegularPartCode

end S2IL
