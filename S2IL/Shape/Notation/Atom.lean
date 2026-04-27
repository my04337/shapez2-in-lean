-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.Types

/-!
# S2IL.Shape.Notation.Atom

原子型（`Color` / `PartCode` / `RegularPartCode`）の 1 文字表現と
ラウンドトリップ補題。`Quarter` / `Layer` / `Shape` の文字列表現は
`S2IL.Shape.Notation` 側で定義する。

## エンコード規約

| Color    | `r`/`g`/`b`/`y`/`c`/`m`/`w`/`k`/`u` |
| PartCode | `C`(circle)/`R`(rectangle)/`S`(star)/`W`(windmill)/`P`(pin)/`c`(crystal) |
| RegularPartCode | PartCode から pin/crystal を除いたもの |
-/

namespace S2IL

-- ============================================================
-- Color
-- ============================================================

namespace Color

def toChar : Color → Char
  | red       => 'r'
  | green     => 'g'
  | blue      => 'b'
  | yellow    => 'y'
  | cyan      => 'c'
  | magenta   => 'm'
  | white     => 'w'
  | black     => 'k'
  | uncolored => 'u'

def ofChar? : Char → Option Color
  | 'r' => some red
  | 'g' => some green
  | 'b' => some blue
  | 'y' => some yellow
  | 'c' => some cyan
  | 'm' => some magenta
  | 'w' => some white
  | 'k' => some black
  | 'u' => some uncolored
  | _   => none

@[simp] theorem ofChar_toChar (c : Color) : ofChar? c.toChar = some c := by
  cases c <;> rfl

instance : ToString Color := ⟨fun c => c.toChar.toString⟩

end Color

-- ============================================================
-- PartCode
-- ============================================================

namespace PartCode

def toChar : PartCode → Char
  | circle    => 'C'
  | rectangle => 'R'
  | star      => 'S'
  | windmill  => 'W'
  | pin       => 'P'
  | crystal   => 'c'

def ofChar? : Char → Option PartCode
  | 'C' => some circle
  | 'R' => some rectangle
  | 'S' => some star
  | 'W' => some windmill
  | 'P' => some pin
  | 'c' => some crystal
  | _   => none

@[simp] theorem ofChar_toChar (p : PartCode) : ofChar? p.toChar = some p := by
  cases p <;> rfl

instance : ToString PartCode := ⟨fun p => p.toChar.toString⟩

end PartCode

-- ============================================================
-- RegularPartCode
-- ============================================================

namespace RegularPartCode

def toChar : RegularPartCode → Char
  | circle    => 'C'
  | rectangle => 'R'
  | star      => 'S'
  | windmill  => 'W'

def ofChar? : Char → Option RegularPartCode
  | 'C' => some circle
  | 'R' => some rectangle
  | 'S' => some star
  | 'W' => some windmill
  | _   => none

@[simp] theorem ofChar_toChar (p : RegularPartCode) : ofChar? p.toChar = some p := by
  cases p <;> rfl

instance : ToString RegularPartCode := ⟨fun p => p.toChar.toString⟩

end RegularPartCode

end S2IL
