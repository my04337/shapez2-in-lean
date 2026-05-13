-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

/-!
# S2IL.Shape.Types.Direction

`Direction := Fin 4` と方角算術の基本補題。
-/

namespace S2IL

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

/-! ### `+1` / `-1` の相殺補題

`Fin 4` 上の `+1` と `-1` は逆元同士のため打ち消し合うが、`omega` だけでは
`Fin` 引数の等式を直接閉じられないため `ext` を 1 段挟んで `omega` する。
本セクションでは Operations 各層の等変性証明で繰り返し現れる小補題を集約する。 -/

/-- `(d + 1) - 1 = d`。 -/
theorem add_one_sub_one (d : Direction) : d + 1 - 1 = d := by
  ext; simp [Fin.sub_def, Fin.add_def]; omega

/-- `(d - 1) + 1 = d`。 -/
theorem sub_one_add_one (d : Direction) : d - 1 + 1 = d := by
  ext; simp [Fin.sub_def, Fin.add_def]; omega

/-- `(d₁ + 1) - (d₂ + 1) = d₁ - d₂`（隣接判定の CW 等変性で利用）。 -/
theorem add_one_sub_add_one (d₁ d₂ : Direction) :
    (d₁ + 1) - (d₂ + 1) = d₁ - d₂ := by
  ext; simp [Fin.sub_def, Fin.add_def]; omega

/-- `+1` の単射性: `d₁ + 1 = d₂ + 1 ↔ d₁ = d₂`。 -/
theorem add_one_inj {d₁ d₂ : Direction} : d₁ + 1 = d₂ + 1 ↔ d₁ = d₂ := by
  constructor
  · intro h
    have h' : d₁ + 1 - 1 = d₂ + 1 - 1 := by rw [h]
    rwa [add_one_sub_one, add_one_sub_one] at h'
  · intro h; rw [h]

/-- 180° 相当: `d - 1 - 1 = d + 1 + 1`（`Fin 4` の算術）。 -/
theorem sub_two_eq_add_two (d : Direction) : d - 1 - 1 = d + 1 + 1 := by
  ext; simp [Fin.sub_def, Fin.add_def]; omega

end Direction

end S2IL