import S2IL.Shape.Types.Atom

/-!
# S2IL.Shape.Types.Quarter

1 象限の状態と基本判定。
-/

namespace S2IL

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

/-- 結合能力を持つ象限は空ではない。 -/
theorem not_isEmpty_of_canFormBond {q : Quarter} (h : q.canFormBond = true) :
    ¬ q.isEmpty := by
  cases q <;> intro hEmpty <;> simp only [canFormBond, isEmpty, Bool.false_eq_true] at h hEmpty

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

end S2IL