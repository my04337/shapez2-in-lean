-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel

/-!
# S2IL.Operations.Painter

着色機 (A-2-3)。最上位レイヤの **通常パーツ** (`Quarter.colored _ _`) のみを
指定色で塗り替える。空・ピン・結晶は不変。

## セマンティクス

- 対象: 最上位レイヤ (`s.getLast?`) の `Quarter.colored part _` を `Quarter.colored part c` に置換
- 非対象: 空 / ピン / 結晶 / それ以外のレイヤの全象限
- 0 層シェイプは不変（`[]` は最上位レイヤを持たない）

## 公開 API

- `Quarter.paint : Quarter → Color → Quarter`
- `Layer.paint : Layer → Color → Layer`
- `Shape.paint : Shape → Color → Shape`
- 冪等性 (`Shape.paint.idempotent`)
- CW 等変性 (`Shape.paint.rotateCW_comm`) と 180°/CCW 1 行系

## 単一チェーン原則

CW 等変性のみを直接証明、180° / CCW は `Shape.rotate180_eq_rotateCW_rotateCW` 経由の 1 行系。
-/

namespace S2IL

-- ============================================================
-- Quarter / Layer の paint
-- ============================================================

/-- 1 象限の塗り替え。通常パーツのみ色を上書き、それ以外は不変。 -/
def Quarter.paint (q : Quarter) (c : Color) : Quarter :=
  match q with
  | Quarter.colored p _ => Quarter.colored p c
  | _ => q

@[simp] theorem Quarter.paint_empty (c : Color) : Quarter.empty.paint c = Quarter.empty := rfl
@[simp] theorem Quarter.paint_pin (c : Color) : Quarter.pin.paint c = Quarter.pin := rfl
@[simp] theorem Quarter.paint_crystal (c c' : Color) :
    (Quarter.crystal c').paint c = Quarter.crystal c' := rfl
@[simp] theorem Quarter.paint_colored (p : RegularPartCode) (c c' : Color) :
    (Quarter.colored p c').paint c = Quarter.colored p c := rfl

theorem Quarter.paint_idempotent (q : Quarter) (c : Color) :
    (q.paint c).paint c = q.paint c := by
  cases q <;> rfl

/-- 1 レイヤの塗り替え。各象限を `Quarter.paint` する。 -/
def Layer.paint (l : Layer) (c : Color) : Layer :=
  fun d => (l d).paint c

@[simp] theorem Layer.paint_apply (l : Layer) (c : Color) (d : Fin 4) :
    (l.paint c) d = (l d).paint c := rfl

theorem Layer.paint_idempotent (l : Layer) (c : Color) :
    (l.paint c).paint c = l.paint c := by
  funext d; exact Quarter.paint_idempotent (l d) c

/-- `Layer.paint` は CW 回転と可換。 -/
theorem Layer.paint_rotateCW (l : Layer) (c : Color) :
    (l.paint c).rotateCW = l.rotateCW.paint c := by
  funext d
  simp [Layer.rotateCW, Layer.paint]

-- ============================================================
-- Shape.paint
-- ============================================================

/-- シェイプの塗り替え。最上位レイヤの通常パーツを指定色に置換する。 -/
def Shape.paint : Shape → Color → Shape
  | [], _ => []
  | [l], c => [l.paint c]
  | l₁ :: l₂ :: rest, c => l₁ :: Shape.paint (l₂ :: rest) c

@[simp] theorem Shape.paint_nil (c : Color) : Shape.paint [] c = [] := rfl

@[simp] theorem Shape.paint_singleton (l : Layer) (c : Color) :
    Shape.paint [l] c = [l.paint c] := rfl

@[simp] theorem Shape.paint_cons_cons (l₁ l₂ : Layer) (rest : List Layer) (c : Color) :
    Shape.paint (l₁ :: l₂ :: rest) c = l₁ :: Shape.paint (l₂ :: rest) c := rfl

/-- 非空 cons の paint 分配（補助）。 -/
theorem Shape.paint_cons_of_ne_nil (l : Layer) (rest : List Layer) (hne : rest ≠ [])
    (c : Color) : Shape.paint (l :: rest) c = l :: Shape.paint rest c := by
  cases rest with
  | nil => exact absurd rfl hne
  | cons _ _ => rfl

/-- `Shape.paint` は List 長を保存する（補助）。 -/
theorem Shape.paint_length (s : Shape) (c : Color) :
    (Shape.paint s c).length = s.length := by
  induction s with
  | nil => rfl
  | cons l rest ih =>
    cases rest with
    | nil => rfl
    | cons _ _ =>
      simp only [Shape.paint_cons_cons, List.length_cons]
      simp [ih]

/-- `paint` は冪等。 -/
theorem Shape.paint.idempotent (s : Shape) (c : Color) :
    Shape.paint (Shape.paint s c) c = Shape.paint s c := by
  induction s with
  | nil => rfl
  | cons l rest ih =>
    cases rest with
    | nil => simp [Layer.paint_idempotent]
    | cons l₂ rest' =>
      have hne : Shape.paint (l₂ :: rest') c ≠ [] := by
        intro h
        have := congrArg List.length h
        simp [Shape.paint_length] at this
      rw [Shape.paint_cons_cons,
          Shape.paint_cons_of_ne_nil l _ hne c,
          ih]

/-- `paint` と CW 回転は可換。 -/
theorem Shape.paint.rotateCW_comm (s : Shape) (c : Color) :
    Shape.rotateCW (Shape.paint s c) = Shape.paint (Shape.rotateCW s) c := by
  induction s with
  | nil => rfl
  | cons l rest ih =>
    cases rest with
    | nil =>
      show ((l.paint c) :: []).map Layer.rotateCW = Shape.paint [l.rotateCW] c
      simp [Layer.paint_rotateCW]
    | cons l₂ rest' =>
      have hne_paint : Shape.paint (l₂ :: rest') c ≠ [] := by
        intro h
        have := congrArg List.length h
        simp [Shape.paint_length] at this
      have hne_rot : Shape.rotateCW (l₂ :: rest') ≠ [] := by
        intro h
        have := congrArg List.length h
        simp [Shape.rotateCW] at this
      -- LHS = Shape.rotateCW (l :: Shape.paint (l₂::rest') c)
      --     = l.rotateCW :: Shape.rotateCW (Shape.paint (l₂::rest') c)
      -- RHS = Shape.paint (l.rotateCW :: Shape.rotateCW (l₂::rest')) c
      --     = l.rotateCW :: Shape.paint (Shape.rotateCW (l₂::rest')) c
      show Shape.rotateCW (l :: Shape.paint (l₂ :: rest') c)
            = Shape.paint (l.rotateCW :: Shape.rotateCW (l₂ :: rest')) c
      rw [Shape.paint_cons_of_ne_nil l.rotateCW _ hne_rot c]
      show l.rotateCW :: (Shape.paint (l₂ :: rest') c).map Layer.rotateCW
            = l.rotateCW :: Shape.paint (Shape.rotateCW (l₂ :: rest')) c
      exact congrArg (l.rotateCW :: ·) ih

/-- `paint` と 180° 回転は可換（CW の系）。 -/
theorem Shape.paint.rotate180_comm (s : Shape) (c : Color) :
    Shape.rotate180 (Shape.paint s c) = Shape.paint (Shape.rotate180 s) c := by
  simp [Shape.rotate180_eq_rotateCW_rotateCW, Shape.paint.rotateCW_comm]

/-- `paint` と CCW 回転は可換（CW の系）。 -/
theorem Shape.paint.rotateCCW_comm (s : Shape) (c : Color) :
    Shape.rotateCCW (Shape.paint s c) = Shape.paint (Shape.rotateCCW s) c := by
  simp [Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW, Shape.paint.rotateCW_comm]

end S2IL
