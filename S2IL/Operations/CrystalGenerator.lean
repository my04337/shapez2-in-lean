-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel

/-!
# S2IL.Operations.CrystalGenerator

結晶製造機 (A-2-6)。空象限とピン象限を指定色の結晶で無条件に充填する。

## セマンティクス

- 対象: `Quarter.empty` と `Quarter.pin` の **両方** を指定色の結晶 (`Quarter.crystal c`) に置換
  （docs/shapez2/game-system-overview.md「隙間 (Gaps) や ピン (Pins)」に対応）
- 非対象: 既存の通常パーツと結晶は置き換わらない（色も保持）
- 全レイヤを対象: 接地・settled 判定を問わず、シェイプ内の全 empty/pin を結晶化する
  （ゲーム仕様上、出力が必ず settled になるかは stack/pinPush 側の責務）

## 公開 API

- `Quarter.crystallize : Quarter → Color → Quarter`
- `Layer.crystallize : Layer → Color → Layer`
- `Shape.crystallize : Shape → Color → Shape`
- 冪等性 (`Shape.crystallize.idempotent`)
- CW 等変性 (`Shape.crystallize.rotateCW_comm`) と 180°/CCW 1 行系

## 単一チェーン原則

CW 等変性のみを直接証明、180° / CCW は 1 行系。
-/

namespace S2IL

-- ============================================================
-- Quarter / Layer の crystallize
-- ============================================================

/-- 1 象限の結晶化。空とピンを `Quarter.crystal c` に置換、それ以外は不変。 -/
def Quarter.crystallize (q : Quarter) (c : Color) : Quarter :=
  match q with
  | Quarter.empty => Quarter.crystal c
  | Quarter.pin => Quarter.crystal c
  | _ => q

@[simp] theorem Quarter.crystallize_empty (c : Color) :
    Quarter.empty.crystallize c = Quarter.crystal c := rfl
@[simp] theorem Quarter.crystallize_pin (c : Color) :
    Quarter.pin.crystallize c = Quarter.crystal c := rfl
@[simp] theorem Quarter.crystallize_crystal (c c' : Color) :
    (Quarter.crystal c').crystallize c = Quarter.crystal c' := rfl
@[simp] theorem Quarter.crystallize_colored (p : RegularPartCode) (c c' : Color) :
    (Quarter.colored p c').crystallize c = Quarter.colored p c' := rfl

theorem Quarter.crystallize_idempotent (q : Quarter) (c : Color) :
    (q.crystallize c).crystallize c = q.crystallize c := by
  cases q <;> rfl

/-- 1 レイヤの結晶化。 -/
def Layer.crystallize (l : Layer) (c : Color) : Layer :=
  fun d => (l d).crystallize c

@[simp] theorem Layer.crystallize_apply (l : Layer) (c : Color) (d : Fin 4) :
    (l.crystallize c) d = (l d).crystallize c := rfl

theorem Layer.crystallize_idempotent (l : Layer) (c : Color) :
    (l.crystallize c).crystallize c = l.crystallize c := by
  funext d; exact Quarter.crystallize_idempotent (l d) c

/-- `Layer.crystallize` は CW 回転と可換。 -/
theorem Layer.crystallize_rotateCW (l : Layer) (c : Color) :
    (l.crystallize c).rotateCW = l.rotateCW.crystallize c := by
  funext d
  simp [Layer.rotateCW, Layer.crystallize]

-- ============================================================
-- Shape.crystallize
-- ============================================================

/-- シェイプの結晶化。全レイヤの空・ピン象限を結晶 c で充填する。 -/
def Shape.crystallize (s : Shape) (c : Color) : Shape :=
  s.map (fun l => l.crystallize c)

@[simp] theorem Shape.crystallize_nil (c : Color) : Shape.crystallize [] c = [] := rfl

@[simp] theorem Shape.crystallize_cons (l : Layer) (rest : List Layer) (c : Color) :
    Shape.crystallize (l :: rest) c = l.crystallize c :: Shape.crystallize rest c := rfl

/-- `crystallize` は冪等。 -/
theorem Shape.crystallize.idempotent (s : Shape) (c : Color) :
    (Shape.crystallize s c).crystallize c = Shape.crystallize s c := by
  unfold Shape.crystallize
  rw [List.map_map]
  apply List.map_congr_left
  intro l _
  exact Layer.crystallize_idempotent l c

/-- `crystallize` と CW 回転は可換。 -/
theorem Shape.crystallize.rotateCW_comm (s : Shape) (c : Color) :
    (Shape.crystallize s c).rotateCW = Shape.crystallize s.rotateCW c := by
  unfold Shape.crystallize Shape.rotateCW
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro l _
  exact Layer.crystallize_rotateCW l c

/-- `crystallize` と 180° 回転は可換（CW の系）。 -/
theorem Shape.crystallize.rotate180_comm (s : Shape) (c : Color) :
    (Shape.crystallize s c).rotate180 = Shape.crystallize s.rotate180 c := by
  simp [Shape.rotate180_eq_rotateCW_rotateCW, Shape.crystallize.rotateCW_comm]

/-- `crystallize` と CCW 回転は可換（CW の系）。 -/
theorem Shape.crystallize.rotateCCW_comm (s : Shape) (c : Color) :
    (Shape.crystallize s c).rotateCCW = Shape.crystallize s.rotateCCW c := by
  simp [Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW, Shape.crystallize.rotateCW_comm]

end S2IL
