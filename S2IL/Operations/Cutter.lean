-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel

/-!
# S2IL.Operations.Cutter

切断機 (A-2-1 + B-4-2)。Phase D-5 で axiom-free 化。

E/W 参照操作（§1.4.1 例外規則）の primitive を提供する。CW 等変性は持たず、
180° 回転についてのみ等変性が成り立つ。

## セマンティクス

- `Layer.eastHalf l` — NE/SE は `l` のまま、SW/NW を `Quarter.empty` に置換
- `Layer.westHalf l` — SW/NW は `l` のまま、NE/SE を `Quarter.empty` に置換
- `Layer.combineHalves a b` — NE/SE は `a`、SW/NW は `b` から取る
- `Shape.{eastHalf,westHalf}` は各レイヤへの `List.map`
- `Shape.combineHalves` は `List.zipWith Layer.combineHalves`（短い方に揃える）

## 公開 API

- `Layer.eastHalf` / `Layer.westHalf` / `Layer.combineHalves`
- `Shape.eastHalf` / `Shape.westHalf` / `Shape.combineHalves`
- `Shape.cut : Shape → Shape × Shape`（`eastHalf` + `westHalf` の派生 def）
- `Shape.halfDestroy : Shape → Shape`（`eastHalf` の別名 def）
- 構造的恒等式 (`combineHalves.eastHalf_westHalf` / `combineHalves.self`)
- 180° 回転等変性（primitive 3 本 + `cut` / `halfDestroy` の系）

## E/W 参照操作（§1.4.1）

primitive: `eastHalf` / `westHalf` / `combineHalves` の 3 操作のみ。
`cut` / `halfDestroy` は `def` 合成。`rotate180_comm` は primitive の系で導出。
CW / CCW 等変性は **存在しない**（E/W 軸が回転で N/S 軸へ写るため）。
-/

namespace S2IL

-- ============================================================
-- Layer level
-- ============================================================

/-- レイヤの東半分。NE/SE は `l` のまま、SW/NW は `Quarter.empty` に置換。 -/
def Layer.eastHalf (l : Layer) : Layer :=
  fun d => if d.val < 2 then l d else Quarter.empty

/-- レイヤの西半分。SW/NW は `l` のまま、NE/SE は `Quarter.empty` に置換。 -/
def Layer.westHalf (l : Layer) : Layer :=
  fun d => if d.val < 2 then Quarter.empty else l d

/-- 2 つのレイヤから東半分・西半分を取り出して合成。NE/SE は `a`、SW/NW は `b`。 -/
def Layer.combineHalves (a b : Layer) : Layer :=
  fun d => if d.val < 2 then a d else b d

@[simp] theorem Layer.eastHalf_apply (l : Layer) (d : Fin 4) :
    Layer.eastHalf l d = if d.val < 2 then l d else Quarter.empty := rfl

@[simp] theorem Layer.westHalf_apply (l : Layer) (d : Fin 4) :
    Layer.westHalf l d = if d.val < 2 then Quarter.empty else l d := rfl

@[simp] theorem Layer.combineHalves_apply (a b : Layer) (d : Fin 4) :
    Layer.combineHalves a b d = if d.val < 2 then a d else b d := rfl

/-- 東半分と西半分を合成すると元のレイヤに戻る。 -/
theorem Layer.combineHalves.eastHalf_westHalf (l : Layer) :
    Layer.combineHalves (Layer.eastHalf l) (Layer.westHalf l) = l := by
  funext d
  by_cases h : d.val < 2 <;> simp [Layer.combineHalves, Layer.eastHalf, Layer.westHalf, h]

/-- 同じレイヤを 2 つ合成しても結果は不変。 -/
theorem Layer.combineHalves.self (l : Layer) :
    Layer.combineHalves l l = l := by
  funext d
  by_cases h : d.val < 2 <;> simp [Layer.combineHalves, h]

-- Layer.rotate180 の点ごとの値（補助）。
private theorem Layer.rotate180_apply (l : Layer) (d : Fin 4) :
    l.rotate180 d = l (d - 2) := by
  rcases d with ⟨v, hv⟩
  match v, hv with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

/-- Layer 東半分と 180° 回転: 元の西半分の 180° 回転。 -/
theorem Layer.eastHalf.rotate180_comm (l : Layer) :
    Layer.eastHalf l.rotate180 = (Layer.westHalf l).rotate180 := by
  funext d
  rw [Layer.eastHalf_apply, Layer.rotate180_apply, Layer.rotate180_apply,
      Layer.westHalf_apply]
  rcases d with ⟨v, hv⟩
  match v, hv with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

/-- Layer 西半分と 180° 回転: 元の東半分の 180° 回転。 -/
theorem Layer.westHalf.rotate180_comm (l : Layer) :
    Layer.westHalf l.rotate180 = (Layer.eastHalf l).rotate180 := by
  funext d
  rw [Layer.westHalf_apply, Layer.rotate180_apply, Layer.rotate180_apply,
      Layer.eastHalf_apply]
  rcases d with ⟨v, hv⟩
  match v, hv with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

/-- Layer `combineHalves` と 180° 回転: 引数が swap されて 180° 回転される。 -/
theorem Layer.combineHalves.rotate180_comm (a b : Layer) :
    (Layer.combineHalves a b).rotate180 =
      Layer.combineHalves b.rotate180 a.rotate180 := by
  funext d
  rw [Layer.rotate180_apply, Layer.combineHalves_apply, Layer.combineHalves_apply,
      Layer.rotate180_apply, Layer.rotate180_apply]
  rcases d with ⟨v, hv⟩
  match v, hv with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

-- ============================================================
-- Shape level — primitives
-- ============================================================

/-- シェイプの東半分。各レイヤに `Layer.eastHalf` を適用。 -/
def Shape.eastHalf (s : Shape) : Shape := s.map Layer.eastHalf

/-- シェイプの西半分。各レイヤに `Layer.westHalf` を適用。 -/
def Shape.westHalf (s : Shape) : Shape := s.map Layer.westHalf

/-- 2 つのシェイプから東半分・西半分を取り出して合成（短い方に長さを揃える）。 -/
def Shape.combineHalves (s1 s2 : Shape) : Shape :=
  List.zipWith Layer.combineHalves s1 s2

@[simp] theorem Shape.eastHalf_nil : Shape.eastHalf [] = [] := rfl
@[simp] theorem Shape.westHalf_nil : Shape.westHalf [] = [] := rfl

@[simp] theorem Shape.eastHalf_cons (l : Layer) (rest : List Layer) :
    Shape.eastHalf (l :: rest) = l.eastHalf :: Shape.eastHalf rest := rfl

@[simp] theorem Shape.westHalf_cons (l : Layer) (rest : List Layer) :
    Shape.westHalf (l :: rest) = l.westHalf :: Shape.westHalf rest := rfl

/-- 東半分と西半分を合成すると元のシェイプに戻る。 -/
theorem Shape.combineHalves.eastHalf_westHalf (s : Shape) :
    Shape.combineHalves (Shape.eastHalf s) (Shape.westHalf s) = s := by
  induction s with
  | nil => rfl
  | cons l rest ih =>
    show Layer.combineHalves l.eastHalf l.westHalf
          :: List.zipWith Layer.combineHalves (Shape.eastHalf rest) (Shape.westHalf rest)
          = l :: rest
    rw [Layer.combineHalves.eastHalf_westHalf]
    exact congrArg (List.cons l) ih

/-- 同じシェイプを 2 つ合成しても結果は不変。 -/
theorem Shape.combineHalves.self (s : Shape) :
    Shape.combineHalves s s = s := by
  induction s with
  | nil => rfl
  | cons l rest ih =>
    show Layer.combineHalves l l :: List.zipWith Layer.combineHalves rest rest
          = l :: rest
    rw [Layer.combineHalves.self]
    exact congrArg (List.cons l) ih

-- ============================================================
-- Shape level — derived defs
-- ============================================================

/-- 切断: 東半分と西半分のペア（全関数）。 -/
def Shape.cut (s : Shape) : Shape × Shape :=
  (Shape.eastHalf s, Shape.westHalf s)

/-- 半壊: 東半分を残す（全関数）。 -/
def Shape.halfDestroy (s : Shape) : Shape :=
  Shape.eastHalf s

theorem Shape.halfDestroy.eq_cut_fst (s : Shape) :
    Shape.halfDestroy s = (Shape.cut s).1 := rfl

-- ============================================================
-- 180° 回転等変性（CW / CCW は持たない、§1.4.1）
-- ============================================================

-- Shape.rotate180 = ·.map Layer.rotate180（補助）。
private theorem Shape.rotate180_eq_map (s : Shape) :
    s.rotate180 = s.map Layer.rotate180 := by
  show (s.map Layer.rotateCW).map Layer.rotateCW = s.map Layer.rotate180
  rw [List.map_map]; rfl

/-- Shape 東半分と 180° 回転: 元の西半分の 180° 回転。 -/
theorem Shape.eastHalf.rotate180_comm (s : Shape) :
    Shape.eastHalf s.rotate180 = (Shape.westHalf s).rotate180 := by
  rw [Shape.rotate180_eq_map, Shape.rotate180_eq_map]
  show (s.map Layer.rotate180).map Layer.eastHalf
        = (s.map Layer.westHalf).map Layer.rotate180
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro l _
  exact Layer.eastHalf.rotate180_comm l

/-- Shape 西半分と 180° 回転: 元の東半分の 180° 回転。 -/
theorem Shape.westHalf.rotate180_comm (s : Shape) :
    Shape.westHalf s.rotate180 = (Shape.eastHalf s).rotate180 := by
  rw [Shape.rotate180_eq_map, Shape.rotate180_eq_map]
  show (s.map Layer.rotate180).map Layer.westHalf
        = (s.map Layer.eastHalf).map Layer.rotate180
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro l _
  exact Layer.westHalf.rotate180_comm l

/-- Shape `combineHalves` と 180° 回転: 引数が swap されて 180° 回転される。 -/
theorem Shape.combineHalves.rotate180_comm (a b : Shape) :
    Shape.rotate180 (Shape.combineHalves a b) =
      Shape.combineHalves (Shape.rotate180 b) (Shape.rotate180 a) := by
  rw [Shape.rotate180_eq_map (Shape.combineHalves a b), Shape.rotate180_eq_map b,
      Shape.rotate180_eq_map a]
  show (List.zipWith Layer.combineHalves a b).map Layer.rotate180
        = List.zipWith Layer.combineHalves (b.map Layer.rotate180) (a.map Layer.rotate180)
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons la rest_a iha =>
    cases b with
    | nil => rfl
    | cons lb rest_b =>
      simp only [List.zipWith_cons_cons, List.map_cons]
      exact congrArg₂ _ (Layer.combineHalves.rotate180_comm la lb) (iha rest_b)

/-- `cut` と 180° 回転: 成分が swap される（primitive の系）。 -/
theorem Shape.cut.rotate180_comm (s : Shape) :
    Shape.cut s.rotate180 =
      ((Shape.westHalf s).rotate180, (Shape.eastHalf s).rotate180) := by
  simp only [Shape.cut, Shape.eastHalf.rotate180_comm, Shape.westHalf.rotate180_comm]

/-- `halfDestroy` と 180° 回転（primitive の系）。 -/
theorem Shape.halfDestroy.rotate180_comm (s : Shape) :
    Shape.halfDestroy s.rotate180 = (Shape.westHalf s).rotate180 := by
  simp only [Shape.halfDestroy, Shape.eastHalf.rotate180_comm]

end S2IL
