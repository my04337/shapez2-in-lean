-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel
import S2IL.Operations.Gravity
import S2IL.Operations.Shatter

/-!
# S2IL.Operations.Cutter

切断機 (A-2-1 + B-4-2)（Phase C re-scaffold 済み）。
Option 追放（§1.9）と合成化（§8.1.4）適用済み。

## 公開 API

- `Layer.eastHalf` / `Layer.westHalf` / `Layer.combineHalves` — Layer 基本操作
- `Shape.eastHalf` / `Shape.westHalf` / `Shape.combineHalves` — Shape primitive（E/W axiom）
- `Shape.cut : Shape → Shape × Shape` — 全関数、`eastHalf` + `westHalf` の合成 `def`
- `Shape.halfDestroy : Shape → Shape` — 全関数、`eastHalf` の別名 `def`
- 構造的恒等式と **180° 回転等変性**

## E/W 参照操作（§1.4.1）

primitive: `eastHalf` / `westHalf` / `combineHalves` の 3 操作のみ。
`cut` / `halfDestroy` は `def` 合成。`rotate180_comm` は primitive の系で導出。
-/

namespace S2IL

-- ============================================================
-- Layer level
-- ============================================================

axiom Layer.eastHalf : Layer → Layer
axiom Layer.westHalf : Layer → Layer
axiom Layer.combineHalves : Layer → Layer → Layer

axiom Layer.combineHalves.eastHalf_westHalf (l : Layer) :
    Layer.combineHalves (Layer.eastHalf l) (Layer.westHalf l) = l

-- ============================================================
-- Shape level — primitive axioms
-- ============================================================

axiom Shape.eastHalf : Shape → Shape
axiom Shape.westHalf : Shape → Shape
axiom Shape.combineHalves : Shape → Shape → Shape

axiom Shape.combineHalves.eastHalf_westHalf (s : Shape) :
    Shape.combineHalves (Shape.eastHalf s) (Shape.westHalf s) = s

axiom Shape.combineHalves.self (s : Shape) :
    Shape.combineHalves s s = s

-- ============================================================
-- Shape level — derived defs（§8.1.4 合成化）
-- ============================================================

/-- 切断: 東半分と西半分のペア（全関数）。 -/
noncomputable def Shape.cut (s : Shape) : Shape × Shape :=
  (Shape.eastHalf s, Shape.westHalf s)

/-- 半壊: 東半分を残す（全関数）。 -/
noncomputable def Shape.halfDestroy (s : Shape) : Shape :=
  Shape.eastHalf s

theorem Shape.halfDestroy.eq_cut_fst (s : Shape) :
    Shape.halfDestroy s = (Shape.cut s).1 := rfl

-- ============================================================
-- Equivariance (rotate180 only; CW / CCW do NOT hold)
-- ============================================================

/-- 東半分と 180° 回転: 元の西半分の 180° 回転。 -/
axiom Shape.eastHalf.rotate180_comm (s : Shape) :
    Shape.eastHalf s.rotate180 = (Shape.westHalf s).rotate180

/-- 西半分と 180° 回転: 元の東半分の 180° 回転。 -/
axiom Shape.westHalf.rotate180_comm (s : Shape) :
    Shape.westHalf s.rotate180 = (Shape.eastHalf s).rotate180

/-- `combineHalves` と 180° 回転: 入力が swap されて 180° 回転される
    （E↔W が swap されるため）。 -/
axiom Shape.combineHalves.rotate180_comm (a b : Shape) :
    (Shape.combineHalves a b).rotate180 =
      Shape.combineHalves b.rotate180 a.rotate180

/-- `cut` と 180° 回転: 成分が swap される（theorem、primitive の系）。 -/
theorem Shape.cut.rotate180_comm (s : Shape) :
    Shape.cut s.rotate180 =
      ((Shape.westHalf s).rotate180, (Shape.eastHalf s).rotate180) := by
  simp only [Shape.cut, Shape.eastHalf.rotate180_comm, Shape.westHalf.rotate180_comm]

/-- `halfDestroy` と 180° 回転（theorem、primitive の系）。 -/
theorem Shape.halfDestroy.rotate180_comm (s : Shape) :
    Shape.halfDestroy s.rotate180 = (Shape.westHalf s).rotate180 := by
  simp only [Shape.halfDestroy, Shape.eastHalf.rotate180_comm]

end S2IL
