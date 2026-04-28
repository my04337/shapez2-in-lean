-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Abel

/-!
# S2IL.Kernel.Transform

回転操作の中心定義。全て `def` で具体化されている（Phase C re-scaffold 済み）。

## 設計

- `Layer.rotateCW` は `Shape/Types.lean` で定義済み（`fun d => l (d - 1)`）
- `Shape.rotateCW` は `List.map Layer.rotateCW` として定義
- `rotate180` / `rotateCCW` は単一チェーン原則（§1.4）で CW の合成

## 公開 API

- `Shape.rotateCW` / `Shape.rotate180` / `Shape.rotateCCW`
- `Layer.rotate180` / `Layer.rotateCCW`
- 4 周性・レイヤ数保存（全て theorem）

## Internal

- `S2IL.Kernel.Internal.Rotate180Lemmas` — 書換系（Phase C で整備）
-/

namespace S2IL

-- ============================================================
-- Layer（rotateCW は Types.lean で定義済み）
-- ============================================================

/-- レイヤを 180° 回転。`rotateCW` の 2 回合成として定義する。 -/
def Layer.rotate180 (l : Layer) : Layer :=
  l.rotateCW.rotateCW

/-- レイヤを反時計回り 90° 回転。`rotateCW` の 3 回合成として定義する。 -/
def Layer.rotateCCW (l : Layer) : Layer :=
  l.rotateCW.rotateCW.rotateCW

@[simp] theorem Layer.rotate180_eq_rotateCW_rotateCW (l : Layer) :
    l.rotate180 = l.rotateCW.rotateCW := rfl

@[simp] theorem Layer.rotateCCW_eq_rotateCW_rotateCW_rotateCW (l : Layer) :
    l.rotateCCW = l.rotateCW.rotateCW.rotateCW := rfl

/-- Layer の 4 周性。`Layer.rotateCW` は `fun d => l (d - 1)` なので、
    4 回適用で `fun d => l (d - 4)` = `fun d => l d`。 -/
theorem Layer.rotateCW.four (l : Layer) :
    l.rotateCW.rotateCW.rotateCW.rotateCW = l := by
  funext d; simp [Layer.rotateCW]; congr 1; omega

-- ============================================================
-- Shape
-- ============================================================

/-- シェイプを時計回り 90° 回転。各レイヤに `Layer.rotateCW` を適用。 -/
def Shape.rotateCW (s : Shape) : Shape := s.map Layer.rotateCW

/-- シェイプを 180° 回転。`rotateCW` の 2 回合成として定義する。 -/
def Shape.rotate180 (s : Shape) : Shape :=
  s.rotateCW.rotateCW

/-- シェイプを反時計回り 90° 回転。`rotateCW` の 3 回合成として定義する。 -/
def Shape.rotateCCW (s : Shape) : Shape :=
  s.rotateCW.rotateCW.rotateCW

@[simp] theorem Shape.rotate180_eq_rotateCW_rotateCW (s : Shape) :
    s.rotate180 = s.rotateCW.rotateCW := rfl

@[simp] theorem Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW (s : Shape) :
    s.rotateCCW = s.rotateCW.rotateCW.rotateCW := rfl

/-- Shape の 4 周性。 -/
theorem Shape.rotateCW.four (s : Shape) :
    s.rotateCW.rotateCW.rotateCW.rotateCW = s := by
  simp only [Shape.rotateCW, List.map_map]
  have : (Layer.rotateCW ∘ Layer.rotateCW ∘ Layer.rotateCW ∘ Layer.rotateCW) = id := by
    funext l; exact Layer.rotateCW.four l
  rw [show Layer.rotateCW ∘ (Layer.rotateCW ∘ (Layer.rotateCW ∘ Layer.rotateCW))
      = Layer.rotateCW ∘ Layer.rotateCW ∘ Layer.rotateCW ∘ Layer.rotateCW from rfl,
      this, List.map_id]

/-- CW 回転はレイヤ数を保存。 -/
theorem Shape.layerCount.rotateCW (s : Shape) :
    s.rotateCW.layerCount = s.layerCount := by
  simp [Shape.rotateCW, Shape.layerCount, List.length_map]

/-- 180° 回転はレイヤ数保存（CW の系）。 -/
theorem Shape.layerCount.rotate180 (s : Shape) :
    s.rotate180.layerCount = s.layerCount := by
  simp [Shape.rotate180_eq_rotateCW_rotateCW, Shape.layerCount.rotateCW]

/-- CCW 回転はレイヤ数保存（CW の系）。 -/
theorem Shape.layerCount.rotateCCW (s : Shape) :
    s.rotateCCW.layerCount = s.layerCount := by
  simp [Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW, Shape.layerCount.rotateCW]

-- ============================================================
-- QuarterPos と Direction の rotateCW 補助
-- ============================================================

@[simp] theorem QuarterPos.rotateCW_fst (p : QuarterPos) :
    p.rotateCW.1 = p.1 := rfl

@[simp] theorem QuarterPos.rotateCW_snd (p : QuarterPos) :
    p.rotateCW.2 = p.2 + 1 := rfl

/-- レイヤ回転は `+1` 方角シフト: `(l.rotateCW) d = l (d - 1)`。 -/
@[simp] theorem Layer.rotateCW_apply (l : Layer) (d : Fin 4) :
    l.rotateCW d = l (d - 1) := rfl

/-- レイヤ回転と `+1` 方角シフトの相殺。 -/
@[simp] theorem Layer.rotateCW_apply_succ (l : Layer) (d : Fin 4) :
    l.rotateCW (d + 1) = l d := by
  show l ((d + 1) - 1) = l d
  rw [Direction.add_one_sub_one]

/-- `getQuarter` は CW 回転と可換: `s.rotateCW.getQuarter p.rotateCW = s.getQuarter p`。 -/
theorem QuarterPos.getQuarter_rotateCW (s : Shape) (p : QuarterPos) :
    QuarterPos.getQuarter s.rotateCW p.rotateCW = QuarterPos.getQuarter s p := by
  simp only [QuarterPos.getQuarter, Shape.rotateCW, List.length_map,
             QuarterPos.rotateCW_fst, QuarterPos.rotateCW_snd]
  by_cases h : p.1 < s.length
  · simp only [h, dite_true]
    rw [List.getElem_map]
    exact Layer.rotateCW_apply_succ _ _
  · simp [h]

/-- `Direction.isAdjacent` は CW 回転で不変。 -/
theorem Direction.isAdjacent_rotateCW (d1 d2 : Direction) :
    Direction.isAdjacent (d1 + 1) (d2 + 1) = Direction.isAdjacent d1 d2 := by
  simp only [Direction.isAdjacent, Direction.add_one_sub_add_one]

-- ============================================================
-- QuarterPos.rotateCW 双射と allValid 不変
-- ============================================================

/-- CW と CCW の打ち消し（左）。 -/
@[simp] theorem QuarterPos.rotateCW_rotateCCW (p : QuarterPos) :
    p.rotateCCW.rotateCW = p := by
  obtain ⟨n, d⟩ := p
  show (n, d - 1 + 1) = (n, d)
  rw [Direction.sub_one_add_one]

/-- CW と CCW の打ち消し（右）。 -/
@[simp] theorem QuarterPos.rotateCCW_rotateCW (p : QuarterPos) :
    p.rotateCW.rotateCCW = p := by
  obtain ⟨n, d⟩ := p
  show (n, d + 1 - 1) = (n, d)
  rw [Direction.add_one_sub_one]

/-- `QuarterPos.rotateCW` は単射（双射の片側）。 -/
theorem QuarterPos.rotateCW_injective : Function.Injective QuarterPos.rotateCW := by
  intro p q h
  have := congrArg QuarterPos.rotateCCW h
  simpa [QuarterPos.rotateCCW_rotateCW] using this

/-- `QuarterPos.allValid` は CW 回転で不変（`s.length` のみに依存）。 -/
theorem QuarterPos.allValid_rotateCW (s : Shape) :
    QuarterPos.allValid s.rotateCW = QuarterPos.allValid s := by
  unfold QuarterPos.allValid
  show List.flatMap (fun n => List.map (fun d => (n, d)) Direction.all)
        (List.range (List.length s.rotateCW)) = _
  rw [show s.rotateCW.length = s.length from by simp [Shape.rotateCW]]

/-- `QuarterPos.allValid` のメンバーシップは `.1 < s.length` と同値。 -/
theorem QuarterPos.mem_allValid (s : Shape) (p : QuarterPos) :
    p ∈ QuarterPos.allValid s ↔ p.1 < s.length := by
  unfold QuarterPos.allValid
  simp only [List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨n, hn, d, _, hpair⟩
    have : p.1 = n := by rw [← hpair]
    rw [this]; exact hn
  · intro hp
    refine ⟨p.1, hp, p.2, ?_, ?_⟩
    · -- p.2 ∈ Direction.all
      have h : ∀ d : Direction, d ∈ ([0, 1, 2, 3] : List Direction) := by decide
      exact h p.2
    · ext <;> rfl

/-- `QuarterPos.rotateCCW` も `.1` を保つので `mem_allValid` と整合。 -/
@[simp] theorem QuarterPos.rotateCCW_fst (p : QuarterPos) :
    p.rotateCCW.1 = p.1 := rfl

end S2IL
