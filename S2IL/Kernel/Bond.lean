-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape
import S2IL.Kernel.Transform

/-!
# S2IL.Kernel.Bond

結晶結合条件（Phase C 完了形）。
Prop/Bool 二層規約（architecture §1.11）に従い、Prop 層を primitive とし、
Bool 層 `isBonded` は `decide` 派生として定義する。

## 結合条件

| 種類 | 条件 |
|---|---|
| 同レイヤ内 | 同層 + 隣接方角（NE↔SE, SE↔SW, SW↔NW, NW↔NE）+ 両象限が結晶 |
| 上下レイヤ間 | 隣接層 + 同方角 + 両象限が結晶 |

色は問わない（[docs/shapez2/adjacency.md](../../docs/shapez2/adjacency.md)）。

## 公開 API

- `IsBondedInLayer` / `IsBondedCrossLayer` / `IsBonded`     — Prop 層（`def`）
- `isBonded`                                                 — Bool 層（`decide` 派生）
- `IsBonded.symm`                                            — 対称性
- `IsBonded.rotateCW` / `IsBonded.rotate180` / `IsBonded.rotateCCW` — 等変性

## Internal

- `S2IL.Kernel.Internal.BondImpl`        — 内部補助補題（現状空）
- `S2IL.Kernel.Internal.Rotate180Lemmas` — 180°/CCW 系（現状空）
-/

namespace S2IL

-- ============================================================
-- Prop 層 primitive 定義
-- ============================================================

/-- 同レイヤ内結合: 同層 + 隣接方角 + 両象限が結晶。 -/
def IsBondedInLayer (s : Shape) (p1 p2 : QuarterPos) : Prop :=
  p1.1 = p2.1 ∧
  Direction.isAdjacent p1.2 p2.2 = true ∧
  (QuarterPos.getQuarter s p1).IsCrystal ∧
  (QuarterPos.getQuarter s p2).IsCrystal

/-- 上下レイヤ間結合: 隣接層 + 同方角 + 両象限が結晶。 -/
def IsBondedCrossLayer (s : Shape) (p1 p2 : QuarterPos) : Prop :=
  (p1.1 + 1 = p2.1 ∨ p2.1 + 1 = p1.1) ∧
  p1.2 = p2.2 ∧
  (QuarterPos.getQuarter s p1).IsCrystal ∧
  (QuarterPos.getQuarter s p2).IsCrystal

/-- 結合関係: 同レイヤ内 ∨ 上下レイヤ間。 -/
def IsBonded (s : Shape) (p1 p2 : QuarterPos) : Prop :=
  IsBondedInLayer s p1 p2 ∨ IsBondedCrossLayer s p1 p2

-- ============================================================
-- Decidable instance
-- ============================================================

instance instDecidableIsBondedInLayer (s : Shape) (p q : QuarterPos) :
    Decidable (IsBondedInLayer s p q) := by
  unfold IsBondedInLayer; exact inferInstance

instance instDecidableIsBondedCrossLayer (s : Shape) (p q : QuarterPos) :
    Decidable (IsBondedCrossLayer s p q) := by
  unfold IsBondedCrossLayer; exact inferInstance

instance instDecidableIsBonded (s : Shape) (p q : QuarterPos) :
    Decidable (IsBonded s p q) := by
  unfold IsBonded; exact inferInstance

-- ============================================================
-- Bool 層派生（§1.11 規約）
-- ============================================================

/-- Bool 層: `isBonded := decide ∘ IsBonded`。 -/
def isBonded (s : Shape) (p q : QuarterPos) : Bool := decide (IsBonded s p q)

/-- Prop/Bool 橋渡し（自動）。 -/
@[simp] theorem isBonded.iff (s : Shape) (p q : QuarterPos) :
    isBonded s p q = true ↔ IsBonded s p q := by
  simp [isBonded]

-- ============================================================
-- 対称性
-- ============================================================

theorem IsBondedInLayer.symm {s : Shape} {p q : QuarterPos}
    (h : IsBondedInLayer s p q) : IsBondedInLayer s q p := by
  obtain ⟨hL, hAdj, hC1, hC2⟩ := h
  refine ⟨hL.symm, ?_, hC2, hC1⟩
  rw [Direction.isAdjacent_symm]; exact hAdj

theorem IsBondedCrossLayer.symm {s : Shape} {p q : QuarterPos}
    (h : IsBondedCrossLayer s p q) : IsBondedCrossLayer s q p := by
  obtain ⟨hN, hD, hC1, hC2⟩ := h
  exact ⟨hN.symm, hD.symm, hC2, hC1⟩

theorem IsBonded.symm {s : Shape} {p q : QuarterPos}
    (h : IsBonded s p q) : IsBonded s q p := by
  rcases h with h | h
  · exact .inl h.symm
  · exact .inr h.symm

-- ============================================================
-- CW 等変性
-- ============================================================

theorem IsBondedInLayer.rotateCW (s : Shape) (p q : QuarterPos) :
    IsBondedInLayer s.rotateCW p.rotateCW q.rotateCW ↔ IsBondedInLayer s p q := by
  unfold IsBondedInLayer
  rw [QuarterPos.getQuarter_rotateCW, QuarterPos.getQuarter_rotateCW]
  simp only [QuarterPos.rotateCW_fst, QuarterPos.rotateCW_snd,
             Direction.isAdjacent_rotateCW]

theorem IsBondedCrossLayer.rotateCW (s : Shape) (p q : QuarterPos) :
    IsBondedCrossLayer s.rotateCW p.rotateCW q.rotateCW ↔ IsBondedCrossLayer s p q := by
  unfold IsBondedCrossLayer
  rw [QuarterPos.getQuarter_rotateCW, QuarterPos.getQuarter_rotateCW]
  simp only [QuarterPos.rotateCW_fst, QuarterPos.rotateCW_snd]
  have hd : p.2 + 1 = q.2 + 1 ↔ p.2 = q.2 := by
    constructor
    · intro h
      have h' : p.2 + 1 - 1 = q.2 + 1 - 1 := by rw [h]
      have e1 : p.2 + 1 - 1 = p.2 := by
        ext; simp [Fin.sub_def, Fin.add_def]; omega
      have e2 : q.2 + 1 - 1 = q.2 := by
        ext; simp [Fin.sub_def, Fin.add_def]; omega
      rw [e1, e2] at h'; exact h'
    · intro h; rw [h]
  rw [hd]

theorem IsBonded.rotateCW (s : Shape) (p q : QuarterPos) :
    IsBonded s.rotateCW p.rotateCW q.rotateCW ↔ IsBonded s p q := by
  unfold IsBonded
  rw [IsBondedInLayer.rotateCW, IsBondedCrossLayer.rotateCW]

-- ============================================================
-- 180° / CCW 等変性（§1.4 単一チェーン原則）
-- ============================================================

theorem IsBonded.rotate180 (s : Shape) (p q : QuarterPos) :
    IsBonded s.rotate180 p.rotateCW.rotateCW q.rotateCW.rotateCW ↔ IsBonded s p q := by
  simp [Shape.rotate180_eq_rotateCW_rotateCW, IsBonded.rotateCW]

theorem IsBonded.rotateCCW (s : Shape) (p q : QuarterPos) :
    IsBonded s.rotateCCW p.rotateCW.rotateCW.rotateCW q.rotateCW.rotateCW.rotateCW ↔
      IsBonded s p q := by
  simp [Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW, IsBonded.rotateCW]

end S2IL
