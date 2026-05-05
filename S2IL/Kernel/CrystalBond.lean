-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape
import S2IL.Kernel.Transform

/-!
# S2IL.Kernel.CrystalBond

**結晶結合（Crystalline Bond, [docs/shapez2/crystal-shatter.md](../../docs/shapez2/crystal-shatter.md)）**
の判定条件。
Prop/Bool 二層規約（architecture §1.11）に従い、Prop 層を primitive とし、
Bool 層 `isCrystalBonded` は `decide` 派生として定義する。

> ⚠ **構造結合（Structural Bond, `canFormBond` ペア）とは別概念**:
> 重力・着地系で使う「構造結合」は [S2IL.Operations.Settled](../Operations/Settled.lean)
> の `IsStructurallyBonded` 側を参照すること。本ファイルは結晶限定の crystal-shatter
> 用結合のみを扱う。識別子に `Crystal` プレフィクスを付けて取り違いを構文レベルで防ぐ。

## 結晶結合条件

| 種類 | 条件 |
|---|---|
| 同レイヤ内 | 同層 + 隣接方角（NE↔SE, SE↔SW, SW↔NW, NW↔NE）+ 両象限が結晶 |
| 上下レイヤ間 | 隣接層 + 同方角 + 両象限が結晶 |

色は問わない（[docs/shapez2/adjacency.md](../../docs/shapez2/adjacency.md)）。

## 公開 API

- `IsCrystalBondedInLayer` / `IsCrystalBondedCrossLayer` / `IsCrystalBonded`     — Prop 層（`def`）
- `isCrystalBonded`                                                 — Bool 層（`decide` 派生）
- `IsCrystalBonded.symm`                                            — 対称性
- `IsCrystalBonded.rotateCW` / `IsCrystalBonded.rotate180` / `IsCrystalBonded.rotateCCW` — 等変性

## Internal

- `S2IL.Kernel.Internal.CrystalBondImpl`        — 内部補助補題（現状空）
- `S2IL.Kernel.Internal.Rotate180Lemmas` — 180°/CCW 系（現状空）
-/

namespace S2IL

-- ============================================================
-- Prop 層 primitive 定義
-- ============================================================

/-- 同レイヤ内結晶結合: 同層 + 隣接方角 + 両象限が結晶。 -/
def IsCrystalBondedInLayer (s : Shape) (p1 p2 : QuarterPos) : Prop :=
  p1.1 = p2.1 ∧
  Direction.isAdjacent p1.2 p2.2 = true ∧
  (QuarterPos.getQuarter s p1).IsCrystal ∧
  (QuarterPos.getQuarter s p2).IsCrystal

/-- 上下レイヤ間結晶結合: 隣接層 + 同方角 + 両象限が結晶。 -/
def IsCrystalBondedCrossLayer (s : Shape) (p1 p2 : QuarterPos) : Prop :=
  (p1.1 + 1 = p2.1 ∨ p2.1 + 1 = p1.1) ∧
  p1.2 = p2.2 ∧
  (QuarterPos.getQuarter s p1).IsCrystal ∧
  (QuarterPos.getQuarter s p2).IsCrystal

/-- 結晶結合関係: 同レイヤ内 ∨ 上下レイヤ間。 -/
def IsCrystalBonded (s : Shape) (p1 p2 : QuarterPos) : Prop :=
  IsCrystalBondedInLayer s p1 p2 ∨ IsCrystalBondedCrossLayer s p1 p2

-- ============================================================
-- Decidable instance
-- ============================================================

instance instDecidableIsCrystalBondedInLayer (s : Shape) (p q : QuarterPos) :
    Decidable (IsCrystalBondedInLayer s p q) := by
  unfold IsCrystalBondedInLayer; exact inferInstance

instance instDecidableIsCrystalBondedCrossLayer (s : Shape) (p q : QuarterPos) :
    Decidable (IsCrystalBondedCrossLayer s p q) := by
  unfold IsCrystalBondedCrossLayer; exact inferInstance

instance instDecidableIsCrystalBonded (s : Shape) (p q : QuarterPos) :
    Decidable (IsCrystalBonded s p q) := by
  unfold IsCrystalBonded; exact inferInstance

-- ============================================================
-- Bool 層派生（§1.11 規約）
-- ============================================================

/-- Bool 層: `isCrystalBonded := decide ∘ IsCrystalBonded`。 -/
def isCrystalBonded (s : Shape) (p q : QuarterPos) : Bool := decide (IsCrystalBonded s p q)

/-- Prop/Bool 橋渡し（自動）。 -/
@[simp] theorem isCrystalBonded.iff (s : Shape) (p q : QuarterPos) :
    isCrystalBonded s p q = true ↔ IsCrystalBonded s p q := by
  simp [isCrystalBonded]

-- ============================================================
-- 対称性
-- ============================================================

theorem IsCrystalBondedInLayer.symm {s : Shape} {p q : QuarterPos}
    (h : IsCrystalBondedInLayer s p q) : IsCrystalBondedInLayer s q p := by
  obtain ⟨hL, hAdj, hC1, hC2⟩ := h
  refine ⟨hL.symm, ?_, hC2, hC1⟩
  rw [Direction.isAdjacent_symm]; exact hAdj

theorem IsCrystalBondedCrossLayer.symm {s : Shape} {p q : QuarterPos}
    (h : IsCrystalBondedCrossLayer s p q) : IsCrystalBondedCrossLayer s q p := by
  obtain ⟨hN, hD, hC1, hC2⟩ := h
  exact ⟨hN.symm, hD.symm, hC2, hC1⟩

theorem IsCrystalBonded.symm {s : Shape} {p q : QuarterPos}
    (h : IsCrystalBonded s p q) : IsCrystalBonded s q p := by
  rcases h with h | h
  · exact .inl h.symm
  · exact .inr h.symm

-- ============================================================
-- CW 等変性
-- ============================================================

theorem IsCrystalBondedInLayer.rotateCW (s : Shape) (p q : QuarterPos) :
    IsCrystalBondedInLayer s.rotateCW p.rotateCW q.rotateCW ↔ IsCrystalBondedInLayer s p q := by
  unfold IsCrystalBondedInLayer
  rw [QuarterPos.getQuarter_rotateCW, QuarterPos.getQuarter_rotateCW]
  simp only [QuarterPos.rotateCW_fst, QuarterPos.rotateCW_snd,
             Direction.isAdjacent_rotateCW]

theorem IsCrystalBondedCrossLayer.rotateCW (s : Shape) (p q : QuarterPos) :
    IsCrystalBondedCrossLayer s.rotateCW p.rotateCW q.rotateCW ↔ IsCrystalBondedCrossLayer s p q := by
  unfold IsCrystalBondedCrossLayer
  rw [QuarterPos.getQuarter_rotateCW, QuarterPos.getQuarter_rotateCW]
  simp only [QuarterPos.rotateCW_fst, QuarterPos.rotateCW_snd, Direction.add_one_inj]

theorem IsCrystalBonded.rotateCW (s : Shape) (p q : QuarterPos) :
    IsCrystalBonded s.rotateCW p.rotateCW q.rotateCW ↔ IsCrystalBonded s p q := by
  unfold IsCrystalBonded
  rw [IsCrystalBondedInLayer.rotateCW, IsCrystalBondedCrossLayer.rotateCW]

-- ============================================================
-- 180° / CCW 等変性（§1.4 単一チェーン原則）
-- ============================================================

theorem IsCrystalBonded.rotate180 (s : Shape) (p q : QuarterPos) :
    IsCrystalBonded s.rotate180 p.rotateCW.rotateCW q.rotateCW.rotateCW ↔ IsCrystalBonded s p q := by
  simp [Shape.rotate180_eq_rotateCW_rotateCW, IsCrystalBonded.rotateCW]

theorem IsCrystalBonded.rotateCCW (s : Shape) (p q : QuarterPos) :
    IsCrystalBonded s.rotateCCW p.rotateCW.rotateCW.rotateCW q.rotateCW.rotateCW.rotateCW ↔
      IsCrystalBonded s p q := by
  simp [Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW, IsCrystalBonded.rotateCW]

end S2IL
