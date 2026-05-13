-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel
import Mathlib.Logic.Relation

/-!
# S2IL.Operations.Settled.Defs

Settled (安定状態、B-3) の構造的判定。
-/

namespace S2IL

open Relation

/-- 接地接触: 同方角の上下隣接（両非空）または同層隣接方角（両非空・両非ピン）。 -/
def IsContact (s : Shape) (a b : QuarterPos) : Prop :=
  (a.2 = b.2 ∧ (a.1 + 1 = b.1 ∨ b.1 + 1 = a.1) ∧
    ¬ (QuarterPos.getQuarter s a).isEmpty ∧ ¬ (QuarterPos.getQuarter s b).isEmpty)
  ∨
  (a.1 = b.1 ∧ Direction.isAdjacent a.2 b.2 = true ∧
    ¬ (QuarterPos.getQuarter s a).isEmpty ∧ ¬ (QuarterPos.getQuarter s b).isEmpty ∧
    QuarterPos.getQuarter s a ≠ Quarter.pin ∧ QuarterPos.getQuarter s b ≠ Quarter.pin)

/-- 上方向接地接触: 接触かつ `a.layer ≤ b.layer`。
垂直接触では下から上への支持のみを許し、同層接触はそのまま許す。 -/
def IsUpwardGroundingContact (s : Shape) (a b : QuarterPos) : Prop :=
  IsContact s a b ∧ a.1 ≤ b.1

/-- 構造結合: 両端 `canFormBond` ∧ 隣接（同層方角隣接 ∨ 上下同方角）。
    [`docs/shapez2/falling.md §2.2`] に従う。
    結晶限定の `IsCrystalBonded` (Kernel) と異なり、種別・色を問わず結合能力で判定する。 -/
def IsStructurallyBonded (s : Shape) (a b : QuarterPos) : Prop :=
  ((a.1 = b.1 ∧ Direction.isAdjacent a.2 b.2 = true) ∨
    (a.2 = b.2 ∧ (a.1 + 1 = b.1 ∨ b.1 + 1 = a.1))) ∧
  (QuarterPos.getQuarter s a).canFormBond = true ∧
  (QuarterPos.getQuarter s b).canFormBond = true

/-- 接地エッジ: 上方向接地接触 または 構造結合 (`IsStructurallyBonded`)。
    [`docs/shapez2/falling.md §4.2`] に従う。 -/
def IsGroundingEdge (s : Shape) (a b : QuarterPos) : Prop :=
  IsUpwardGroundingContact s a b ∨ IsStructurallyBonded s a b

namespace IsContact

/-- 端点の象限値が変わらなければ、接地接触は保存される。 -/
theorem of_getQuarter_eq {s t : Shape} {a b : QuarterPos}
    (ha : QuarterPos.getQuarter t a = QuarterPos.getQuarter s a)
    (hb : QuarterPos.getQuarter t b = QuarterPos.getQuarter s b)
    (h : IsContact s a b) : IsContact t a b := by
  simpa only [IsContact, ha, hb] using h

end IsContact

namespace IsUpwardGroundingContact

/-- 端点の象限値が変わらなければ、上方向接地接触は保存される。 -/
theorem of_getQuarter_eq {s t : Shape} {a b : QuarterPos}
    (ha : QuarterPos.getQuarter t a = QuarterPos.getQuarter s a)
    (hb : QuarterPos.getQuarter t b = QuarterPos.getQuarter s b)
    (h : IsUpwardGroundingContact s a b) : IsUpwardGroundingContact t a b := by
  simpa only [IsUpwardGroundingContact] using
    And.intro (IsContact.of_getQuarter_eq ha hb h.1) h.2

end IsUpwardGroundingContact

namespace IsStructurallyBonded

/-- 端点の象限値が変わらなければ、構造結合は保存される。 -/
theorem of_getQuarter_eq {s t : Shape} {a b : QuarterPos}
    (ha : QuarterPos.getQuarter t a = QuarterPos.getQuarter s a)
    (hb : QuarterPos.getQuarter t b = QuarterPos.getQuarter s b)
    (h : IsStructurallyBonded s a b) : IsStructurallyBonded t a b := by
  simpa only [IsStructurallyBonded, ha, hb] using h

end IsStructurallyBonded

namespace IsStructurallyBonded

/-- 構造結合は対称関係。隣接条件と `canFormBond` 条件が共に対称。 -/
theorem symm {s : Shape} {a b : QuarterPos}
    (h : IsStructurallyBonded s a b) : IsStructurallyBonded s b a := by
  obtain ⟨hadj, hcfa, hcfb⟩ := h
  refine ⟨?_, hcfb, hcfa⟩
  rcases hadj with ⟨hl, hd⟩ | ⟨hd, hl⟩
  · exact Or.inl ⟨hl.symm, by
      have : Direction.isAdjacent b.2 a.2 = true := by
        unfold Direction.isAdjacent at hd ⊢
        rw [Bool.or_comm]; exact hd
      exact this⟩
  · refine Or.inr ⟨hd.symm, ?_⟩
    rcases hl with h1 | h1
    · exact Or.inr h1
    · exact Or.inl h1

end IsStructurallyBonded

namespace IsGroundingEdge

/-- 端点の象限値が変わらなければ、接地エッジは保存される。 -/
theorem of_getQuarter_eq {s t : Shape} {a b : QuarterPos}
    (ha : QuarterPos.getQuarter t a = QuarterPos.getQuarter s a)
    (hb : QuarterPos.getQuarter t b = QuarterPos.getQuarter s b)
    (h : IsGroundingEdge s a b) : IsGroundingEdge t a b := by
  rcases h with h | h
  · exact Or.inl (IsUpwardGroundingContact.of_getQuarter_eq ha hb h)
  · exact Or.inr (IsStructurallyBonded.of_getQuarter_eq ha hb h)

end IsGroundingEdge

/-- 接地: layer 0 の非空象限から接地エッジで到達可能。 -/
def IsGrounded (s : Shape) (p : QuarterPos) : Prop :=
  ∃ p₀ : QuarterPos, p₀.1 = 0 ∧ ¬ (QuarterPos.getQuarter s p₀).isEmpty ∧
    ReflTransGen (IsGroundingEdge s) p₀ p

/-- 安定: 全有効非空象限が接地している。 -/
def IsSettled (s : Shape) : Prop :=
  ∀ p : QuarterPos, p ∈ QuarterPos.allValid s →
    ¬ (QuarterPos.getQuarter s p).isEmpty → IsGrounded s p

namespace IsGroundingEdge

/-- 接地エッジの右端は非空である。 -/
theorem right_nonempty {s : Shape} {a b : QuarterPos}
    (h : IsGroundingEdge s a b) :
    ¬ (QuarterPos.getQuarter s b).isEmpty := by
  rcases h with hContact | hBond
  · rcases hContact.1 with hVertical | hHorizontal
    · exact hVertical.2.2.2
    · exact hHorizontal.2.2.2.1
  · exact Quarter.not_isEmpty_of_canFormBond hBond.2.2

end IsGroundingEdge

namespace IsGrounded

/-- 接地している位置は非空である。 -/
theorem nonempty {s : Shape} {p : QuarterPos} (h : IsGrounded s p) :
    ¬ (QuarterPos.getQuarter s p).isEmpty := by
  obtain ⟨_p₀, _hLayer, hNonempty, hPath⟩ := h
  induction hPath with
  | refl => exact hNonempty
  | tail _ hedge _ => exact IsGroundingEdge.right_nonempty hedge

end IsGrounded

noncomputable instance instDecidableIsSettled : DecidablePred IsSettled :=
  Classical.decPred _

/-- `IsSettled` の Bool 版（派生）。 -/
noncomputable def isSettled (s : Shape) : Bool := decide (IsSettled s)

/-- 橋渡し。 -/
theorem isSettled.iff (s : Shape) : isSettled s = true ↔ IsSettled s := by
  simp [isSettled]

end S2IL