-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Settled

/-!
# Internal: grounding Bool/Prop bridges

このファイルは `S2IL.Operations.Gravity` namespace の補助補題を集める。
**外部モジュール（S2IL/Operations/Gravity.lean, S2IL/Operations/Gravity/*.lean 以外）からは import 禁止**。
-/

namespace S2IL

namespace Gravity.Internal

/-- 接地 seed / closure 計算用の非空判定。Prop 仕様の派生 Bool。 -/
def groundingNonempty (s : Shape) (p : QuarterPos) : Bool :=
  !(QuarterPos.getQuarter s p).isEmpty

/-- `groundingNonempty` と非空 Prop の bridge。 -/
theorem groundingNonempty_iff (s : Shape) (p : QuarterPos) :
    groundingNonempty s p = true ↔ ¬ (QuarterPos.getQuarter s p).isEmpty := by
  simp [groundingNonempty]

/-- `IsContact` の実行可能 Bool 版。Prop 層を正本とする派生ビュー。 -/
def isContactBool (s : Shape) (a b : QuarterPos) : Bool :=
  ((a.2 == b.2) && ((a.1 + 1 == b.1) || (b.1 + 1 == a.1)) &&
    groundingNonempty s a && groundingNonempty s b) ||
  ((a.1 == b.1) && Direction.isAdjacent a.2 b.2 &&
    groundingNonempty s a && groundingNonempty s b &&
    decide (QuarterPos.getQuarter s a ≠ Quarter.pin) &&
    decide (QuarterPos.getQuarter s b ≠ Quarter.pin))

/-- `isContactBool` と `IsContact` の bridge。 -/
theorem isContactBool_iff (s : Shape) (a b : QuarterPos) :
    isContactBool s a b = true ↔ IsContact s a b := by
  simp [isContactBool, IsContact, groundingNonempty]
  constructor
  · intro h
    rcases h with hVertical | hHorizontal
    · rcases hVertical with ⟨⟨⟨hDir, hLayer⟩, hA⟩, hB⟩
      exact Or.inl ⟨hDir, hLayer, hA, hB⟩
    · rcases hHorizontal with ⟨⟨⟨⟨⟨hLayer, hAdj⟩, hA⟩, hB⟩, hPinA⟩, hPinB⟩
      exact Or.inr ⟨hLayer, hAdj, hA, hB,
        hPinA, hPinB⟩
  · intro h
    rcases h with hVertical | hHorizontal
    · rcases hVertical with ⟨hDir, hLayer, hA, hB⟩
      exact Or.inl ⟨⟨⟨hDir, hLayer⟩, hA⟩, hB⟩
    · rcases hHorizontal with ⟨hLayer, hAdj, hA, hB, hPinA, hPinB⟩
      exact Or.inr ⟨⟨⟨⟨⟨hLayer, hAdj⟩, hA⟩, hB⟩,
        hPinA⟩, hPinB⟩

/-- `IsUpwardGroundingContact` の実行可能 Bool 版。Prop 層を正本とする派生ビュー。 -/
def isUpwardGroundingContactBool (s : Shape) (a b : QuarterPos) : Bool :=
  isContactBool s a b && decide (a.1 ≤ b.1)

/-- `isUpwardGroundingContactBool` と `IsUpwardGroundingContact` の bridge。 -/
theorem isUpwardGroundingContactBool_iff (s : Shape) (a b : QuarterPos) :
    isUpwardGroundingContactBool s a b = true ↔ IsUpwardGroundingContact s a b := by
  simp [isUpwardGroundingContactBool, IsUpwardGroundingContact, isContactBool_iff]

/-- `IsStructurallyBonded` の実行可能 Bool 版。Prop 層を正本とする派生ビュー。 -/
def isStructurallyBondedBool (s : Shape) (a b : QuarterPos) : Bool :=
  (((a.1 == b.1) && Direction.isAdjacent a.2 b.2) ||
    ((a.2 == b.2) && ((a.1 + 1 == b.1) || (b.1 + 1 == a.1)))) &&
  (QuarterPos.getQuarter s a).canFormBond && (QuarterPos.getQuarter s b).canFormBond

/-- `isStructurallyBondedBool` と `IsStructurallyBonded` の bridge。 -/
theorem isStructurallyBondedBool_iff (s : Shape) (a b : QuarterPos) :
    isStructurallyBondedBool s a b = true ↔ IsStructurallyBonded s a b := by
  simp [isStructurallyBondedBool, IsStructurallyBonded]
  constructor
  · intro h
    rcases h with ⟨⟨hAdj, hA⟩, hB⟩
    exact ⟨hAdj, hA, hB⟩
  · intro h
    rcases h with ⟨hAdj, hA, hB⟩
    exact ⟨⟨hAdj, hA⟩, hB⟩

/-- `IsGroundingEdge` の実行可能 Bool 版。Prop 層を正本とする派生ビュー。 -/
def isGroundingEdgeBool (s : Shape) (a b : QuarterPos) : Bool :=
  isUpwardGroundingContactBool s a b || isStructurallyBondedBool s a b

/-- `isGroundingEdgeBool` と `IsGroundingEdge` の bridge。 -/
theorem isGroundingEdgeBool_iff (s : Shape) (a b : QuarterPos) :
    isGroundingEdgeBool s a b = true ↔ IsGroundingEdge s a b := by
  simp [isGroundingEdgeBool, IsGroundingEdge, isUpwardGroundingContactBool_iff,
    isStructurallyBondedBool_iff]

/-- `getQuarter` が非空なら、その位置は有効範囲内にある。 -/
theorem getQuarter_nonempty_mem_allValid {s : Shape} {p : QuarterPos}
    (h : ¬ (QuarterPos.getQuarter s p).isEmpty) : p ∈ QuarterPos.allValid s := by
  rw [QuarterPos.mem_allValid]
  by_contra hValid
  have hEmpty : QuarterPos.getQuarter s p = Quarter.empty := by
    simp [QuarterPos.getQuarter, hValid]
  simp [hEmpty, Quarter.isEmpty] at h

/-- `getQuarter` が結合可能なら、その位置は有効範囲内にある。 -/
theorem getQuarter_canFormBond_mem_allValid {s : Shape} {p : QuarterPos}
    (h : (QuarterPos.getQuarter s p).canFormBond = true) : p ∈ QuarterPos.allValid s := by
  rw [QuarterPos.mem_allValid]
  by_contra hValid
  have hEmpty : QuarterPos.getQuarter s p = Quarter.empty := by
    simp [QuarterPos.getQuarter, hValid]
  simp [hEmpty, Quarter.canFormBond] at h

namespace IsContact

/-- 接地接触の右端は有効位置である。 -/
theorem right_mem_allValid {s : Shape} {a b : QuarterPos}
    (h : IsContact s a b) : b ∈ QuarterPos.allValid s := by
  rcases h with hVertical | hHorizontal
  · exact getQuarter_nonempty_mem_allValid hVertical.2.2.2
  · exact getQuarter_nonempty_mem_allValid hHorizontal.2.2.2.1

end IsContact

namespace IsStructurallyBonded

/-- 構造結合の右端は有効位置である。 -/
theorem right_mem_allValid {s : Shape} {a b : QuarterPos}
    (h : IsStructurallyBonded s a b) : b ∈ QuarterPos.allValid s :=
  getQuarter_canFormBond_mem_allValid h.2.2

end IsStructurallyBonded

namespace IsGroundingEdge

/-- 接地エッジの右端は有効位置である。 -/
theorem right_mem_allValid {s : Shape} {a b : QuarterPos}
    (h : IsGroundingEdge s a b) : b ∈ QuarterPos.allValid s := by
  rcases h with hContact | hBond
  · exact IsContact.right_mem_allValid hContact.1
  · exact IsStructurallyBonded.right_mem_allValid hBond

end IsGroundingEdge

end Gravity.Internal

end S2IL