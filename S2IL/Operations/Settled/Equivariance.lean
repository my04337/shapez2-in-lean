-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Settled.Defs

/-!
# S2IL.Operations.Settled.Equivariance

接地・安定述語の CW 等変性と 180° / CCW の 1 行系。
-/

namespace S2IL

open Relation

/-- `IsContact` は CW 回転で保存される。 -/
theorem IsContact.rotateCW (s : Shape) (a b : QuarterPos) :
    IsContact s.rotateCW a.rotateCW b.rotateCW ↔ IsContact s a b := by
  unfold IsContact
  simp only [QuarterPos.rotateCW_fst, QuarterPos.rotateCW_snd]
  rw [QuarterPos.getQuarter_rotateCW, QuarterPos.getQuarter_rotateCW]
  have hd : a.2 + 1 = b.2 + 1 ↔ a.2 = b.2 := Direction.add_one_inj
  rw [hd, Direction.isAdjacent_rotateCW]

/-- `IsUpwardGroundingContact` は CW 回転で保存される。 -/
theorem IsUpwardGroundingContact.rotateCW (s : Shape) (a b : QuarterPos) :
    IsUpwardGroundingContact s.rotateCW a.rotateCW b.rotateCW ↔
      IsUpwardGroundingContact s a b := by
  unfold IsUpwardGroundingContact
  simp only [QuarterPos.rotateCW_fst, IsContact.rotateCW]

/-- `IsStructurallyBonded` は CW 回転で保存される。 -/
theorem IsStructurallyBonded.rotateCW (s : Shape) (a b : QuarterPos) :
    IsStructurallyBonded s.rotateCW a.rotateCW b.rotateCW ↔
      IsStructurallyBonded s a b := by
  unfold IsStructurallyBonded
  simp only [QuarterPos.rotateCW_fst, QuarterPos.rotateCW_snd]
  rw [QuarterPos.getQuarter_rotateCW, QuarterPos.getQuarter_rotateCW]
  have hd : a.2 + 1 = b.2 + 1 ↔ a.2 = b.2 := Direction.add_one_inj
  rw [hd, Direction.isAdjacent_rotateCW]

/-- `IsGroundingEdge` は CW 回転で保存される。 -/
theorem IsGroundingEdge.rotateCW (s : Shape) (a b : QuarterPos) :
    IsGroundingEdge s.rotateCW a.rotateCW b.rotateCW ↔ IsGroundingEdge s a b := by
  unfold IsGroundingEdge
  rw [IsUpwardGroundingContact.rotateCW, IsStructurallyBonded.rotateCW]

private theorem groundingEdge_reflTransGen_rotateCW (s : Shape) (p q : QuarterPos) :
    ReflTransGen (IsGroundingEdge s.rotateCW) p.rotateCW q.rotateCW ↔
      ReflTransGen (IsGroundingEdge s) p q := by
  constructor
  · intro h
    have hlift :
        ReflTransGen (IsGroundingEdge s) p.rotateCW.rotateCCW q.rotateCW.rotateCCW :=
      h.lift QuarterPos.rotateCCW (fun a b hab => by
        have key : IsGroundingEdge s.rotateCW a.rotateCCW.rotateCW b.rotateCCW.rotateCW
                    ↔ IsGroundingEdge s a.rotateCCW b.rotateCCW :=
          IsGroundingEdge.rotateCW s a.rotateCCW b.rotateCCW
        exact key.mp (by simpa [QuarterPos.rotateCW_rotateCCW] using hab))
    simpa [QuarterPos.rotateCCW_rotateCW] using hlift
  · intro h
    exact h.lift QuarterPos.rotateCW (fun a b hab =>
      (IsGroundingEdge.rotateCW s a b).mpr hab)

namespace IsGrounded

theorem rotateCW {s : Shape} {p : QuarterPos} (h : IsGrounded s p) :
    IsGrounded s.rotateCW p.rotateCW := by
  obtain ⟨p₀, hl, hne, hpath⟩ := h
  refine ⟨p₀.rotateCW, ?_, ?_, ?_⟩
  · simp [QuarterPos.rotateCW_fst, hl]
  · rw [QuarterPos.getQuarter_rotateCW]; exact hne
  · exact (groundingEdge_reflTransGen_rotateCW s p₀ p).mpr hpath

end IsGrounded

namespace IsSettled

/-- `IsSettled` は CW 回転で保存される。 -/
theorem rotateCW {s : Shape} (h : IsSettled s) : IsSettled s.rotateCW := by
  intro p hp_valid hp_ne
  rw [QuarterPos.allValid_rotateCW] at hp_valid
  have hp_eq : p = p.rotateCCW.rotateCW := by
    rw [QuarterPos.rotateCW_rotateCCW]
  rw [hp_eq]
  apply IsGrounded.rotateCW
  apply h
  · rw [QuarterPos.mem_allValid] at hp_valid ⊢
    show p.rotateCCW.1 < s.length
    rw [QuarterPos.rotateCCW_fst]
    exact hp_valid
  · rw [hp_eq] at hp_ne
    rw [QuarterPos.getQuarter_rotateCW] at hp_ne
    exact hp_ne

/-- `IsSettled` は 180° 回転で保存される（CW の系）。 -/
theorem rotate180 {s : Shape} (h : IsSettled s) : IsSettled s.rotate180 := by
  rw [Shape.rotate180_eq_rotateCW_rotateCW]
  exact rotateCW (rotateCW h)

/-- `IsSettled` は CCW 回転で保存される（CW の系）。 -/
theorem rotateCCW {s : Shape} (h : IsSettled s) : IsSettled s.rotateCCW := by
  rw [Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW]
  exact rotateCW (rotateCW (rotateCW h))

end IsSettled

end S2IL