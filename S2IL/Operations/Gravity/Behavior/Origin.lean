-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity.Behavior.Grounded

/-!
# S2IL.Operations.Gravity.Behavior.Origin

`waveStep` 後の非空/floating 位置がどこから来たかを分解する。
-/

namespace S2IL

namespace Shape

/-- `waveStep` 後の非空セルは、旧静止セルまたは旧 floating 位置の shift に由来する。 -/
theorem waveStep_nonempty_origin {s : Shape} {r : QuarterPos}
    (hNonempty : ¬ (QuarterPos.getQuarter (Shape.waveStep s) r).isEmpty) :
    (¬ FloatingPos s r ∧ ¬ (QuarterPos.getQuarter s r).isEmpty) ∨
      ∃ p : QuarterPos, FloatingPos s p ∧ p.down = r ∧
        QuarterPos.getQuarter (Shape.waveStep s) r = QuarterPos.getQuarter s p := by
  classical
  by_cases hPreimage : ∃ p : QuarterPos, p ∈ floatingPositions s ∧ p.down = r
  · rcases hPreimage with ⟨p, hpMem, hpDown⟩
    have hpFloating : FloatingPos s p := (mem_floatingPositions_iff s p).mp hpMem
    right
    refine ⟨p, hpFloating, hpDown, ?_⟩
    rw [← hpDown, Shape.waveStep]
    apply Gravity.Internal.getQuarter_atomicShiftDown_of_unique_preimage
    · exact hpMem
    · exact (QuarterPos.mem_allValid s p.down).mp (FloatingPos.down_valid hpFloating)
    · intro q hqMem hqDown
      exact QuarterPos.down_injective_on_floating
        ((mem_floatingPositions_iff s q).mp hqMem) hpFloating hqDown
  · by_cases hClear : r ∈ floatingPositions s
    · have hEmpty : QuarterPos.getQuarter (Shape.waveStep s) r = Quarter.empty := by
        rw [Shape.waveStep]
        apply Gravity.Internal.getQuarter_atomicShiftDown_of_cleared
        · intro p hpMem hpDown
          exact hPreimage ⟨p, hpMem, hpDown⟩
        · exact hClear
      exact False.elim (hNonempty (by simp only [hEmpty, Quarter.isEmpty]))
    · left
      refine ⟨?_, ?_⟩
      · intro hrFloating
        exact hClear ((mem_floatingPositions_iff s r).mpr hrFloating)
      · have hStatic :
            QuarterPos.getQuarter (Shape.waveStep s) r = QuarterPos.getQuarter s r := by
          rw [Shape.waveStep]
          apply Gravity.Internal.getQuarter_atomicShiftDown_of_static
          · intro p hpMem hpDown
            exact hPreimage ⟨p, hpMem, hpDown⟩
          · exact hClear
        intro hEmpty
        exact hNonempty (by simpa only [hStatic] using hEmpty)

end Shape

namespace FloatingPos

/-- `waveStep` 後の floating 位置は、旧 floating 位置の 1 レイヤ下に由来する。 -/
theorem waveStep_origin {s : Shape} {r : QuarterPos}
    (h : FloatingPos (Shape.waveStep s) r) :
    ∃ p : QuarterPos, FloatingPos s p ∧ p.down = r := by
  rcases Shape.waveStep_nonempty_origin (s := s) (r := r) h.2.1 with hStatic | hShift
  · rcases hStatic with ⟨hNotFloating, hOldNonempty⟩
    have hValid : r ∈ QuarterPos.allValid s := by
      rw [QuarterPos.mem_allValid]
      have hLayer : r.1 < (Shape.waveStep s).length :=
        (QuarterPos.mem_allValid (Shape.waveStep s) r).mp h.1
      simpa only [Shape.waveStep, Gravity.Internal.length_atomicShiftDown] using hLayer
    have hGrounded : IsGrounded s r := by
      by_contra hNotGrounded
      exact hNotFloating ⟨hValid, hOldNonempty, hNotGrounded⟩
    exact False.elim (h.2.2 (IsGrounded.waveStep_mono hGrounded))
  · rcases hShift with ⟨p, hpFloating, hpDown, _hEq⟩
    exact ⟨p, hpFloating, hpDown⟩

end FloatingPos

end S2IL
