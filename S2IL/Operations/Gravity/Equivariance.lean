-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity.Behavior

/-!
# S2IL.Operations.Gravity.Equivariance

Wave Gravity の等変性層。

## 公開 API

- `FloatingPos.rotateCW`
- `Shape.waveStep.rotateCW_comm`
- `Shape.waveGravityCore.rotateCW_comm`
- `Shape.gravity.rotateCW_comm`
- `Shape.gravity.rotate180_comm`
- `Shape.gravity.rotateCCW_comm`

## 単一チェーン原則

CW 等変性のみを主証明対象とし、180° / CCW は CW 版の 1 行系として維持する。
-/

namespace S2IL

private theorem isGrounded_rotateCW_iff (s : Shape) (p : QuarterPos) :
    IsGrounded s.rotateCW p.rotateCW ↔ IsGrounded s p := by
  constructor
  · intro h
    have h1 := IsGrounded.rotateCW h
    have h2 := IsGrounded.rotateCW h1
    have h3 := IsGrounded.rotateCW h2
    simpa [Shape.rotateCW.four, QuarterPos.rotateCW.four] using h3
  · intro h
    exact IsGrounded.rotateCW h

namespace FloatingPos

/-- `FloatingPos` は CW 回転で保存・反映される。 -/
theorem rotateCW (s : Shape) (p : QuarterPos) :
    FloatingPos s.rotateCW p.rotateCW ↔ FloatingPos s p := by
  constructor
  · rintro ⟨hValidRot, hNonemptyRot, hNotGroundedRot⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [QuarterPos.mem_allValid]
      have hLayer := (QuarterPos.mem_allValid s.rotateCW p.rotateCW).mp hValidRot
      simpa [QuarterPos.rotateCW_fst, Shape.rotateCW] using hLayer
    · simpa [QuarterPos.getQuarter_rotateCW] using hNonemptyRot
    · intro hGrounded
      exact hNotGroundedRot (IsGrounded.rotateCW hGrounded)
  · rintro ⟨hValid, hNonempty, hNotGrounded⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [QuarterPos.mem_allValid]
      have hLayer := (QuarterPos.mem_allValid s p).mp hValid
      simpa [QuarterPos.rotateCW_fst, Shape.rotateCW] using hLayer
    · simpa [QuarterPos.getQuarter_rotateCW] using hNonempty
    · intro hGroundedRot
      exact hNotGrounded ((isGrounded_rotateCW_iff s p).mp hGroundedRot)

end FloatingPos

private theorem getQuarter_waveStep_of_floating_down {s : Shape} {p r : QuarterPos}
    (hpFloating : FloatingPos s p) (hpDown : p.down = r) :
    QuarterPos.getQuarter (Shape.waveStep s) r = QuarterPos.getQuarter s p := by
  rw [← hpDown, Shape.waveStep]
  apply Gravity.Internal.getQuarter_atomicShiftDown_of_unique_preimage
  · exact (mem_floatingPositions_iff s p).mpr hpFloating
  · exact (QuarterPos.mem_allValid s p.down).mp (FloatingPos.down_valid hpFloating)
  · intro q hqMem hqDown
    exact QuarterPos.down_injective_on_floating
      ((mem_floatingPositions_iff s q).mp hqMem) hpFloating hqDown

private theorem getQuarter_waveStep_of_no_preimage_cleared {s : Shape} {r : QuarterPos}
    (hNo : ∀ p : QuarterPos, FloatingPos s p → p.down ≠ r)
    (hClear : FloatingPos s r) :
    QuarterPos.getQuarter (Shape.waveStep s) r = Quarter.empty := by
  rw [Shape.waveStep]
  apply Gravity.Internal.getQuarter_atomicShiftDown_of_cleared
  · intro p hpMem hpDown
    exact hNo p ((mem_floatingPositions_iff s p).mp hpMem) hpDown
  · exact (mem_floatingPositions_iff s r).mpr hClear

private theorem getQuarter_waveStep_of_no_preimage_static {s : Shape} {r : QuarterPos}
    (hNo : ∀ p : QuarterPos, FloatingPos s p → p.down ≠ r)
    (hStatic : ¬ FloatingPos s r) :
    QuarterPos.getQuarter (Shape.waveStep s) r = QuarterPos.getQuarter s r := by
  rw [Shape.waveStep]
  apply Gravity.Internal.getQuarter_atomicShiftDown_of_static
  · intro p hpMem hpDown
    exact hNo p ((mem_floatingPositions_iff s p).mp hpMem) hpDown
  · intro hrMem
    exact hStatic ((mem_floatingPositions_iff s r).mp hrMem)

private theorem no_floating_preimage_of_not_exists {s : Shape} {r : QuarterPos}
    (hNoPreimage : ¬ ∃ p : QuarterPos, FloatingPos s p ∧ p.down = r) :
    ∀ p : QuarterPos, FloatingPos s p → p.down ≠ r := by
  intro p hpFloating hpDown
  exact hNoPreimage ⟨p, hpFloating, hpDown⟩

private theorem no_rotated_floating_preimage {s : Shape} {r : QuarterPos}
    (hNo : ∀ p : QuarterPos, FloatingPos s p → p.down ≠ r) :
    ∀ q : QuarterPos, FloatingPos s.rotateCW q → q.down ≠ r.rotateCW := by
  intro q hqFloatingRot hqDown
  have hqFloating : FloatingPos s q.rotateCCW := by
    have hqRewritten : FloatingPos s.rotateCW q.rotateCCW.rotateCW := by
      simpa [QuarterPos.rotateCW_rotateCCW] using hqFloatingRot
    exact (FloatingPos.rotateCW s q.rotateCCW).mp hqRewritten
  have hDown : q.rotateCCW.down = r := by
    have h := congrArg QuarterPos.rotateCCW hqDown
    simpa [QuarterPos.down] using h
  exact hNo q.rotateCCW hqFloating hDown

private theorem getQuarter_waveStep_rotateCW (s : Shape) (r : QuarterPos) :
    QuarterPos.getQuarter (Shape.waveStep s).rotateCW r.rotateCW =
      QuarterPos.getQuarter (Shape.waveStep s.rotateCW) r.rotateCW := by
  rw [QuarterPos.getQuarter_rotateCW]
  by_cases hPreimage : ∃ p : QuarterPos, FloatingPos s p ∧ p.down = r
  · rcases hPreimage with ⟨p, hpFloating, hpDown⟩
    have hLeft := getQuarter_waveStep_of_floating_down hpFloating hpDown
    have hpFloatingRot : FloatingPos s.rotateCW p.rotateCW :=
      (FloatingPos.rotateCW s p).mpr hpFloating
    have hpDownRot : p.rotateCW.down = r.rotateCW := by
      rw [← QuarterPos.down_rotateCW, hpDown]
    have hRight := getQuarter_waveStep_of_floating_down hpFloatingRot hpDownRot
    rw [hLeft, hRight, QuarterPos.getQuarter_rotateCW]
  · have hNo := no_floating_preimage_of_not_exists hPreimage
    have hNoRot := no_rotated_floating_preimage (s := s) (r := r) hNo
    by_cases hClear : FloatingPos s r
    · have hLeft := getQuarter_waveStep_of_no_preimage_cleared hNo hClear
      have hRight := getQuarter_waveStep_of_no_preimage_cleared
        (s := s.rotateCW) (r := r.rotateCW) hNoRot ((FloatingPos.rotateCW s r).mpr hClear)
      rw [hLeft, hRight]
    · have hLeft := getQuarter_waveStep_of_no_preimage_static hNo hClear
      have hStaticRot : ¬ FloatingPos s.rotateCW r.rotateCW := fun hrRot =>
        hClear ((FloatingPos.rotateCW s r).mp hrRot)
      have hRight := getQuarter_waveStep_of_no_preimage_static
        (s := s.rotateCW) (r := r.rotateCW) hNoRot hStaticRot
      rw [hLeft, hRight, QuarterPos.getQuarter_rotateCW]

namespace Shape

/-- `waveStep` と CW 回転は可換。 -/
theorem waveStep.rotateCW_comm (s : Shape) :
    (Shape.waveStep s).rotateCW = Shape.waveStep s.rotateCW := by
  apply Shape.ext_getQuarter
  · simp [Shape.waveStep, Shape.rotateCW]
  · intro p
    have h := getQuarter_waveStep_rotateCW s p.rotateCCW
    simpa [QuarterPos.rotateCW_rotateCCW] using h

private theorem waveGravityCore_succ_eq (fuel : Nat) (s : Shape) :
    Shape.waveGravityCore (fuel + 1) s = Shape.waveGravityCore fuel (Shape.waveStep s) := by
  rfl

/-- `waveGravityCore` と CW 回転は可換。 -/
theorem waveGravityCore.rotateCW_comm (fuel : Nat) (s : Shape) :
    (Shape.waveGravityCore fuel s).rotateCW = Shape.waveGravityCore fuel s.rotateCW := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      rw [waveGravityCore_succ_eq, waveGravityCore_succ_eq]
      rw [ih (Shape.waveStep s), Shape.waveStep.rotateCW_comm]

end Shape

/-- `gravity` と CW 回転は可換。 -/
theorem Shape.gravity.rotateCW_comm (s : Shape) :
    Shape.rotateCW (Shape.gravity s) = Shape.gravity (Shape.rotateCW s) := by
  rw [Shape.gravity, Shape.gravity]
  rw [Shape.normalize.rotateCW_comm]
  rw [Shape.waveGravityCoreFast_eq_waveGravityCore]
  rw [Shape.waveGravityCoreFast_eq_waveGravityCore]
  rw [Shape.waveGravityCore.rotateCW_comm]
  simp [Shape.rotateCW]

/-- `gravity` と 180° 回転は可換（CW の系）。 -/
theorem Shape.gravity.rotate180_comm (s : Shape) :
    (Shape.gravity s).rotate180 = Shape.gravity s.rotate180 := by
  simp [Shape.rotate180_eq_rotateCW_rotateCW, Shape.gravity.rotateCW_comm]

/-- `gravity` と CCW 回転は可換（CW の系）。 -/
theorem Shape.gravity.rotateCCW_comm (s : Shape) :
    (Shape.gravity s).rotateCCW = Shape.gravity s.rotateCCW := by
  simp [Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW, Shape.gravity.rotateCW_comm]

end S2IL
