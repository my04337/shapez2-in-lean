-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity.Defs

/-!
# S2IL.Operations.Gravity.Behavior.Grounded

Wave tick が接地性を保存することを示す Behavior A 層。
-/

namespace S2IL

namespace IsGroundingEdge

/-- `waveStep` で両端の象限値が不変な接地エッジは保存される。 -/
theorem waveStep_of_static {s : Shape} {a b : QuarterPos}
    (ha : QuarterPos.getQuarter (Shape.waveStep s) a = QuarterPos.getQuarter s a)
    (hb : QuarterPos.getQuarter (Shape.waveStep s) b = QuarterPos.getQuarter s b)
    (h : IsGroundingEdge s a b) :
    IsGroundingEdge (Shape.waveStep s) a b :=
  of_getQuarter_eq ha hb h

end IsGroundingEdge

namespace IsGrounded

private theorem of_grounding_path {s : Shape} {p₀ p : QuarterPos}
    (hLayer : p₀.1 = 0)
    (hNonempty : ¬ (QuarterPos.getQuarter s p₀).isEmpty)
    (hPath : Relation.ReflTransGen (IsGroundingEdge s) p₀ p) :
    IsGrounded s p :=
  ⟨p₀, hLayer, hNonempty, hPath⟩

/-- 接地している位置は `FloatingPos` ではない。 -/
theorem not_floating {s : Shape} {p : QuarterPos} (h : IsGrounded s p) :
    ¬ FloatingPos s p := fun hf => hf.2.2 h

/-- 接地パス上の到達点は `FloatingPos` を避ける。 -/
theorem grounding_path_avoids_floating {s : Shape} {p₀ p : QuarterPos}
    (hLayer : p₀.1 = 0)
    (hNonempty : ¬ (QuarterPos.getQuarter s p₀).isEmpty)
    (hPath : Relation.ReflTransGen (IsGroundingEdge s) p₀ p) :
    ¬ FloatingPos s p :=
  not_floating (of_grounding_path hLayer hNonempty hPath)

private theorem grounding_path_waveStep_of_grounded_static {s : Shape} {p₀ p : QuarterPos}
    (hStatic : ∀ r : QuarterPos, IsGrounded s r →
      QuarterPos.getQuarter (Shape.waveStep s) r = QuarterPos.getQuarter s r)
    (hLayer : p₀.1 = 0)
    (hNonempty : ¬ (QuarterPos.getQuarter s p₀).isEmpty)
    (hPath : Relation.ReflTransGen (IsGroundingEdge s) p₀ p) :
    Relation.ReflTransGen (IsGroundingEdge (Shape.waveStep s)) p₀ p := by
  induction hPath with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hpath hedge ih =>
      have hFromGrounded : IsGrounded s _ :=
        ⟨p₀, hLayer, hNonempty, hpath⟩
      have hToGrounded : IsGrounded s _ :=
        ⟨p₀, hLayer, hNonempty, Relation.ReflTransGen.tail hpath hedge⟩
      have hedge' : IsGroundingEdge (Shape.waveStep s) _ _ :=
        IsGroundingEdge.waveStep_of_static
          (hStatic _ hFromGrounded) (hStatic _ hToGrounded) hedge
      exact Relation.ReflTransGen.tail ih hedge'

private theorem waveStep_mono_of_grounded_static {s : Shape} {p : QuarterPos}
    (hStatic : ∀ r : QuarterPos, IsGrounded s r →
      QuarterPos.getQuarter (Shape.waveStep s) r = QuarterPos.getQuarter s r)
    (h : IsGrounded s p) : IsGrounded (Shape.waveStep s) p := by
  obtain ⟨p₀, hp₀Layer, hp₀Nonempty, hpath⟩ := h
  refine ⟨p₀, hp₀Layer, ?_, ?_⟩
  · rw [hStatic p₀ (of_grounding_path hp₀Layer hp₀Nonempty Relation.ReflTransGen.refl)]
    exact hp₀Nonempty
  · exact grounding_path_waveStep_of_grounded_static hStatic hp₀Layer hp₀Nonempty hpath

private theorem not_mem_floatingPositions {s : Shape} {p : QuarterPos}
    (h : IsGrounded s p) : p ∉ floatingPositions s := by
  intro hp
  exact not_floating h ((mem_floatingPositions_iff s p).mp hp)

private theorem no_floating_preimage_down {s : Shape} {p : QuarterPos}
    (h : IsGrounded s p) :
    ∀ q : QuarterPos, q ∈ floatingPositions s → q.down ≠ p := by
  intro q hq hdown
  have hqFloating : FloatingPos s q := (mem_floatingPositions_iff s q).mp hq
  have hpNonempty : ¬ (QuarterPos.getQuarter s p).isEmpty := nonempty h
  have hDownNonempty : ¬ (QuarterPos.getQuarter s q.down).isEmpty := by
    simpa only [hdown] using hpNonempty
  rcases FloatingPos.down_empty_or_floating hqFloating with hDownEmpty | hDownFloating
  · exact hDownNonempty hDownEmpty
  · have hpFloating : FloatingPos s p := by
      simpa only [hdown] using hDownFloating
    exact (not_floating h) hpFloating

/-- 接地済み位置は `waveStep` で象限値が不変である。 -/
theorem waveStep_static {s : Shape} {p : QuarterPos} (h : IsGrounded s p) :
    QuarterPos.getQuarter (Shape.waveStep s) p = QuarterPos.getQuarter s p := by
  rw [Shape.waveStep]
  exact Gravity.Internal.getQuarter_atomicShiftDown_of_static s (floatingPositions s) p
    (no_floating_preimage_down h) (not_mem_floatingPositions h)

/-- `waveStep` は接地性を保存する。 -/
theorem waveStep_mono {s : Shape} {p : QuarterPos} (h : IsGrounded s p) :
    IsGrounded (Shape.waveStep s) p := by
  exact waveStep_mono_of_grounded_static (fun _r hr => waveStep_static hr) h

end IsGrounded

end S2IL
