-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity
import S2IL.Kernel.Transform.Rotate

-- RotateCW の安定状態保存
-- ============================================================

-- floatingUnits_isEmpty_rotateCW は Gravity.lean で証明済み

namespace Shape

/-- 安定状態は rotateCW (時計回り 90° 回転) で保存される -/
theorem IsSettled_rotateCW (s : Shape) (h : s.IsSettled) :
        s.rotateCW.IsSettled := by
    simp only [IsSettled] at h ⊢
    have he := Gravity.floatingUnits_isEmpty_rotateCW s
    rw [h] at he
    cases hf : Gravity.floatingUnits s.rotateCW with
    | nil => rfl
    | cons a l =>
        rw [hf] at he
        simp only [List.isEmpty_cons, List.isEmpty_nil] at he
        exact absurd he (show true ≠ false by decide)

/-- 安定状態は rotateCCW (反時計回り 90° 回転) で保存される。
    rotateCCW = rotateCW の 3 回適用として導出する -/
theorem IsSettled_rotateCCW (s : Shape) (h : s.IsSettled) :
        s.rotateCCW.IsSettled := by
    -- rotateCCW = rotateCW³ を利用: s.rotateCCW = s.rotateCW.rotateCW.rotateCW
    have : s.rotateCCW = s.rotateCW.rotateCW.rotateCW := by
        have h4 := s.rotateCW_four
        -- s.rotateCW⁴ = s → s.rotateCW³ = s.rotateCCW
        calc s.rotateCCW
            = s.rotateCW.rotateCW.rotateCW.rotateCW.rotateCCW := by
                rw [h4]
            _ = s.rotateCW.rotateCW.rotateCW := by
                rw [rotateCW_rotateCCW]
    rw [this]
    exact IsSettled_rotateCW _ (IsSettled_rotateCW _ (IsSettled_rotateCW _ h))

end Shape
