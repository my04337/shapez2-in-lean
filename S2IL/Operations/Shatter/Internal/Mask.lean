-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel

/-!
# Internal: shatter mask primitive

このファイルは `S2IL.Operations.Shatter` namespace の補助補題を集める。
**外部モジュール（S2IL/Operations/Shatter.lean, S2IL/Operations/Shatter/*.lean 以外）からは import 禁止**。
-/

namespace S2IL

namespace Shatter.Internal

/-- `shatterMaskFrom P start s`: `s` の各レイヤ（`start, start+1, ...`）の各方角 `d` について、
    `P n d` が真なら `Quarter.empty`、偽なら元の象限を保持する。 -/
def shatterMaskFrom (P : Nat → Direction → Bool) : Nat → Shape → Shape
  | _, [] => []
  | n, l :: ls =>
    (fun d => if P n d then Quarter.empty else l d) :: shatterMaskFrom P (n + 1) ls

/-- `shatterMaskFrom` と `Shape.rotateCW` は方角 +1 シフト相当の述語入れ替えで可換。 -/
theorem shatterMaskFrom.rotateCW_eq
    {P P' : Nat → Direction → Bool} (h : ∀ k d, P k d = P' k (d + 1)) :
    ∀ (n : Nat) (s : Shape),
      (shatterMaskFrom P n s).rotateCW = shatterMaskFrom P' n s.rotateCW := by
  intro n s
  induction s generalizing n with
  | nil => rfl
  | cons l ls ih =>
    show List.map Layer.rotateCW (shatterMaskFrom P n (l :: ls))
        = shatterMaskFrom P' n (List.map Layer.rotateCW (l :: ls))
    rw [shatterMaskFrom, List.map_cons, List.map_cons, shatterMaskFrom]
    congr 1
    · funext d
      show (if P n (d - 1) then Quarter.empty else l (d - 1))
          = (if P' n d then Quarter.empty else l (d - 1))
      have hkey : P n (d - 1) = P' n d := by
        have := h n (d - 1)
        rwa [Direction.sub_one_add_one] at this
      rw [hkey]
    · exact ih (n + 1)

end Shatter.Internal

end S2IL