-- Scratch file to check simp? output with only S2IL imports (no Mathlib)
import S2IL.Shape.Shape

-- L153 approach: simp only + decide_eq_false_iff_not + omega
example (i : Nat) : ((i + 1 == i) || (i + 1 == i)) = false := by
    simp only [Bool.or_self]
    exact decide_eq_false_iff_not.mpr (by omega)

-- L284 approach: cases on the list
example (layers : List Layer) (h_len : 0 = layers.length) (h_ne : layers ≠ []) : False := by
    exact h_ne (by cases layers with
        | nil => rfl
        | cons _ l => simp only [List.length_cons] at h_len; omega)

-- L307 approach: simp_all stays bare (can't stabilize without Mathlib lemma names)
-- Just verify it works
example (l : List Layer) (i j : Nat) (a : Layer) :
    (l.set i a).getD j Layer.empty =
    if i = j ∧ i < l.length then a else l.getD j Layer.empty := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
    split <;> split <;> simp_all <;> omega
