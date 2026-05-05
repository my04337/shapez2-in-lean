-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Settled.Defs

/-!
# S2IL.Operations.Settled.Normalize

`Shape.normalize`（末尾空レイヤの削除）が `IsSettled` を保存することを示す。
-/

namespace S2IL

private theorem mem_takeWhile_bool {α : Type} {p : α → Bool} {x : α} {xs : List α}
    (hx : x ∈ xs.takeWhile p) : p x = true := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      by_cases hy : p y = true
      · simp [List.takeWhile, hy] at hx
        rcases hx with hx | hx
        · subst hx
          exact hy
        · exact ih hx
      · simp [List.takeWhile, hy] at hx

private theorem normalize_prefix_with_empty_suffix (s : Shape) :
    ∃ suffix : List Layer,
      Shape.normalize s ++ suffix = s ∧ ∀ l : Layer, l ∈ suffix → l.isEmpty = true := by
  refine ⟨(s.reverse.takeWhile Layer.isEmpty).reverse, ?_, ?_⟩
  · unfold Shape.normalize Shape.dropTrailingEmpty
    calc
      (s.reverse.dropWhile Layer.isEmpty).reverse ++
          (s.reverse.takeWhile Layer.isEmpty).reverse =
          (s.reverse.takeWhile Layer.isEmpty ++
            s.reverse.dropWhile Layer.isEmpty).reverse := by
        rw [List.reverse_append]
      _ = (s.reverse).reverse := by
        rw [List.takeWhile_append_dropWhile]
      _ = s := by
        simp only [List.reverse_reverse]
  · intro l hl
    exact mem_takeWhile_bool (x := l) (List.mem_reverse.mp hl)

private theorem getQuarter_of_layer_isEmpty {l : Layer} {d : Direction}
    (h : l.isEmpty = true) : (l d).isEmpty = true := by
  rcases d with ⟨n, hn⟩
  have hnCases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hnCases with rfl | rfl | rfl | rfl <;> simp [Layer.isEmpty] at h ⊢ <;> tauto

private theorem getQuarter_normalize_of_valid {s : Shape} {p : QuarterPos}
    (hp : p.1 < (Shape.normalize s).length) :
    QuarterPos.getQuarter (Shape.normalize s) p = QuarterPos.getQuarter s p := by
  rcases normalize_prefix_with_empty_suffix s with ⟨suffix, hPrefix, _hSuffix⟩
  unfold QuarterPos.getQuarter
  rw [dif_pos hp]
  have hpS : p.1 < s.length := by
    have hle : (Shape.normalize s).length ≤ s.length := by
      calc
        (Shape.normalize s).length ≤ (Shape.normalize s ++ suffix).length := by
          simp only [List.length_append, Nat.le_add_right]
        _ = s.length := by
          rw [hPrefix]
    omega
  rw [dif_pos hpS]
  have hget : (Shape.normalize s)[p.1] = s[p.1] := by
    have hget? : (Shape.normalize s)[p.1]? = s[p.1]? := by
      calc
        (Shape.normalize s)[p.1]? = (Shape.normalize s ++ suffix)[p.1]? := by
          symm
          rw [List.getElem?_append]
          simp only [hp, ↓reduceIte]
        _ = s[p.1]? := by
          rw [hPrefix]
    simpa only [List.getElem?_eq_getElem hp, List.getElem?_eq_getElem hpS,
      Option.some.injEq] using hget?
  rw [hget]

private theorem layer_lt_normalize_length_of_getQuarter_nonempty {s : Shape} {p : QuarterPos}
    (h : ¬ (QuarterPos.getQuarter s p).isEmpty) :
    p.1 < (Shape.normalize s).length := by
  rcases normalize_prefix_with_empty_suffix s with ⟨suffix, hPrefix, hSuffixEmpty⟩
  by_contra hpNorm
  have hpS : p.1 < s.length := by
    unfold QuarterPos.getQuarter at h
    by_cases hp : p.1 < s.length
    · exact hp
    · rw [dif_neg hp] at h
      exact False.elim (h (by simp only [Quarter.isEmpty]))
  have hle : (Shape.normalize s).length ≤ p.1 := Nat.le_of_not_gt hpNorm
  have hindexSuffix : p.1 - (Shape.normalize s).length < suffix.length := by
    have hlen : s.length = (Shape.normalize s ++ suffix).length := by
      rw [hPrefix]
    rw [hlen] at hpS
    simp only [List.length_append] at hpS
    omega
  have hLayerEq : s[p.1] = suffix[p.1 - (Shape.normalize s).length] := by
    have hget? : s[p.1]? = suffix[p.1 - (Shape.normalize s).length]? := by
      calc
        s[p.1]? = (Shape.normalize s ++ suffix)[p.1]? := by
          rw [hPrefix]
        _ = suffix[p.1 - (Shape.normalize s).length]? := by
          rw [List.getElem?_append]
          simp only [Nat.not_lt_of_ge hle, ↓reduceIte]
    simpa only [List.getElem?_eq_getElem hpS, List.getElem?_eq_getElem hindexSuffix,
      Option.some.injEq] using hget?
  have hLayerEmpty : (s[p.1]).isEmpty = true := by
    rw [hLayerEq]
    exact hSuffixEmpty _ (List.getElem_mem hindexSuffix)
  unfold QuarterPos.getQuarter at h
  rw [dif_pos hpS] at h
  have hQuarterEmpty : (s[p.1] p.2).isEmpty = true := getQuarter_of_layer_isEmpty hLayerEmpty
  exact h (by simpa using hQuarterEmpty)

private theorem IsGroundingEdge.left_nonempty {s : Shape} {a b : QuarterPos}
    (h : IsGroundingEdge s a b) :
    ¬ (QuarterPos.getQuarter s a).isEmpty := by
  rcases h with hContact | hBond
  · rcases hContact.1 with hVertical | hHorizontal
    · exact hVertical.2.2.1
    · exact hHorizontal.2.2.1
  · exact Quarter.not_isEmpty_of_canFormBond hBond.2.1

private theorem IsGroundingEdge.normalize {s : Shape} {a b : QuarterPos}
    (h : IsGroundingEdge s a b) :
    IsGroundingEdge (Shape.normalize s) a b := by
  apply IsGroundingEdge.of_getQuarter_eq
  · exact getQuarter_normalize_of_valid
      (layer_lt_normalize_length_of_getQuarter_nonempty (IsGroundingEdge.left_nonempty h))
  · exact getQuarter_normalize_of_valid
      (layer_lt_normalize_length_of_getQuarter_nonempty (IsGroundingEdge.right_nonempty h))
  · exact h

private theorem IsGrounded.normalize {s : Shape} {p : QuarterPos}
    (h : IsGrounded s p) : IsGrounded (Shape.normalize s) p := by
  rcases h with ⟨p₀, hp₀Layer, hp₀Nonempty, hPath⟩
  refine ⟨p₀, hp₀Layer, ?_, ?_⟩
  · exact (by
      simpa only [getQuarter_normalize_of_valid
        (layer_lt_normalize_length_of_getQuarter_nonempty hp₀Nonempty)] using hp₀Nonempty)
  · induction hPath with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hedge ih => exact Relation.ReflTransGen.tail ih (IsGroundingEdge.normalize hedge)

namespace IsSettled

/-- `IsSettled` は末尾空レイヤの正規化で保存される。 -/
theorem normalize {s : Shape} (h : IsSettled s) : IsSettled (Shape.normalize s) := by
  intro p hpValid hpNonempty
  have hpLayer : p.1 < (Shape.normalize s).length :=
    (QuarterPos.mem_allValid (Shape.normalize s) p).mp hpValid
  have hpSame : QuarterPos.getQuarter (Shape.normalize s) p = QuarterPos.getQuarter s p :=
    getQuarter_normalize_of_valid hpLayer
  have hpValidS : p ∈ QuarterPos.allValid s := by
    rw [QuarterPos.mem_allValid]
    rcases normalize_prefix_with_empty_suffix s with ⟨suffix, hPrefix, _hSuffix⟩
    have hle : (Shape.normalize s).length ≤ s.length := by
      calc
        (Shape.normalize s).length ≤ (Shape.normalize s ++ suffix).length := by
          simp only [List.length_append, Nat.le_add_right]
        _ = s.length := by
          rw [hPrefix]
    omega
  have hpNonemptyS : ¬ (QuarterPos.getQuarter s p).isEmpty := by
    simpa only [← hpSame] using hpNonempty
  exact IsGrounded.normalize (h p hpValidS hpNonemptyS)

end IsSettled

end S2IL
