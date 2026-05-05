-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity.Behavior.Origin

/-!
# S2IL.Operations.Gravity.Behavior.FloatingHeight

`floatingHeight` の減少と fixed fuel 終端性。
-/

namespace S2IL

private theorem foldl_max_acc_le (xs : List Nat) (acc : Nat) :
    acc ≤ xs.foldl Nat.max acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih =>
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left acc a) (ih (Nat.max acc a))

private theorem foldl_max_mem_le_aux {xs : List Nat} {n acc : Nat} (h : n ∈ xs) :
    n ≤ xs.foldl Nat.max acc := by
  induction xs generalizing acc with
  | nil => simp at h
  | cons a xs ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp h with hHead | hTail
      · subst hHead
        exact Nat.le_trans (Nat.le_max_right acc n) (foldl_max_acc_le xs (Nat.max acc n))
      · exact ih (acc := Nat.max acc a) hTail

private theorem foldl_max_mem_le {xs : List Nat} {n : Nat} (h : n ∈ xs) :
    n ≤ xs.foldl Nat.max 0 :=
  foldl_max_mem_le_aux (acc := 0) h

private theorem foldl_max_eq_acc_or_mem (xs : List Nat) (acc : Nat) :
    xs.foldl Nat.max acc = acc ∨
      ∃ n : Nat, n ∈ xs ∧ n = xs.foldl Nat.max acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih =>
      rcases ih (Nat.max acc a) with hEq | hMem
      · by_cases hlt : acc < a
        · right
          refine ⟨a, ?_, ?_⟩
          · simp only [List.mem_cons, true_or]
          · have hMax : Nat.max acc a = a := Nat.max_eq_right (Nat.le_of_lt hlt)
            change a = xs.foldl Nat.max (Nat.max acc a)
            rw [hEq, hMax]
        · left
          have hMax : Nat.max acc a = acc := Nat.max_eq_left (Nat.not_lt.mp hlt)
          change xs.foldl Nat.max (Nat.max acc a) = acc
          rw [hEq, hMax]
      · right
        rcases hMem with ⟨n, hn, hnEq⟩
        refine ⟨n, ?_, ?_⟩
        · exact List.mem_cons_of_mem a hn
        · simpa only [List.foldl_cons] using hnEq

private theorem exists_mem_eq_foldl_max_of_pos {xs : List Nat}
    (hpos : 0 < xs.foldl Nat.max 0) :
    ∃ n : Nat, n ∈ xs ∧ n = xs.foldl Nat.max 0 := by
  rcases foldl_max_eq_acc_or_mem xs 0 with hEq | hMem
  · rw [hEq] at hpos
    omega
  · exact hMem

private theorem foldl_max_lt_of_forall_lt {xs : List Nat} {bound : Nat}
    (hpos : 0 < xs.foldl Nat.max 0)
    (hall : ∀ n : Nat, n ∈ xs → n < bound) :
    xs.foldl Nat.max 0 < bound := by
  rcases exists_mem_eq_foldl_max_of_pos hpos with ⟨n, hn, hnEq⟩
  rw [← hnEq]
  exact hall n hn

private theorem floatingHeight_mem_le {s : Shape} {p : QuarterPos}
    (hp : p ∈ floatingPositions s) :
    p.1 ≤ floatingHeight s := by
  unfold floatingHeight
  apply foldl_max_mem_le
  exact List.mem_map.mpr ⟨p, hp, rfl⟩

private theorem floatingPos_layer_le_floatingHeight {s : Shape} {p : QuarterPos}
    (h : FloatingPos s p) : p.1 ≤ floatingHeight s :=
  floatingHeight_mem_le ((mem_floatingPositions_iff s p).mpr h)

private theorem floatingPos_floatingHeight_pos {s : Shape} {p : QuarterPos}
    (h : FloatingPos s p) : 0 < floatingHeight s :=
  Nat.lt_of_lt_of_le (FloatingPos.layer_pos h) (floatingPos_layer_le_floatingHeight h)

private theorem floatingHeight_lt_of_forall_lt {s : Shape} {bound : Nat}
    (hpos : 0 < floatingHeight s)
    (h : ∀ r : QuarterPos, FloatingPos s r → r.1 < bound) :
    floatingHeight s < bound := by
  unfold floatingHeight at hpos ⊢
  apply foldl_max_lt_of_forall_lt hpos
  intro n hn
  rcases List.mem_map.mp hn with ⟨r, hrMem, hrEq⟩
  rw [← hrEq]
  exact h r ((mem_floatingPositions_iff s r).mp hrMem)

/-- `waveStep` 後に floating 位置が残るなら、`floatingHeight` は真に減少する。 -/
theorem floatingHeight_waveStep_lt {s : Shape}
    (h : 0 < floatingHeight (Shape.waveStep s)) :
    floatingHeight (Shape.waveStep s) < floatingHeight s := by
  refine floatingHeight_lt_of_forall_lt (s := Shape.waveStep s) h ?_
  intro r hrFloating
  rcases FloatingPos.waveStep_origin hrFloating with ⟨p, hpFloating, hpDown⟩
  have hpLe : p.1 ≤ floatingHeight s := floatingPos_layer_le_floatingHeight hpFloating
  have hpPos : 0 < p.1 := FloatingPos.layer_pos hpFloating
  have hLayer : r.1 = p.1 - 1 := by
    have hfst := congrArg Prod.fst hpDown
    simpa only [QuarterPos.down] using hfst.symm
  omega

private theorem floatingPositions_eq_nil_of_floatingHeight_eq_zero {s : Shape}
    (h : floatingHeight s = 0) :
    floatingPositions s = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro p hp
  have hpFloating : FloatingPos s p := (mem_floatingPositions_iff s p).mp hp
  have hpos : 0 < floatingHeight s := floatingPos_floatingHeight_pos hpFloating
  rw [h] at hpos
  omega

private theorem floatingHeight_le_length (s : Shape) :
    floatingHeight s ≤ s.length := by
  by_cases hpos : 0 < floatingHeight s
  · have hlt : floatingHeight s < s.length := by
      apply floatingHeight_lt_of_forall_lt hpos
      intro r hrFloating
      exact (QuarterPos.mem_allValid s r).mp hrFloating.1
    exact Nat.le_of_lt hlt
  · have hzero : floatingHeight s = 0 := Nat.eq_zero_of_not_pos hpos
    rw [hzero]
    exact Nat.zero_le s.length

private theorem floatingHeight_iterate_eq_zero_of_le {s : Shape} {fuel : Nat}
    (h : floatingHeight s ≤ fuel) :
    floatingHeight (Nat.iterate Shape.waveStep fuel s) = 0 := by
  induction fuel generalizing s with
  | zero =>
      have hzero : floatingHeight s = 0 := by omega
      simpa using hzero
  | succ fuel ih =>
      rw [Function.iterate_succ_apply]
      apply ih
      by_cases hpos : 0 < floatingHeight (Shape.waveStep s)
      · have hlt := floatingHeight_waveStep_lt (s := s) hpos
        omega
      · have hzero : floatingHeight (Shape.waveStep s) = 0 := Nat.eq_zero_of_not_pos hpos
        omega

/-- `s.length` 回の wave step 後には floating 位置が存在しない。 -/
theorem waveStep_iter_no_floating (s : Shape) :
    floatingPositions (Nat.iterate Shape.waveStep s.length s) = [] := by
  apply floatingPositions_eq_nil_of_floatingHeight_eq_zero
  exact floatingHeight_iterate_eq_zero_of_le (s := s) (fuel := s.length)
    (floatingHeight_le_length s)

end S2IL
