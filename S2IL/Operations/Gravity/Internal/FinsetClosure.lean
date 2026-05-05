import Mathlib.Data.Finset.Card

/-!
# Internal: finite closure fixed-point helpers

このファイルは `S2IL.Operations.Gravity` namespace の補助補題を集める。
**外部モジュール（S2IL/Operations/Gravity.lean, S2IL/Operations/Gravity/*.lean 以外）からは import 禁止**。
-/

namespace S2IL

namespace Gravity.Internal

open scoped Finset

/-- bounded な `step` の反復は常に carrier `bound` 内に留まる。 -/
private theorem finset_iterate_subset_bound {α : Type}
    (bound start : Finset α) (step : Finset α → Finset α)
    (hBoundStart : start ⊆ bound)
    (hBoundStep : ∀ a : Finset α, a ⊆ bound → step a ⊆ bound) :
    ∀ n : Nat, step^[n] start ⊆ bound := by
  intro n
  induction n with
  | zero =>
      simpa using hBoundStart
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hBoundStep (step^[n] start) ih

/-- bounded かつ増加的な `step` では、各反復段階は次段階に含まれる。 -/
private theorem finset_iterate_subset_next {α : Type}
    (bound start : Finset α) (step : Finset α → Finset α)
    (hInfl : ∀ a : Finset α, a ⊆ bound → a ⊆ step a)
    (hBoundStart : start ⊆ bound)
    (hBoundStep : ∀ a : Finset α, a ⊆ bound → step a ⊆ bound) :
    ∀ n : Nat, step^[n] start ⊆ step^[n + 1] start := by
  intro n
  rw [Function.iterate_succ_apply']
  exact hInfl (step^[n] start)
    (finset_iterate_subset_bound bound start step hBoundStart hBoundStep n)

/-- ある反復段階で固定点になれば、それ以降の反復は同じ値になる。 -/
theorem iterate_eq_of_fixed_at {α : Type} (start : α) (step : α → α)
    {i n : Nat} (hFix : step (step^[i] start) = step^[i] start) (hi : i ≤ n) :
    step^[n] start = step^[i] start := by
  rw [← Nat.add_sub_of_le hi]
  calc
    step^[i + (n - i)] start = step^[(n - i) + i] start := by
      rw [Nat.add_comm i (n - i)]
    _ = step^[n - i] (step^[i] start) :=
      Function.iterate_add_apply step (n - i) i start
    _ = step^[i] start := Function.iterate_fixed hFix (n - i)

/-- ある反復段階で固定点なら、それ以降の任意段階も固定点である。 -/
theorem iterate_fixed_at_of_fixed_at_le {α : Type} (start : α) (step : α → α)
    {i n : Nat} (hFix : step (step^[i] start) = step^[i] start) (hi : i ≤ n) :
    step (step^[n] start) = step^[n] start := by
  rw [iterate_eq_of_fixed_at start step hFix hi]
  exact hFix

/-- 最終段階が固定点でないなら、それ以前の各段階で card が真に増加する。 -/
private theorem finset_iterate_card_strict_of_not_fixed_at_bound {α : Type} [DecidableEq α]
    (bound start : Finset α) (step : Finset α → Finset α)
    (hInfl : ∀ a : Finset α, a ⊆ bound → a ⊆ step a)
    (hBoundStart : start ⊆ bound)
    (hBoundStep : ∀ a : Finset α, a ⊆ bound → step a ⊆ bound)
    (hNotFixed : step (step^[#bound] start) ≠ step^[#bound] start)
    {i : Nat} (hi : i ≤ #bound) :
    #(step^[i] start) < #(step^[i + 1] start) := by
  have hSubset : step^[i] start ⊆ step^[i + 1] start :=
    finset_iterate_subset_next bound start step hInfl hBoundStart hBoundStep i
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hSubset, ?_⟩)
  intro hEq
  have hFixI : step (step^[i] start) = step^[i] start := by
    rw [← Function.iterate_succ_apply' step i start]
    exact hEq.symm
  exact hNotFixed (iterate_fixed_at_of_fixed_at_le start step hFixI hi)

/-- 長さ `n` まで毎回 card が真に増えれば、`m` 段階目の card は少なくとも `m`。 -/
private theorem finset_card_lower_of_strict_chain {α : Type} (seq : Nat → Finset α)
    {n : Nat} (hStrict : ∀ i : Nat, i < n → #(seq i) < #(seq (i + 1))) :
    ∀ m : Nat, m ≤ n → m ≤ #(seq m) := by
  intro m hm
  induction m with
  | zero =>
      exact Nat.zero_le _
  | succ m ih =>
      have hmLt : m < n := Nat.lt_of_succ_le hm
      have hlt := hStrict m hmLt
      have hih : m ≤ #(seq m) := ih (Nat.le_trans (Nat.le_succ m) hm)
      omega

/-- 有限 carrier 内で増加的に閉じる Finset 反復は、carrier サイズ後に固定点へ到達する。 -/
theorem finset_iterate_fixed_of_bounded {α : Type} [DecidableEq α]
    (bound start : Finset α) (step : Finset α → Finset α)
    (hInfl : ∀ a : Finset α, a ⊆ bound → a ⊆ step a)
    (hBoundStart : start ⊆ bound)
    (hBoundStep : ∀ a : Finset α, a ⊆ bound → step a ⊆ bound) :
    step (step^[#bound] start) = step^[#bound] start := by
  classical
  by_contra hNotFixed
  let seq : Nat → Finset α := fun n => step^[n] start
  have hStrict : ∀ i : Nat, i < #bound + 1 → #(seq i) < #(seq (i + 1)) := by
    intro i hi
    exact finset_iterate_card_strict_of_not_fixed_at_bound bound start step
      hInfl hBoundStart hBoundStep hNotFixed (Nat.lt_succ_iff.mp hi)
  have hLower : #bound + 1 ≤ #(seq (#bound + 1)) :=
    finset_card_lower_of_strict_chain seq hStrict (#bound + 1) le_rfl
  have hUpper : #(seq (#bound + 1)) ≤ #bound := by
    simpa [seq] using Finset.card_le_card
      (finset_iterate_subset_bound bound start step hBoundStart hBoundStep (#bound + 1))
  omega

end Gravity.Internal

end S2IL