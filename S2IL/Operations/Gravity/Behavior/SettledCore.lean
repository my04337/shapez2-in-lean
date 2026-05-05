-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity.Behavior.FloatingHeight
import S2IL.Shape.Notation

/-!
# S2IL.Operations.Gravity.Behavior.SettledCore

floating 位置ゼロと `Shape.gravity.isSettled` を結ぶ Behavior B の最終ブリッジ。
-/

namespace S2IL

namespace IsSettled

/-- 安定しているシェイプには floating 位置が存在しない。 -/
theorem floatingPositions_eq_nil {s : Shape} (h : IsSettled s) :
    floatingPositions s = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro p hp
  have hpFloating : FloatingPos s p := (mem_floatingPositions_iff s p).mp hp
  exact hpFloating.2.2 (h p hpFloating.1 hpFloating.2.1)

/-- 安定しているシェイプは `waveStep` の不動点である。 -/
theorem waveStep_fixed {s : Shape} (h : IsSettled s) : Shape.waveStep s = s := by
  rw [Shape.waveStep, floatingPositions_eq_nil h]
  rfl

end IsSettled

/-- fixed fuel core の successor 展開。 -/
private theorem waveGravityCore_succ (fuel : Nat) (s : Shape) :
    Shape.waveGravityCore (fuel + 1) s = Shape.waveGravityCore fuel (Shape.waveStep s) := by
  rfl

/-- Prop として floating 位置が存在しないことは `IsSettled` と同値。 -/
theorem no_floating_iff_isSettled (s : Shape) :
    (∀ p : QuarterPos, ¬ FloatingPos s p) ↔ IsSettled s := by
  constructor
  · intro hNo p hpValid hpNonempty
    by_contra hNotGrounded
    have hpFloating : FloatingPos s p := ⟨hpValid, hpNonempty, hNotGrounded⟩
    exact hNo p hpFloating
  · intro hSettled p hpFloating
    exact hpFloating.2.2 (hSettled p hpFloating.1 hpFloating.2.1)

/-- Prop として floating 位置が存在しないなら `waveStep` は不動点である。 -/
theorem Shape.waveStep_eq_self_of_no_floating {s : Shape}
    (h : ∀ p : QuarterPos, ¬ FloatingPos s p) : Shape.waveStep s = s := by
  exact IsSettled.waveStep_fixed ((no_floating_iff_isSettled s).mp h)

/-- List で列挙した floating 位置が空であることは `IsSettled` と同値。 -/
theorem floatingPositions_eq_nil_iff_isSettled (s : Shape) :
    floatingPositions s = [] ↔ IsSettled s := by
  constructor
  · intro hNo
    exact (no_floating_iff_isSettled s).mp (by
      intro p hpFloating
      have hpMem : p ∈ floatingPositions s := (mem_floatingPositions_iff s p).mpr hpFloating
      rw [hNo] at hpMem
      cases hpMem)
  · intro hSettled
    exact IsSettled.floatingPositions_eq_nil hSettled

/-- `floatingPositions = []` なら `waveStep` は不動点である。 -/
theorem Shape.waveStep_eq_self_of_floatingPositions_eq_nil {s : Shape}
    (h : floatingPositions s = []) : Shape.waveStep s = s := by
  exact IsSettled.waveStep_fixed ((floatingPositions_eq_nil_iff_isSettled s).mp h)

/-- `waveStep` が不動点なら fixed fuel core も不動点である。 -/
private theorem waveGravityCore_eq_self_of_waveStep_fixed {s : Shape}
    (h : Shape.waveStep s = s) (fuel : Nat) : Shape.waveGravityCore fuel s = s := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [waveGravityCore_succ, h, ih]

/-- 安定入力に対して fixed fuel core は任意 fuel で不動点である。 -/
theorem waveGravityCore_eq_self_of_IsSettled {s : Shape}
    (h : IsSettled s) (fuel : Nat) : Shape.waveGravityCore fuel s = s := by
  have hNoFloating : ∀ p : QuarterPos, ¬ FloatingPos s p :=
    (no_floating_iff_isSettled s).mpr h
  exact waveGravityCore_eq_self_of_waveStep_fixed
    (Shape.waveStep_eq_self_of_no_floating hNoFloating) fuel

/-- 早期停止 core は fixed fuel core と同じ結果を返す。 -/
theorem Shape.waveGravityCoreFast_eq_waveGravityCore (fuel : Nat) (s : Shape) :
    Shape.waveGravityCoreFast fuel s = Shape.waveGravityCore fuel s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      unfold Shape.waveGravityCoreFast
      by_cases h : floatingPositions s = []
      · rw [if_pos h]
        exact (waveGravityCore_eq_self_of_waveStep_fixed
          (Shape.waveStep_eq_self_of_floatingPositions_eq_nil h) (fuel + 1)).symm
      · rw [if_neg h]
        rw [ih]
        rw [waveGravityCore_succ]
        rfl

/-- fixed fuel の Wave Gravity core は常に安定状態に到達する。 -/
theorem waveGravityCore_isSettled (s : Shape) :
    IsSettled (Shape.waveGravityCore s.length s) := by
  rw [Shape.waveGravityCore]
  exact (floatingPositions_eq_nil_iff_isSettled (Nat.iterate Shape.waveStep s.length s)).mp
    (waveStep_iter_no_floating s)

/-- 早期停止 core は常に安定状態に到達する。 -/
theorem waveGravityCoreFast_isSettled (s : Shape) :
    IsSettled (Shape.waveGravityCoreFast s.length s) := by
  rw [Shape.waveGravityCoreFast_eq_waveGravityCore]
  exact waveGravityCore_isSettled s

/-- `gravity` の出力は常に `IsSettled`。 -/
theorem Shape.gravity.isSettled (s : Shape) : IsSettled (Shape.gravity s) := by
  rw [Shape.gravity]
  exact IsSettled.normalize (waveGravityCoreFast_isSettled s)

/-- 安定入力に対する `gravity` の不動点性。
    末尾空レイヤを許容する `IsSettled` だけでは `gravity` 末尾の `normalize`
    と整合しないため、`IsNormalized s` を追加仮定する（spec [`falling.md §6.6`]
    に沿う、shape の正規形のみを扱う）。

    旧 `of_isSettled : IsSettled s → gravity s = s` は反例
    `s = [L_grounded, L_empty]` を持つため取り下げ。 -/
theorem Shape.gravity.of_isSettled {s : Shape}
    (hSettled : IsSettled s) (hNorm : Shape.IsNormalized s) :
    Shape.gravity s = s := by
  rw [Shape.gravity]
  rw [Shape.waveGravityCoreFast_eq_waveGravityCore]
  rw [waveGravityCore_eq_self_of_IsSettled hSettled]
  exact Shape.normalize_of_isNormalized s hNorm

end S2IL
