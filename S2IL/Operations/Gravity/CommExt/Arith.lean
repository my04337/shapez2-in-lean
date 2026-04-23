-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity.Equivariance

/-!
# Gravity CommExt: 着地合計の telescoping（arithmetic）

S1 Sub-lemma #9 の算術基盤。`sum_map_layer_landing_telescope` /
`landing_sum_bound` を提供する。

このファイルは `CommExt.lean` の肥大化回避のために分離された（2026-04-21）。
純 Nat 演算のみに依存し、型は `QuarterPos` のみを参照する。
-/

namespace Gravity

/-- 着地重み合計の telescope 恒等式:
    全要素が `p.layer ≥ d` を満たすなら、
    `∑ ((p.layer - d) + 1) + |ps| · d = ∑ (p.layer + 1)`。

    `Nat` 減算のアンダーフローを回避するため加法形で表現。 -/
theorem sum_map_layer_landing_telescope (ps : List QuarterPos) (d : Nat)
        (h_ge : ∀ p ∈ ps, d ≤ p.layer) :
        (ps.map fun p => (p.layer - d) + 1).sum + ps.length * d =
        (ps.map fun p => p.layer + 1).sum := by
    induction ps with
    | nil => simp
    | cons p tail ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
        have hp : d ≤ p.layer := h_ge p (List.mem_cons_self ..)
        have ih' := ih (fun q hq => h_ge q (List.mem_cons_of_mem _ hq))
        omega

/-- Nat 上の Sublist は sum で単調。 -/
private theorem sublist_sum_le_sum_nat {l1 l2 : List Nat} (h : l1.Sublist l2) :
        l1.sum ≤ l2.sum := by
    induction h with
    | slnil => simp
    | cons a _ ih => simp only [List.sum_cons]; omega
    | cons₂ a _ ih => simp only [List.sum_cons]; omega

/-- 着地境界: 非空な位置リスト `ps`（全要素 `p.layer ≥ d`, `d ≥ 1`）に対し、
    任意の述語 `pred` でフィルタした部分集合の着地重み合計は
    元の重み合計より **真に** 小さい。

    これは S1 の telescoping 引数の核: settling 位置の重み寄与が NGS を
    真に減少させる保証を与える（`|ps|·d ≥ 1` が strict bound の源泉）。 -/
theorem landing_sum_bound (ps : List QuarterPos) (pred : QuarterPos → Bool) (d : Nat)
        (hd : 1 ≤ d) (h_ge : ∀ p ∈ ps, d ≤ p.layer) (h_ne : ps ≠ []) :
        ((ps.filter pred).map fun p => (p.layer - d) + 1).sum <
        (ps.map fun p => p.layer + 1).sum := by
    have h_sub : (ps.filter pred).Sublist ps := List.filter_sublist
    have h_filter_le : ((ps.filter pred).map fun p => (p.layer - d) + 1).sum ≤
            (ps.map fun p => (p.layer - d) + 1).sum :=
        sublist_sum_le_sum_nat (h_sub.map _)
    have h_tel := sum_map_layer_landing_telescope ps d h_ge
    have h_len : 1 ≤ ps.length := by
        cases ps with
        | nil => exact absurd rfl h_ne
        | cons _ _ => simp
    have h_mul : 1 ≤ ps.length * d := Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp h_len) (Nat.one_le_iff_ne_zero.mp hd))
    omega

/-- List.map 点別単調: 各要素で `f ≤ g` なら和も `≤`。 -/
private theorem sum_map_le_of_pointwise_nat {α : Type*} (l : List α) (f g : α → Nat)
        (h : ∀ x ∈ l, f x ≤ g x) :
        (l.map f).sum ≤ (l.map g).sum := by
    induction l with
    | nil => simp
    | cons a rest ih =>
        simp only [List.map_cons, List.sum_cons]
        have h_a := h a (List.mem_cons_self ..)
        have ih' := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
        omega

/-- **`landing_sum_bound` の変数 d 版**。
    各位置 `p` が独自の着地距離 `actual_d p`（`1 ≤ actual_d p`）を持つ場合の
    strict 加法境界。S1 waveStep は FU グループごとに異なる landing distance を
    持つため、固定 d 版だけでは直接接続できない: この版が telescoping の
    `+ 1 ≤` 形式を実 landing distance で直接与える。

    証明核: 各位置で `p.layer - actual_d p ≤ p.layer - 1` を点別単調で和に持ち上げ、
    `landing_sum_bound ps pred 1 ...` の strict 不等式を omega で `+ 1 ≤` 化。 -/
theorem landing_sum_bound_var_d (ps : List QuarterPos) (pred : QuarterPos → Bool)
        (actual_d : QuarterPos → Nat)
        (h_pos : ∀ p ∈ ps, 1 ≤ actual_d p)
        (h_le_layer : ∀ p ∈ ps, 1 ≤ p.layer)
        (h_ne : ps ≠ []) :
        ((ps.filter pred).map fun p => (p.layer - actual_d p) + 1).sum + 1 ≤
        (ps.map fun p => p.layer + 1).sum := by
    have h_filter_sub : ∀ p ∈ ps.filter pred, p ∈ ps := fun p hp =>
        (List.mem_filter.mp hp).1
    have h_step : ((ps.filter pred).map fun p => (p.layer - actual_d p) + 1).sum ≤
            ((ps.filter pred).map fun p => (p.layer - 1) + 1).sum :=
        sum_map_le_of_pointwise_nat _ _ _ (fun p hp => by
            have hp' := h_filter_sub p hp
            have := h_pos p hp'; omega)
    have h_base : ((ps.filter pred).map fun p => (p.layer - 1) + 1).sum <
            (ps.map fun p => p.layer + 1).sum :=
        landing_sum_bound ps pred 1 (le_refl 1) h_le_layer h_ne
    omega

end Gravity
