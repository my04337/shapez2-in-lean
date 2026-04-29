-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape
import Mathlib.Data.List.Perm.Subperm

/-!
# S2IL.Operations.Gravity.Internal.BFS

落下機構で用いる **fuel ベース汎用 BFS** と Gravity 共通の小補助
（[gravity-proof-plan.md §7 D-10D](../../../../docs/plans/gravity-proof-plan.md)）。

## 役割

`Defs.lean` から `private def reachClosure` / `horizontalAdj` を本ファイルに切り出し、
**汎用 BFS（型変数 `α` 上）** と **Gravity 固有の補助（`QuarterPos` 上）** を分離する。
`Internal/Collision.lean` の §2-3（`reachClosure` 不変条件）で
これらの公開 API を直接参照できるようにするため、`private` を外して公開する。

## 公開 API

| 名前 | 役割 |
|---|---|
| `listDedup` | 先頭優先の重複除去 |
| `reachClosure` | `step : List α → List α` の有界 fixpoint |
| `horizontalAdj` | 同レイヤ円環上の左右隣接 (`QuarterPos` 限定) |

## 単一責務

本ファイルは **計算的 BFS の純粋骨格** に限定する。
意味論的な同値性（`IsGrounded` / `IsGroundingEdge` との対応）は
`Internal/Collision.lean` 側で扱う。
-/

namespace S2IL
namespace Gravity

-- ============================================================
-- 汎用 BFS（型変数 `α` 上）
-- ============================================================

/-- `xs` の重複を取り除く（先頭優先）。 -/
def listDedup [DecidableEq α] (xs : List α) : List α :=
  xs.foldr (fun x acc => if x ∈ acc then acc else x :: acc) []

/-- `step` を fuel 段適用して fixpoint へ近づける。
    各反復で `init` と `step init` を merge し、長さが増えなければ停止する。 -/
def reachClosure {α : Type _} [DecidableEq α]
    (step : List α → List α) (init : List α) : Nat → List α
  | 0 => init
  | fuel + 1 =>
    let next := step init
    let merged := listDedup (init ++ next)
    if merged.length ≤ init.length then init
    else reachClosure step merged fuel

-- ============================================================
-- Gravity 固有の小補助（`QuarterPos` 上）
-- ============================================================

/-- 同レイヤ内左右隣接（`Direction` 上の `±1`）。 -/
def horizontalAdj (p : QuarterPos) : List QuarterPos :=
  [(p.1, p.2 + 1), (p.1, p.2 - 1)]

-- ============================================================
-- §A. listDedup 汎用補題
-- ============================================================

/-- `listDedup` は要素集合を保つ。 -/
theorem mem_listDedup_iff {α : Type _} [DecidableEq α] (xs : List α) (x : α) :
    x ∈ listDedup xs ↔ x ∈ xs := by
  induction xs generalizing x with
  | nil => simp [listDedup]
  | cons y ys ih =>
    show x ∈ (if y ∈ listDedup ys then listDedup ys else y :: listDedup ys) ↔
         x ∈ y :: ys
    by_cases hmem : y ∈ listDedup ys
    · rw [if_pos hmem, ih, List.mem_cons]
      have hy : y ∈ ys := (ih (x := y)).mp hmem
      constructor
      · intro h; exact Or.inr h
      · rintro (rfl | h)
        · exact hy
        · exact h
    · rw [if_neg hmem, List.mem_cons, List.mem_cons, ih]

/-- `listDedup` の長さは元リストの長さ以下。 -/
theorem listDedup_length_le {α : Type _} [DecidableEq α] (xs : List α) :
    (listDedup xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [listDedup]
  | cons y ys ih =>
    show (if y ∈ listDedup ys then listDedup ys else y :: listDedup ys).length ≤
         (y :: ys).length
    by_cases hmem : y ∈ listDedup ys
    · rw [if_pos hmem]
      exact Nat.le_succ_of_le ih
    · rw [if_neg hmem, List.length_cons, List.length_cons]
      exact Nat.succ_le_succ ih

/-- `listDedup` の結果は常に `Nodup`。 -/
theorem listDedup_nodup {α : Type _} [DecidableEq α] (xs : List α) :
    (listDedup xs).Nodup := by
  induction xs with
  | nil => simp [listDedup]
  | cons y ys ih =>
    show (if y ∈ listDedup ys then listDedup ys else y :: listDedup ys).Nodup
    by_cases h : y ∈ listDedup ys
    · simp [h, ih]
    · simp [h, ih, List.nodup_cons]

-- ============================================================
-- §B. reachClosure 汎用補題
-- ============================================================

/-- `init` は常に `reachClosure` 結果に含まれる。 -/
theorem mem_reachClosure_of_mem_init {α : Type _} [DecidableEq α]
    (step : List α → List α) (init : List α) (fuel : Nat)
    {x : α} (hx : x ∈ init) :
    x ∈ reachClosure step init fuel := by
  induction fuel generalizing init with
  | zero => simpa [reachClosure] using hx
  | succ n ih =>
    simp only [reachClosure]
    by_cases h : (listDedup (init ++ step init)).length ≤ init.length
    · rw [if_pos h]; exact hx
    · rw [if_neg h]
      apply ih
      rw [mem_listDedup_iff, List.mem_append]
      exact Or.inl hx
/-- BFS 帰納原理: `P` が `init` で成立し `step` で保存されるなら `reachClosure` 全体で成立。 -/
theorem reachClosure_induction {α : Type _} [DecidableEq α]
    (step : List α → List α) (P : α → Prop)
    (hStep : ∀ current y, (∀ x ∈ current, P x) → y ∈ step current → P y) :
    ∀ (init : List α) (fuel : Nat),
      (∀ x ∈ init, P x) → ∀ x ∈ reachClosure step init fuel, P x := by
  intro init fuel
  induction fuel generalizing init with
  | zero =>
    intro hInit x hx
    simpa [reachClosure] using hInit x hx
  | succ n ih =>
    intro hInit x hx
    simp only [reachClosure] at hx
    by_cases h : (listDedup (init ++ step init)).length ≤ init.length
    · rw [if_pos h] at hx; exact hInit x hx
    · rw [if_neg h] at hx
      refine ih (listDedup (init ++ step init)) ?_ x hx
      intro y hy
      rw [mem_listDedup_iff, List.mem_append] at hy
      rcases hy with hy | hy
      · exact hInit y hy
      · exact hStep init y hInit hy

/-- `reachClosure` の結果は元の `init` を包む単調列。 -/
theorem mem_init_subset_reachClosure {α : Type _} [DecidableEq α]
    (step : List α → List α) (init : List α) (fuel : Nat) :
    ∀ y ∈ init, y ∈ reachClosure step init fuel :=
  fun _ hx => mem_reachClosure_of_mem_init step init fuel hx

/-- 主要な閉包補題。

`fuel` が十分大（要素全空間 `univ` のサイズ以上）かつ `init` が `Nodup` なら、
`reachClosure` の結果は `step` の閉集合になる。

**証明戦略**: 強化補題 `reachClosure_closed_aux` を `fuel + init.length ≥ univ.length` で
帰納する。各反復で停止しなければ `merged.length ≥ init.length + 1` となり measure が減少し、
fuel = 0 で停止条件が成立する。停止時は `init.Subperm merged` と `merged.length ≤ init.length`
から `init.Perm merged`、よって `step init ⊆ merged ⊆ init` (set-wise)。 -/
theorem reachClosure_closed_aux {α : Type _} [DecidableEq α]
    (step : List α → List α) (univ : List α)
    (huniv_step : ∀ xs, (∀ x ∈ xs, x ∈ univ) → ∀ y ∈ step xs, y ∈ univ) :
    ∀ (fuel : Nat) (init : List α),
      init.Nodup → (∀ x ∈ init, x ∈ univ) →
      univ.length ≤ fuel + init.length →
      ∀ y ∈ step (reachClosure step init fuel), y ∈ reachClosure step init fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro init hInit_nodup hInit_univ hbound
    have hsub : init ⊆ univ := fun x hx => hInit_univ x hx
    have hsp : List.Subperm init univ := hInit_nodup.subperm hsub
    have hbound' : univ.length ≤ init.length := by simpa using hbound
    have hperm : List.Perm init univ := hsp.perm_of_length_le hbound'
    show ∀ y ∈ step (reachClosure step init 0), y ∈ reachClosure step init 0
    simp only [reachClosure]
    intro y hy
    have hy_univ : y ∈ univ := huniv_step init hInit_univ y hy
    exact hperm.symm.mem_iff.mp hy_univ
  | succ n ih =>
    intro init hInit_nodup hInit_univ hbound
    set merged := listDedup (init ++ step init) with hmerged_def
    have hmerged_nodup : merged.Nodup := listDedup_nodup _
    have hstep_univ : ∀ y ∈ step init, y ∈ univ := huniv_step init hInit_univ
    have hmerged_univ : ∀ x ∈ merged, x ∈ univ := by
      intro x hx
      rw [hmerged_def, mem_listDedup_iff, List.mem_append] at hx
      rcases hx with hx | hx
      · exact hInit_univ x hx
      · exact hstep_univ x hx
    have hinit_merged : ∀ x ∈ init, x ∈ merged := by
      intro x hx
      rw [hmerged_def, mem_listDedup_iff, List.mem_append]
      exact Or.inl hx
    have hstep_merged : ∀ y ∈ step init, y ∈ merged := by
      intro y hy
      rw [hmerged_def, mem_listDedup_iff, List.mem_append]
      exact Or.inr hy
    show ∀ y ∈ step (reachClosure step init (n+1)), y ∈ reachClosure step init (n+1)
    simp only [reachClosure]
    rw [show listDedup (init ++ step init) = merged from rfl]
    by_cases hstop : merged.length ≤ init.length
    · rw [if_pos hstop]
      have hsp : List.Subperm init merged := hInit_nodup.subperm hinit_merged
      have hperm : List.Perm init merged := hsp.perm_of_length_le hstop
      intro y hy
      have hy_merged : y ∈ merged := hstep_merged y hy
      exact hperm.symm.mem_iff.mp hy_merged
    · rw [if_neg hstop]
      apply ih merged hmerged_nodup hmerged_univ
      have hb : univ.length ≤ (n+1) + init.length := hbound
      have hgrow : init.length + 1 ≤ merged.length := by omega
      omega

/-- 閉包補題 (公開ラッパー): `init.Nodup` と `univ.length ≤ fuel` で閉性が成立。 -/
theorem reachClosure_closed_of_fuel_ge {α : Type _} [DecidableEq α]
    (step : List α → List α) (init : List α) (fuel : Nat)
    (univ : List α)
    (hInit_nodup : init.Nodup)
    (hUniv_init : ∀ x ∈ init, x ∈ univ)
    (hUniv_step : ∀ xs y, (∀ x ∈ xs, x ∈ univ) → y ∈ step xs → y ∈ univ)
    (hfuel : univ.length ≤ fuel) :
    ∀ y ∈ step (reachClosure step init fuel), y ∈ reachClosure step init fuel := by
  refine reachClosure_closed_aux step univ
    (fun xs hxs y hy => hUniv_step xs y hxs hy) fuel init hInit_nodup hUniv_init ?_
  exact Nat.le_add_right_of_le hfuel

end Gravity
end S2IL
