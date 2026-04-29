-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity.Defs

/-!
# S2IL.Operations.Gravity.Internal.ShareDirection

落下単位 (`FallingUnit`) の方角共有関係と well-founded 関係。

## 公開 API（Internal、外部 import 禁止）

- `FallingUnit.shareDirection.symm` — 共有関係の対称性
- `FallingUnit.precedes`            — `shareDirection ∧ minLayer 厳密小` の半順序
- `FallingUnit.precedes_wf`         — `precedes` の well-founded 性
  （`Nat.lt_wfRel` を `minLayer` で持ち上げ）

## 設計根拠（[gravity-proof-plan.md §6.4](../../../../docs/plans/gravity-proof-plan.md)）

`dropOf U s` を well-founded 再帰で定義する際、measure として
「同方角列を共有しかつ minLayer 厳密小の単位」のみを参照させる必要がある。
本ファイルはその関係定義とWF 性を切り出す（D-10B では実利用前の足場として用意）。
-/

namespace S2IL
namespace Gravity
namespace FallingUnit

open S2IL.Gravity.FallingUnit

/-- `shareDirection` は対称。 -/
theorem shareDirection.symm (u v : FallingUnit) :
    shareDirection u v = shareDirection v u := by
  classical
  unfold shareDirection
  -- 両辺は ∃ p ∈ u.positions, ∃ q ∈ v.positions, p.2 = q.2
  -- どちらも同値のため `decide` で閉じる… のは無理。代わりに simp + Bool.eq_iff
  -- 単純な書き換え
  by_cases h : u.positions.any (fun p => v.positions.any (fun q => decide (p.2 = q.2)))
  · -- LHS = true
    have hL : (u.positions.any (fun p => v.positions.any (fun q => decide (p.2 = q.2)))) = true := by
      simpa using h
    have hR : (v.positions.any (fun p => u.positions.any (fun q => decide (p.2 = q.2)))) = true := by
      rcases (List.any_eq_true.mp hL) with ⟨p, hpu, hpv⟩
      rcases (List.any_eq_true.mp hpv) with ⟨q, hqv, hpq⟩
      have hpq' : p.2 = q.2 := of_decide_eq_true hpq
      apply List.any_eq_true.mpr
      refine ⟨q, hqv, ?_⟩
      apply List.any_eq_true.mpr
      exact ⟨p, hpu, decide_eq_true hpq'.symm⟩
    rw [hL, hR]
  · -- LHS = false
    have hL : (u.positions.any (fun p => v.positions.any (fun q => decide (p.2 = q.2)))) = false := by
      simpa [Bool.not_eq_true] using h
    have hR : (v.positions.any (fun p => u.positions.any (fun q => decide (p.2 = q.2)))) = false := by
      apply Bool.eq_false_iff.mpr
      intro hR
      apply (Bool.eq_false_iff.mp hL)
      rcases (List.any_eq_true.mp hR) with ⟨q, hqv, hqu⟩
      rcases (List.any_eq_true.mp hqu) with ⟨p, hpu, hpq⟩
      have hpq' : q.2 = p.2 := of_decide_eq_true hpq
      apply List.any_eq_true.mpr
      refine ⟨p, hpu, ?_⟩
      apply List.any_eq_true.mpr
      exact ⟨q, hqv, decide_eq_true hpq'.symm⟩
    rw [hL, hR]

/-- 落下単位の処理優先順序の核（well-founded 関係用）:
    「方角列を共有し、`minLayer` が厳密に小さい」とき先行する。 -/
def precedes (u v : FallingUnit) : Prop :=
  shareDirection u v = true ∧ u.minLayer < v.minLayer

/-- `precedes` は well-founded（`minLayer` 上の `<` から持ち上げ）。 -/
theorem precedes_wf : WellFounded (precedes) := by
  -- minLayer をキーとする measure からの well-founded を直接構成
  apply WellFounded.intro
  intro u
  -- Acc on `u` — 帰納で n = u.minLayer に対する強帰納法
  generalize hn : u.minLayer = n
  induction n using Nat.strong_induction_on generalizing u with
  | _ n ih =>
    refine ⟨u, fun v hv => ?_⟩
    -- v precedes u → v.minLayer < u.minLayer = n
    have hlt : v.minLayer < u.minLayer := hv.2
    rw [hn] at hlt
    exact ih _ hlt v rfl

instance : WellFoundedRelation FallingUnit where
  rel := precedes
  wf := precedes_wf

end FallingUnit
end Gravity
end S2IL
