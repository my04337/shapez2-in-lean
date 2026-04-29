-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity.Defs
import S2IL.Operations.Gravity.Internal.Collision

/-!
# S2IL.Operations.Gravity.Behavior

落下機構の **振る舞い系** 補題（Phase D-10C）。

## 公開 API

| 補題 | 内容 |
|---|---|
| `Gravity.landingDistance_le_minLayer` | `landingDistance obs u ≤ u.minLayer`（`dropOf_le_minLayer`） |
| `Shape.gravity.of_isSettled'` | `IsSettled s ∧ IsNormalized s → gravity s = s`（不動点性） |

## 設計メモ

[`gravity-proof-plan.md §1.2 / §6.2 / §7 D-10C`](../../../../docs/plans/gravity-proof-plan.md)
の不動点性は、当初 `IsSettled s → gravity s = s` の形で立てられていた。
しかし `gravity` 末尾の `Shape.normalize` は **末尾空レイヤを必ず除去** する一方、
`IsSettled` は末尾空レイヤを禁止しない（[`Operations.Settled`](../Settled.lean) §2.1）。
反例: `s = [L_grounded, L_empty]` は `IsSettled` だが `gravity s = [L_grounded] ≠ s`。

このため D-10C では次のリファインを採用する:

1. **シグネチャ強化**: `IsNormalized s` を追加仮定とする
2. 1 入力で `floatingUnits = []` が示せるブリッジ補題 `floatingUnits_eq_nil_of_isSettled`
   を導入（D-10D の BFS 完全性で証明、現状は axiom）

`gravity.isSettled` 側の安定性主定理（D-10D）でブリッジを theorem 化したとき、
本ファイルの `of_isSettled'` も axiom-free になる。

## ブリッジ axiom

`isGroundedFast` (Bool BFS) と `IsGrounded` (Prop ReflTransGen) の同値性、および
`structuralCluster` の構造不変は Phase D-10D の `Internal/Collision.lean` で扱う。
本ファイルでは中間結果として 1 本の axiom に集約する。
-/

namespace S2IL
namespace Gravity

open S2IL.Gravity.FallingUnit

-- ============================================================
-- §1. landingDistance ≤ minLayer
-- ============================================================

/-- 着地距離は単位の最小レイヤを超えない（`dropOf_le_minLayer` の実装版）。
    `landingDistance` は `find?` で `range (m+1) ∩ ≥1` 内を探索し、
    候補が無いときは `getD m` で `m` にフォールバックするため、常に `≤ m`。 -/
theorem landingDistance_le_minLayer (obs : Shape) (u : FallingUnit) :
    landingDistance obs u ≤ u.minLayer := by
  classical
  -- 抽象ヘルパー: opt の中身が常に ≤ m なら getD m も ≤ m
  have key : ∀ {opt : Option Nat}, (∀ d, opt = some d → d ≤ u.minLayer) →
      opt.getD u.minLayer ≤ u.minLayer := by
    intro opt h
    cases opt with
    | none => simp
    | some d => simpa using h d rfl
  -- `landingDistance` を展開してから抽象 helper を適用
  unfold landingDistance
  apply key
  intro d hd
  -- `hd` から `d ∈ List.range (u.minLayer + 1)` を取り出す
  have hmem₀ := List.mem_of_find?_eq_some hd
  -- filter が融合されているか否かに依らず `range` メンバーシップを得る:
  -- 融合形 → `d ∈ range (m+1)`、非融合形 → `d ∈ filter _ (range (m+1))`
  have hmem : d ∈ List.range (u.minLayer + 1) := by
    -- 融合形と非融合形の両方を `List.mem_filter` で吸収
    first
      | exact hmem₀
      | exact (List.mem_filter.mp hmem₀).1
  exact Nat.lt_succ_iff.mp (List.mem_range.mp hmem)

-- ============================================================
-- §2. ブリッジ補題（Phase D-10D-4 で `Internal/Collision.lean` の theorem へ転送）
-- ============================================================

/-- `IsSettled` 入力では落下単位が存在しない。
    `isGroundedFast` (Bool BFS) と `IsGrounded` (Prop) の同値性、および
    `structuralCluster` のメンバが非空・有効である構造不変から導かれる。
    本体は `Internal/Collision.lean` の `Gravity.Internal.floatingUnits_eq_nil_of_isSettled`。 -/
theorem floatingUnits_eq_nil_of_isSettled {s : Shape} :
    IsSettled s → floatingUnits s = [] :=
  Internal.floatingUnits_eq_nil_of_isSettled

end Gravity

-- ============================================================
-- §3. gravity の不動点性
-- ============================================================

namespace Shape

open S2IL.Gravity

/-- `IsSettled` かつ `IsNormalized` な入力に対して `gravity` は不動点。
    [`gravity-proof-plan.md §1.2 / §6.2`](../../../../docs/plans/gravity-proof-plan.md)
    の不動点性（D-10C 確定形: 末尾空レイヤを除外する `IsNormalized` を追加仮定）。 -/
theorem gravity.of_isSettled' {s : Shape}
    (hSettled : IsSettled s) (hNorm : IsNormalized s) :
    Shape.gravity s = s := by
  -- Step 1: floatingUnits = [] (ブリッジ axiom)
  have hu : floatingUnits s = [] := floatingUnits_eq_nil_of_isSettled hSettled
  -- Step 2: gravity 本体の各 let を units = [] で還元
  unfold Shape.gravity
  rw [hu]
  -- sortedUnits [] = []  /  initialObstacle s [] = clearPositions s [] = s
  -- foldl _ s [] = s
  -- 残り: s.normalize = s  ←  IsNormalized s
  show ((sortedUnits []).foldl _ (initialObstacle s [])).normalize = s
  simp [sortedUnits, initialObstacle, Shape.clearPositions, List.flatMap]
  exact Shape.normalize_of_isNormalized s hNorm

end Shape

end S2IL
