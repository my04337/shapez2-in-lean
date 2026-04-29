-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape

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

end Gravity
end S2IL
