-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel
import S2IL.Operations.Settled
import S2IL.Operations.Gravity.Internal.BFS

/-!
# S2IL.Operations.Gravity.Defs

落下機構 (Phase D-10B) — Layer A 部の **計算的** 定義群。

## 概要

[gravity-proof-plan.md §3.5 (d) / §6.1 / §7](../../../docs/plans/gravity-proof-plan.md)
の採用モデルを `def`（computable）で実装する。

| 定義 | 内容 |
|---|---|
| `FallingUnit` | `cluster (positions : List QuarterPos)` または `pin (p : QuarterPos)` |
| `floatingClusters` / `floatingPins` / `floatingUnits` | 浮遊要素の列挙 |
| `shareDirection` / `shouldProcessBefore` | 処理順序の核 |
| `landingDistance` | 仕様 §6.3 に基づく最小着地距離 |
| `Shape.gravity` | 落下処理本体（fold ベース） |

## 構造結合 vs 結晶結合

[`docs/shapez2/falling.md` §2.2](../../../docs/shapez2/falling.md):
構造結合は **結合能力 (`canFormBond`)** を持つ任意の非空非ピン象限間の隣接で成立する
（種別・色を問わない）。本ファイルではこれを `structuralNeighbors` で表現する。
`Kernel.IsBonded` は **結晶結合（crystal-shatter 用）** であり、本ファイルでは利用しない。

## 着地距離

[`docs/shapez2/falling.md` §6.3](../../../docs/shapez2/falling.md):
`d(U)` は「`U` を 1 レイヤずつ下方移動し、最初に着地条件を満たす最小 `d ≥ 1`」。
着地条件は ① 最下層到達 ② 直下の障害物との接触。本ファイルでは
`landingCondition` / `landingDistance` で表現する。
-/

namespace S2IL
namespace Gravity

-- ============================================================
-- 隣接列挙
-- ============================================================

/-- `p` から **構造結合** で結ばれる候補位置。
    `falling.md §2.2`: `canFormBond` を両端に持つ隣接（同レイヤ円環 + 上下同方角）。 -/
def structuralNeighbors (s : Shape) (p : QuarterPos) : List QuarterPos :=
  let qp := QuarterPos.getQuarter s p
  if !qp.canFormBond then []
  else
    let same := horizontalAdj p |>.filter
                  (fun q => (QuarterPos.getQuarter s q).canFormBond)
    let above : List QuarterPos :=
      if (QuarterPos.getQuarter s (p.1 + 1, p.2)).canFormBond then
        [(p.1 + 1, p.2)] else []
    let below : List QuarterPos :=
      if p.1 ≥ 1 ∧ (QuarterPos.getQuarter s (p.1 - 1, p.2)).canFormBond then
        [(p.1 - 1, p.2)] else []
    same ++ above ++ below

/-! ### `groundingNeighbors` の 3 ブランチ分解

`groundingNeighbors` は次の 3 ブランチの単純結合に分解される
（Phase D-10D §1 edge correspondence で MECE な case 分析を行うため）:

| ブランチ | 内容 |
|---|---|
| `groundingNeighborsUp` | 上方向 vertical contact (`(p.1+1, p.2)`、両非空) |
| `groundingNeighborsHoriz` | 同層 adjacent contact (`(p.1, p.2±1)`、両非空非ピン) |
| `groundingNeighborsDown` | 下方向 bond (`(p.1-1, p.2)`、両 crystal) |

[`Operations.Settled.IsGroundingEdge`](Settled.lean) の computable shadow。
-/

/-- 上方向 vertical contact ブランチ。両非空（ピン許容）。 -/
def groundingNeighborsUp (s : Shape) (p : QuarterPos) : List QuarterPos :=
  if (QuarterPos.getQuarter s p).isEmpty then []
  else if (QuarterPos.getQuarter s (p.1 + 1, p.2)).isEmpty then []
  else [(p.1 + 1, p.2)]

/-- 同層 adjacent contact ブランチ。両非空・両非ピン。 -/
def groundingNeighborsHoriz (s : Shape) (p : QuarterPos) : List QuarterPos :=
  let qp := QuarterPos.getQuarter s p
  if qp.isEmpty ∨ qp = .pin then []
  else
    horizontalAdj p |>.filter (fun q =>
      let qq := QuarterPos.getQuarter s q
      decide (¬ qq.isEmpty ∧ qq ≠ Quarter.pin))

/-- 下方向 bond ブランチ。両 crystal、`p.1 ≥ 1`。 -/
def groundingNeighborsDown (s : Shape) (p : QuarterPos) : List QuarterPos :=
  if (QuarterPos.getQuarter s p).isCrystal ∧ p.1 ≥ 1
      ∧ (QuarterPos.getQuarter s (p.1 - 1, p.2)).isCrystal then
    [(p.1 - 1, p.2)] else []

/-- `p` から `IsGroundingEdge` 経由で到達可能な前進方向の隣接位置（接地 BFS 用）。 -/
def groundingNeighbors (s : Shape) (p : QuarterPos) : List QuarterPos :=
  groundingNeighborsUp s p ++ groundingNeighborsHoriz s p ++ groundingNeighborsDown s p

-- ============================================================
-- 非空位置・layer 0 root 列挙
-- ============================================================

/-- `s` 内の全非空位置（`allValid` の filter）。 -/
def nonEmptyPositions (s : Shape) : List QuarterPos :=
  (QuarterPos.allValid s).filter
    (fun p => ! (QuarterPos.getQuarter s p).isEmpty)

/-- 接地探索の root: layer 0 の非空位置。 -/
def layer0Roots (s : Shape) : List QuarterPos :=
  Direction.all.filterMap (fun d =>
    let p : QuarterPos := (0, d)
    if (QuarterPos.getQuarter s p).isEmpty then none else some p)

-- ============================================================
-- isGroundedFast: computable BFS による接地判定
-- ============================================================

/-- `p` が接地している（`Operations.Settled.IsGrounded` の computable shadow）。
    Prop 層との同値性は Phase D-10D で証明する。 -/
def isGroundedFast (s : Shape) (p : QuarterPos) : Bool :=
  let roots := layer0Roots s
  let fuel := s.length * 4 + 4
  let step := fun current => current.flatMap (groundingNeighbors s)
  let reachable := reachClosure step roots fuel
  decide (p ∈ reachable)

-- ============================================================
-- 構造クラスタ計算（結合能力ベースの BFS）
-- ============================================================

/-- `p` を含む構造クラスタ（`structuralNeighbors` の BFS）。 -/
def structuralCluster (s : Shape) (p : QuarterPos) : List QuarterPos :=
  let fuel := s.length * 4 + 4
  let step := fun current => current.flatMap (structuralNeighbors s)
  reachClosure step [p] fuel

/-- 構造クラスタの partition 補助再帰: 候補位置 `xs` を順に取り出し、
    各要素を root とした `structuralCluster` を `acc` に push し、その cluster に
    含まれる位置を残候補から除外する。`fuel` で停止性を保証。 -/
def structuralClustersPartition (s : Shape) :
    List QuarterPos → List (List QuarterPos) → Nat → List (List QuarterPos)
  | _, acc, 0 => acc
  | [], acc, _ => acc
  | p :: rest, acc, fuel + 1 =>
    let cl := structuralCluster s p
    let newRest := rest.filter (· ∉ cl)
    structuralClustersPartition s newRest (cl :: acc) fuel

/-- 全 `canFormBond` 位置を構造結合の同値類で分割。 -/
def structuralClusters (s : Shape) : List (List QuarterPos) :=
  let bondablePos := nonEmptyPositions s |>.filter
    (fun p => (QuarterPos.getQuarter s p).canFormBond)
  structuralClustersPartition s bondablePos [] (s.length * 4 + 4)

-- ============================================================
-- FallingUnit
-- ============================================================

/-- 落下単位。構造クラスタまたは単独ピン。 -/
inductive FallingUnit
  | cluster (positions : List QuarterPos)
  | pin (p : QuarterPos)
  deriving DecidableEq, Repr

namespace FallingUnit

/-- 単位に含まれる位置リスト。 -/
def positions : FallingUnit → List QuarterPos
  | .cluster ps => ps
  | .pin p => [p]

/-- 単位の最小レイヤ。空 cluster は 0（実用上発生しない安全値）。 -/
def minLayer (u : FallingUnit) : Nat :=
  match u with
  | .cluster ps =>
      match ps with
      | [] => 0
      | p :: rest => rest.foldr (fun q acc => Nat.min q.1 acc) p.1
  | .pin p => p.1

/-- 方角列共有: 共通する方角を持つか。 -/
def shareDirection (u v : FallingUnit) : Bool :=
  u.positions.any (fun p => v.positions.any (fun q => decide (p.2 = q.2)))

/-- 処理優先（`shareDirection ∧ minLayer 厳密小`）。 -/
def shouldProcessBefore (u v : FallingUnit) : Bool :=
  shareDirection u v && decide (u.minLayer < v.minLayer)

end FallingUnit

-- ============================================================
-- floatingClusters / floatingPins / floatingUnits
-- ============================================================

/-- クラスタ全体が浮遊か（接地構成員 0）。 -/
def clusterFloating (s : Shape) (cl : List QuarterPos) : Bool :=
  cl.all (fun p => ! isGroundedFast s p)

/-- 浮遊構造クラスタ群。 -/
def floatingClusters (s : Shape) : List (List QuarterPos) :=
  (structuralClusters s).filter (clusterFloating s)

/-- 浮遊ピン位置（個別判定）。 -/
def floatingPins (s : Shape) : List QuarterPos :=
  nonEmptyPositions s |>.filter (fun p =>
    decide (QuarterPos.getQuarter s p = Quarter.pin) && ! isGroundedFast s p)

/-- 浮遊落下単位の全列挙。 -/
def floatingUnits (s : Shape) : List FallingUnit :=
  (floatingClusters s).map FallingUnit.cluster ++ (floatingPins s).map FallingUnit.pin

-- ============================================================
-- 着地条件・着地距離（`falling.md §6.3`）
-- ============================================================

/-- 着地条件: 単位 `u` を `d` 段下げた状態で「最下層到達」または「直下障害物」。 -/
def landingCondition (obs : Shape) (u : FallingUnit) (d : Nat) : Bool :=
  u.positions.any (fun q =>
    decide (q.1 = d) ||
      (decide (q.1 > d) &&
        ! (QuarterPos.getQuarter obs (q.1 - d - 1, q.2)).isEmpty))

/-- 着地距離: `d ≥ 1` で `landingCondition` を満たす最小値（上限 `minLayer`）。 -/
def landingDistance (obs : Shape) (u : FallingUnit) : Nat :=
  let m := u.minLayer
  let candidates := (List.range (m + 1)).filter (· ≥ 1)
  (candidates.find? (fun d => landingCondition obs u d)).getD m

-- ============================================================
-- 配置: 単位 `u` を `origS` の内容で `obs` に書き戻す
-- ============================================================

/-- `origS` の `p` における Quarter 内容を取得。 -/
private def quarterAt (origS : Shape) (p : QuarterPos) : Quarter :=
  QuarterPos.getQuarter origS p

/-- 単位 `u` を距離 `d` で配置（`origS` から内容を取り、`obs` に書き込む）。 -/
def placeUnit (origS : Shape) (obs : Shape) (u : FallingUnit) (d : Nat) : Shape :=
  u.positions.foldl (fun acc p =>
    let q := quarterAt origS p
    let newPos : QuarterPos := (p.1 - d, p.2)
    QuarterPos.setQuarter acc newPos q) obs

/-- 単位 `u` を着地距離だけ降ろして `obs` に配置。 -/
def stepUnit (origS : Shape) (obs : Shape) (u : FallingUnit) : Shape :=
  let d := landingDistance obs u
  placeUnit origS obs u d

-- ============================================================
-- 障害物初期化と全体処理
-- ============================================================

/-- 単位処理順（`minLayer` 昇順）。
    `shouldProcessBefore` の必要条件「同列で minLayer 小が先」を包摂する全順序。 -/
def sortedUnits (units : List FallingUnit) : List FallingUnit :=
  units.mergeSort (fun a b => decide (a.minLayer ≤ b.minLayer))

/-- 落下単位の **元位置** を全て空に置換した障害物シェイプ。 -/
def initialObstacle (s : Shape) (units : List FallingUnit) : Shape :=
  Shape.clearPositions s (units.flatMap FallingUnit.positions)

end Gravity

-- ============================================================
-- Shape.gravity 本体
-- ============================================================

namespace Shape

open S2IL.Gravity

/-- 落下処理本体。`def` で計算可能。
    [`gravity-proof-plan.md §3.5 (d) / §7 D-10B`](../../../docs/plans/gravity-proof-plan.md)
    の採用モデルを fold で具体化する。 -/
def gravity (s : Shape) : Shape :=
  let units := floatingUnits s
  let order := sortedUnits units
  let obs0 := initialObstacle s units
  let placed := order.foldl (fun acc u => stepUnit s acc u) obs0
  placed.normalize

end Shape

end S2IL
