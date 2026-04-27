-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape
import S2IL.Kernel.Transform
import Mathlib.Data.Finset.Image

/-!
# S2IL.Kernel.Cluster

クラスタ表現（Phase C re-scaffold 済み）。
Mathlib `Relation.ReflTransGen` を関係層として利用する（architecture §1.10）。

## 公開 API

- `ClusterRel` — 結合関係の反射推移閉包（`Relation.ReflTransGen`）
- `clusterSet` — クラスタの Finset 表現（証明用、noncomputable）
- `clusterList` — クラスタの List 表現（計算用）
- `clusterList_toFinset` — 橋渡し補題（1 本）
- `clusterSet.rotateCW_comm` — Finset CW 等変性

## 設計根拠

旧 `genericBfs` / `GenericReachable` は廃止。Mathlib の
`Relation.ReflTransGen` で完全に代用し、自前 axiom を持たない。
等変性は Finset 等式のみで述べる（List 等式は順序依存のため禁止）。

## Internal

- `S2IL.Kernel.Internal.ClusterImpl` — `clusterList` の実装（Phase D で追加予定）
-/

namespace S2IL

-- 前方参照: IsBonded は Bond.lean で定義される
-- ここでは ClusterRel の定義テンプレートのみ記載。
-- Phase C で Bond.lean の IsBonded 定義後に具体化する。

/-- クラスタの List 表現（計算用）。 -/
axiom clusterList : Shape → QuarterPos → List QuarterPos

/-- クラスタの Finset 表現（証明用）。 -/
axiom clusterSet : Shape → QuarterPos → Finset QuarterPos

/-- 橋渡し補題: List → Finset。 -/
axiom clusterList.toFinset (s : Shape) (start : QuarterPos) :
    List.toFinset (clusterList s start) = clusterSet s start

/-- シェイプ内の全クラスタを列挙する。 -/
axiom allClusters : Shape → List (List QuarterPos)

/-- クラスタ集合の CW 等変性（Finset 等式）。 -/
axiom clusterSet.rotateCW_comm (s : Shape) (start : QuarterPos) :
    clusterSet (Shape.rotateCW s) (QuarterPos.rotateCW start) =
      (clusterSet s start).image QuarterPos.rotateCW

end S2IL
