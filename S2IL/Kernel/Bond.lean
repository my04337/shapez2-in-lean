-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape
import S2IL.Kernel.BFS
import S2IL.Kernel.Transform

/-!
# S2IL.Kernel.Bond

結晶結合条件と BFS ベースのクラスタ算出。

## 公開 API

- `isBonded` / `isBondedInLayer` / `isBondedCrossLayer`
- `cluster` — Finset 版（証明用）
- `clusterList` — List 版（計算用）
- `allClusters`

回転等変性（`_rotateCW_comm`）は CW 版のみ axiom、180° / CCW は `Internal/Rotate180Lemmas` の系。

## Internal

- `S2IL.Kernel.Internal.BondImpl`         — 結合判定の実装補助
- `S2IL.Kernel.Internal.Rotate180Lemmas` — 回転と setDir/getDir の可換性系
-/

namespace S2IL

axiom isBondedInLayer : Shape → QuarterPos → QuarterPos → Bool
axiom isBondedCrossLayer : Shape → QuarterPos → QuarterPos → Bool
axiom isBonded : Shape → QuarterPos → QuarterPos → Bool

axiom isBonded_symm (s : Shape) (p q : QuarterPos) :
    isBonded s p q = isBonded s q p

axiom isBonded_rotateCW (s : Shape) (p q : QuarterPos) :
    isBonded s.rotateCW p.rotateCW q.rotateCW = isBonded s p q

-- NOTE: `isBonded_rotate180` / `isBonded_rotateCCW` は Phase C で
-- `QuarterPos.rotate180` / `rotateCCW` を CW 系として定義した後に
-- 1 行系として追加する。

/-- 指定位置から BFS で到達可能な位置の集合（計算用リスト）。 -/
axiom clusterList : Shape → QuarterPos → List QuarterPos

/-- 指定位置から BFS で到達可能な位置の集合（証明用 `List`）。
    Phase C で `Finset` 化を検討する。 -/
axiom cluster : Shape → QuarterPos → List QuarterPos

/-- シェイプ内の全クラスタを列挙する。 -/
axiom allClusters : Shape → List (List QuarterPos)

/-- クラスタ健全性。 -/
axiom cluster_sound (s : Shape) (start p : QuarterPos) :
    p ∈ cluster s start → GenericReachable (isBonded s) start p

/-- クラスタ完全性。 -/
axiom cluster_complete (s : Shape) (start p : QuarterPos) :
    s.layerCount > 0 → GenericReachable (isBonded s) start p →
    p ∈ cluster s start

/-- cluster の CW 等変性。 -/
axiom cluster_rotateCW (s : Shape) (start : QuarterPos) :
    cluster s.rotateCW start.rotateCW = (cluster s start).map QuarterPos.rotateCW

end S2IL
