-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Processing.CrystalBond
import S2IL.Processing.Rotate

/-!
# Shatter (砕け散り)

結晶の砕け散り (Shatter) 操作の定義。

砕け散りは **脆弱 (Fragile)** な属性を持つ **結晶 (Crystal)** が、
落下や切断によって破壊される現象である。
砕け散り対象の結晶は `Quarter.empty` に置き換わる。

## 砕け散りトリガー

### 切断 (Cutting) による砕け散り
シェイプを南北方向で二分する際、East Half (NE, SE) と West Half (NW, SW) の
**両方に跨がる結合クラスタ** が砕け散る。

### 落下 (Fall) による砕け散り
落下対象となった **脆弱な象限** が属する **結合クラスタ全体** が砕け散る。

## 設計方針

砕け散りはクラスタ全体に伝播する操作であるため、
`CrystalBond` で算出したクラスタ情報を利用して対象位置を決定した後、
それらの位置の象限を `Quarter.empty` に置き換える。

仕様の詳細は `docs/shapez2/crystal-shatter.md` を参照。
-/

namespace Shape

-- ============================================================
-- 基本操作: 象限の一括クリア
-- ============================================================

/-- 指定された位置のリストに含まれる全象限を `Quarter.empty` に置き換える -/
def clearPositions (s : Shape) (positions : List QuarterPos) : Shape :=
    positions.foldl (fun acc pos => pos.setQuarter acc .empty) s

-- ============================================================
-- 切断時の砕け散り (Phase 5)
-- ============================================================

/-- 切断により砕け散る象限位置のリストを返す。
    東西に跨がる結合クラスタの全象限が対象となる -/
def shatterTargetsOnCut (s : Shape) : List QuarterPos :=
    let clusters := CrystalBond.allCrystalClusters s
    -- 東西に跨がるクラスタを抽出し、その全象限を結合する
    clusters.foldl (fun targets cluster =>
        let hasEast := cluster.any fun p => p.dir.isEast
        let hasWest := cluster.any fun p => p.dir.isWest
        if hasEast && hasWest then
            targets ++ cluster
        else
            targets
    ) []

/-- 切断前の砕け散りを適用した結果のシェイプを返す -/
def shatterOnCut (s : Shape) : Shape :=
    s.clearPositions s.shatterTargetsOnCut

-- ============================================================
-- 落下時の砕け散り (Phase 6)
-- ============================================================

/-- 落下により砕け散る象限位置のリストを返す。
    落下対象の脆弱な象限が属する結合クラスタの全象限が対象となる -/
def shatterTargetsOnFall (s : Shape) (fallingPositions : List QuarterPos)
        : List QuarterPos :=
    -- 落下対象のうち、脆弱な象限を抽出
    let fragilePositions := fallingPositions.filter fun p =>
        match p.getQuarter s with
        | some q => q.isFragile
        | none   => false
    -- 各脆弱位置のクラスタを求め、重複を除去しながら収集する
    let clusters := CrystalBond.allCrystalClusters s
    clusters.foldl (fun targets cluster =>
        -- このクラスタに脆弱な落下対象が含まれているか
        let containsFragileFalling := cluster.any fun p =>
            fragilePositions.any (· == p)
        if containsFragileFalling then
            targets ++ cluster
        else
            targets
    ) []

/-- 落下前の砕け散りを適用した結果のシェイプを返す -/
def shatterOnFall (s : Shape) (fallingPositions : List QuarterPos) : Shape :=
    s.clearPositions (s.shatterTargetsOnFall fallingPositions)

-- ============================================================
-- 180° 回転と shatterOnCut の可換性
-- ============================================================

/-- 切断砕け散りと 180° 回転は可換である。
    すなわち、先に砕け散らせてから 180° 回転しても、
    先に 180° 回転してから砕け散らせても結果は同じである -/
theorem shatterOnCut_rotate180_comm (s : Shape) :
        s.shatterOnCut.rotate180 = s.rotate180.shatterOnCut := by
    sorry

/-- 落下砕け散りと 180° 回転は可換である。
    落下位置も一緒に 180° 回転する必要がある -/
theorem shatterOnFall_rotate180_comm (s : Shape) (ps : List QuarterPos) :
        (s.shatterOnFall ps).rotate180 =
        s.rotate180.shatterOnFall (ps.map QuarterPos.rotate180) := by
    sorry

end Shape
