-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.QuarterPos

/-!
# CrystalBond (結晶結合)

結晶の結合 (Bond) と結合クラスタ (Bonded Cluster) の算出。

## 結合条件

結晶同士は以下の条件で結合する:

### 同レイヤ内
- 隣接する方角 (NE↔SE, SE↔SW, SW↔NW, NW↔NE) にある
- 両方が結晶 (`Quarter.crystal`) である
- **同じ色** である

### 上下レイヤ間
- 同じ方角に位置する
- 両方が結晶である
- **色は問わない**

## 結合クラスタ

結合は推移的であり、結合関係で到達可能な結晶の集合が1つのクラスタを形成する。
クラスタの算出はシェイプ内のグラフ上での到達可能性探索（BFS）で行う。
頂点数はレイヤ数 × 4 方角。
-/

namespace CrystalBond

-- ============================================================
-- 結合条件の判定
-- ============================================================

/-- 同レイヤ内で2つの象限位置が結合しているかを判定する。
    同レイヤ内では隣接する同色の結晶同士が結合する -/
def isBondedInLayer (s : Shape) (p1 p2 : QuarterPos) : Bool :=
    p1.layer == p2.layer &&
    p1.dir.adjacent p2.dir &&
    match p1.getQuarter s, p2.getQuarter s with
    | some (.crystal c1), some (.crystal c2) => c1 == c2
    | _, _ => false

/-- 上下レイヤ間で2つの象限位置が結合しているかを判定する。
    上下レイヤ間では同方角の結晶同士が色を問わず結合する -/
def isBondedCrossLayer (s : Shape) (p1 p2 : QuarterPos) : Bool :=
    LayerIndex.verticallyAdjacent p1.layer p2.layer &&
    p1.dir == p2.dir &&
    match p1.getQuarter s, p2.getQuarter s with
    | some (.crystal _), some (.crystal _) => true
    | _, _ => false

/-- 2つの象限位置が結合しているかを判定する（同レイヤ内または上下レイヤ間） -/
def isBonded (s : Shape) (p1 p2 : QuarterPos) : Bool :=
    isBondedInLayer s p1 p2 || isBondedCrossLayer s p1 p2

-- ============================================================
-- 結合クラスタの算出 (BFS)
-- ============================================================

/-- BFS で指定位置から到達可能な全結晶象限を返す。
    `visited` は既に訪問済みの位置、`queue` は処理待ちの位置 -/
private def bfs (s : Shape) (allPos : List QuarterPos) (visited queue : List QuarterPos)
        : (fuel : Nat) → List QuarterPos
    | 0 => visited
    | fuel + 1 =>
        match queue with
        | [] => visited
        | pos :: rest =>
            if visited.any (· == pos) then
                bfs s allPos visited rest fuel
            else
                let newVisited := pos :: visited
                -- pos と結合している未訪問の位置を探索キューに追加
                let neighbors := allPos.filter fun p =>
                    isBonded s pos p && !(newVisited.any (· == p))
                bfs s allPos newVisited (rest ++ neighbors) fuel

/-- 指定位置から到達可能な結合クラスタを返す -/
def crystalCluster (s : Shape) (pos : QuarterPos) : List QuarterPos :=
    let allPos := QuarterPos.allValid s
    -- fuel は最大頂点数の2乗で十分
    let n := s.layerCount * 4
    bfs s allPos [] [pos] (n * n)

/-- シェイプ内の全結合クラスタを返す。各クラスタは `QuarterPos` のリスト -/
def allCrystalClusters (s : Shape) : List (List QuarterPos) :=
    let allPos := QuarterPos.allValid s
    -- 結晶位置のみを対象にする
    let crystalPositions := allPos.filter fun p =>
        match p.getQuarter s with
        | some (.crystal _) => true
        | _ => false
    -- 各結晶位置についてクラスタを算出し、重複を除去する
    crystalPositions.foldl (fun clusters pos =>
        -- この位置が既存のクラスタに含まれているか確認
        if clusters.any (fun cluster => cluster.any (· == pos)) then
            clusters
        else
            let cluster := crystalCluster s pos
            clusters ++ [cluster]
    ) []

end CrystalBond
