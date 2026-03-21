-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Processing.CrystalBond

/-!
# Gravity (落下)

落下 (Gravity) 操作の定義。

浮遊しているシェイプの塊が、支えを得るまで下方に移動する。
仕様の詳細は `docs/shapez2/falling.md` を参照。

## 概要

1. 構造クラスタと孤立ピンを算出する
2. 接地判定を行い、浮遊している落下単位を列挙する
3. 落下単位を下位優先でソートする
4. 各落下単位の着地位置を逐次算出し、障害物シェイプを更新する
5. 正規化して返す

## 積層 (Stacking) との連携

`gravity` 関数は任意のシェイプに対して落下処理を適用する汎用関数であり、
積層操作のサブプロセスとして利用できる。
積層操作は以下の流れで `gravity` を呼び出す想定:

1. 上シェイプを下シェイプの上に単純配置する
2. 砕け散り処理 (`shatterOnFall`) を適用する
3. `gravity` で落下処理を実行する
4. `truncate` でレイヤ数制限を適用する（必要に応じて再度 `gravity`）
-/

namespace Gravity

-- ============================================================
-- 構造結合 (Structural Bond)
-- ============================================================

/-- 2つの象限位置が構造結合しているかを判定する。
    両方が結合能力を持ち (`canFormBond`)、隣接している場合に結合する -/
def isStructurallyBonded (s : Shape) (p1 p2 : QuarterPos) : Bool :=
    match p1.getQuarter s, p2.getQuarter s with
    | some q1, some q2 =>
        q1.canFormBond && q2.canFormBond &&
        (-- 同レイヤ内隣接
         (p1.layer == p2.layer && p1.dir.adjacent p2.dir) ||
         -- 上下レイヤ間隣接（同方角）
         (LayerIndex.verticallyAdjacent p1.layer p2.layer && p1.dir == p2.dir))
    | _, _ => false

-- ============================================================
-- 構造クラスタの算出 (BFS)
-- ============================================================

/-- BFS で構造結合により到達可能な全象限を返す -/
private def structuralBfs (s : Shape) (allPos : List QuarterPos)
        (visited queue : List QuarterPos) : (fuel : Nat) → List QuarterPos
    | 0 => visited
    | fuel + 1 =>
        match queue with
        | [] => visited
        | pos :: rest =>
            if visited.any (· == pos) then
                structuralBfs s allPos visited rest fuel
            else
                let newVisited := pos :: visited
                let neighbors := allPos.filter fun p =>
                    isStructurallyBonded s pos p && !(newVisited.any (· == p))
                structuralBfs s allPos newVisited (rest ++ neighbors) fuel

/-- 指定位置から構造結合で到達可能なクラスタを返す -/
def structuralCluster (s : Shape) (pos : QuarterPos) : List QuarterPos :=
    let allPos := QuarterPos.allValid s
    let n := s.layerCount * 4
    structuralBfs s allPos [] [pos] (n * n)

/-- シェイプ内の全構造クラスタを返す。各クラスタは `QuarterPos` のリスト -/
def allStructuralClusters (s : Shape) : List (List QuarterPos) :=
    let allPos := QuarterPos.allValid s
    -- 結合能力を持つ象限のみを対象にする
    let bondable := allPos.filter fun p =>
        match p.getQuarter s with
        | some q => q.canFormBond
        | none   => false
    bondable.foldl (fun clusters pos =>
        if clusters.any (fun cluster => cluster.any (· == pos)) then
            clusters
        else
            let cluster := structuralCluster s pos
            clusters ++ [cluster]
    ) []

-- ============================================================
-- 孤立ピンの列挙
-- ============================================================

/-- シェイプ内の全孤立ピン位置を返す -/
def allIsolatedPins (s : Shape) : List QuarterPos :=
    let allPos := QuarterPos.allValid s
    allPos.filter fun p =>
        match p.getQuarter s with
        | some .pin => true
        | _         => false

-- ============================================================
-- 接地 (Grounding)
-- ============================================================

/-- 2つの非空象限位置の間に接地接触があるかを判定する -/
def isGroundingContact (s : Shape) (p1 p2 : QuarterPos) : Bool :=
    match p1.getQuarter s, p2.getQuarter s with
    | some q1, some q2 =>
        !q1.isEmpty && !q2.isEmpty &&
        (-- 垂直方向: 同方角・垂直隣接・両方非空（ピンも可）
         (p1.dir == p2.dir && LayerIndex.verticallyAdjacent p1.layer p2.layer) ||
         -- 水平方向: 同レイヤ・隣接方角・両方非ピン
         (p1.layer == p2.layer && p1.dir.adjacent p2.dir &&
          match q1, q2 with
          | .pin, _ | _, .pin => false
          | _, _ => true))
    | _, _ => false

/-- BFS で接地接触チェーンにより到達可能な全象限を返す -/
private def groundingBfs (s : Shape) (allPos : List QuarterPos)
        (visited queue : List QuarterPos) : (fuel : Nat) → List QuarterPos
    | 0 => visited
    | fuel + 1 =>
        match queue with
        | [] => visited
        | pos :: rest =>
            if visited.any (· == pos) then
                groundingBfs s allPos visited rest fuel
            else
                let newVisited := pos :: visited
                let neighbors := allPos.filter fun p =>
                    isGroundingContact s pos p && !(newVisited.any (· == p))
                groundingBfs s allPos newVisited (rest ++ neighbors) fuel

/-- レイヤ 0 の非空象限から接地接触チェーンで到達可能な全位置を返す -/
def groundedPositions (s : Shape) : List QuarterPos :=
    let allPos := QuarterPos.allValid s
    -- レイヤ 0 の非空象限をシードとする
    let seeds := allPos.filter fun p =>
        p.layer == 0 &&
        match p.getQuarter s with
        | some q => !q.isEmpty
        | none   => false
    let n := s.layerCount * 4
    groundingBfs s allPos [] seeds (n * n)

/-- 指定位置が接地しているかを判定する -/
def isGrounded (s : Shape) (pos : QuarterPos) : Bool :=
    let grounded := groundedPositions s
    grounded.any (· == pos)

-- ============================================================
-- 落下単位 (Falling Unit) の列挙
-- ============================================================

/-- 落下単位を表す型。構造クラスタまたは孤立ピン -/
inductive FallingUnit where
    /-- 浮遊する構造クラスタ -/
    | cluster (positions : List QuarterPos)
    /-- 浮遊する孤立ピン -/
    | pin (pos : QuarterPos)
    deriving Repr

namespace FallingUnit

/-- 落下単位に含まれる全象限位置を返す -/
def positions : FallingUnit → List QuarterPos
    | cluster ps => ps
    | pin p      => [p]

/-- 落下単位の最小レイヤ番号を返す -/
def minLayer (u : FallingUnit) : Nat :=
    match u.positions with
    | []     => 0
    | p :: rest => rest.foldl (fun acc q => min acc q.layer) p.layer

/-- 落下単位が指定された方角列にレイヤ l の象限を持つかを判定する -/
def hasPositionAt (u : FallingUnit) (layer : Nat) (dir : Direction) : Bool :=
    u.positions.any fun p => p.layer == layer && p.dir == dir

/-- 落下単位が指定された方角列に象限を持つ最小レイヤを返す。なければ none -/
def minLayerAtDir (u : FallingUnit) (dir : Direction) : Option Nat :=
    let layers := u.positions.filterMap fun p =>
        if p.dir == dir then some p.layer else none
    layers.foldl (fun acc l => some (match acc with | some a => min a l | none => l)) none

end FallingUnit

/-- シェイプの全落下単位（浮遊クラスタ + 浮遊ピン）を列挙する -/
def floatingUnits (s : Shape) : List FallingUnit :=
    let grounded := groundedPositions s
    -- 浮遊クラスタ: 全象限が非接地のクラスタ
    let floatingClusters := (allStructuralClusters s).filter fun cluster =>
        cluster.all fun p => !(grounded.any (· == p))
    -- 浮遊ピン: 接地していないピン
    let floatingPins := (allIsolatedPins s).filter fun p =>
        !(grounded.any (· == p))
    let units : List FallingUnit :=
        (floatingClusters.map .cluster) ++ (floatingPins.map .pin)
    units

-- ============================================================
-- ソート (下位優先のトポロジカルソート)
-- ============================================================

/-- 落下単位 A が落下単位 B より先に処理されるべきか判定する。
    共有する方角列において A が B より下位にある場合 true -/
private def shouldProcessBefore (a b : FallingUnit) : Bool :=
    -- 全方角について、共有列での上下関係を確認
    Direction.all.any fun dir =>
        match a.minLayerAtDir dir, b.minLayerAtDir dir with
        | some la, some lb => la < lb
        | _, _ => false

/-- 挿入ソート: u をソート済みリストの適切な位置に挿入する -/
private def insertSorted (u : FallingUnit) (sorted : List FallingUnit)
        : (fuel : Nat) → List FallingUnit
    | 0 => u :: sorted
    | fuel + 1 =>
        match sorted with
        | [] => [u]
        | v :: rest =>
            -- u が v より先に処理されるべきか判定
            if u.minLayer < v.minLayer ||
               (u.minLayer == v.minLayer && shouldProcessBefore u v)
            then u :: v :: rest
            else v :: insertSorted u rest fuel

/-- 落下単位を下位優先でソートする（挿入ソート。最大16象限なので十分） -/
def sortFallingUnits (units : List FallingUnit) : List FallingUnit :=
    units.foldl (fun sorted u => insertSorted u sorted (sorted.length + 1)) []

-- ============================================================
-- 着地位置の算出
-- ============================================================

/-- 障害物シェイプ上で、指定位置が非空かを判定する。
    レイヤ範囲外の場合は false (空扱い) -/
private def isOccupied (obstacle : List Layer) (layer : Nat) (dir : Direction) : Bool :=
    match obstacle[layer]? with
    | some l => !(QuarterPos.getDir l dir).isEmpty
    | none   => false

/-- 落下単位の着地距離を算出する。
    obstacle は障害物シェイプ（レイヤのリスト） -/
def landingDistance (u : FallingUnit) (obstacle : List Layer) : Nat :=
    let positions := u.positions
    -- 最大落下距離は最小レイヤ番号（それ以上落ちると layer < 0 になる）
    let maxDrop := u.minLayer
    -- d=1 から順に着地条件をチェック
    let rec check (d : Nat) (fuel : Nat) : Nat :=
        match fuel with
        | 0 => d  -- 安全策: fuel切れは現在の d で着地
        | fuel + 1 =>
            if d > maxDrop then maxDrop  -- 全象限が layer 0 以下に到達
            else
                let landed := positions.any fun p =>
                    let newLayer := p.layer - d
                    -- ① layer 0 に到達
                    newLayer == 0 ||
                    -- ② 直下に障害物がある
                    (newLayer > 0 && isOccupied obstacle (newLayer - 1) p.dir)
                if landed then d
                else check (d + 1) fuel
    check 1 (maxDrop + 1)

-- ============================================================
-- 障害物シェイプへの配置
-- ============================================================

/-- レイヤリストの指定位置に象限を配置する。必要に応じてレイヤを拡張 -/
private def placeQuarter (layers : List Layer) (layer : Nat) (dir : Direction)
        (q : Quarter) : List Layer :=
    -- レイヤが足りない場合は空レイヤで拡張
    let emptyLayer : Layer := ⟨.empty, .empty, .empty, .empty⟩
    let extended := if layer < layers.length then layers
        else layers ++ List.replicate (layer + 1 - layers.length) emptyLayer
    match extended[layer]? with
    | some l => extended.set layer (QuarterPos.setDir l dir q)
    | none => extended  -- ありえないが安全策

/-- 落下単位の全象限を元のシェイプから取得し、障害物シェイプに配置する -/
private def placeFallingUnit (origShape : Shape) (obstacle : List Layer)
        (u : FallingUnit) (dropDist : Nat) : List Layer :=
    u.positions.foldl (fun obs p =>
        match p.getQuarter origShape with
        | some q => placeQuarter obs (p.layer - dropDist) p.dir q
        | none => obs
    ) obstacle

-- ============================================================
-- 象限の一括除去（clearPositions のローカル版）
-- ============================================================

/-- 指定された位置のリストに含まれる全象限を `Quarter.empty` に置き換える -/
private def removePositions (s : Shape) (positions : List QuarterPos) : Shape :=
    positions.foldl (fun acc pos => pos.setQuarter acc .empty) s

-- ============================================================
-- 落下処理 (Gravity)
-- ============================================================

/-- 落下処理のメインロジック -/
def process (s : Shape) : Option Shape :=
    let units := floatingUnits s
    -- 落下単位が存在しない場合はそのまま返す
    if units.isEmpty then s.normalize
    else
        -- 落下単位を下位優先でソート
        let sorted := sortFallingUnits units
        -- 障害物シェイプを初期化（全落下単位の象限を除去）
        let allFallingPos := sorted.flatMap FallingUnit.positions
        let obstacle := (removePositions s allFallingPos).layers
        -- 各落下単位を逐次処理
        let result := sorted.foldl (fun obs u =>
            let d := landingDistance u obs
            placeFallingUnit s obs u d
        ) obstacle
        -- 正規化して返す
        Shape.ofLayers result |>.bind Shape.normalize

end Gravity

namespace Shape

/-- 落下処理を適用する。浮遊している落下単位を下方に移動させる -/
def gravity (s : Shape) : Option Shape :=
    Gravity.process s

/-- 落下処理を適用し、結果がない場合（全て空）は元のシェイプを返す便利関数 -/
def gravityOrSelf (s : Shape) : Shape :=
    s.gravity.getD s

end Shape
