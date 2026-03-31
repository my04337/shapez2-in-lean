-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Behavior.CrystalBond
import S2IL.Behavior.GenericBfs
import S2IL.Behavior.Rotate180Lemmas
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Finset.Image

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

-- beq_symm / dir_beq_symm は Batteries の BEq.comm に統一

/-- 構造結合は対称的である -/
theorem isStructurallyBonded_symm (s : Shape) (p1 p2 : QuarterPos) :
        isStructurallyBonded s p1 p2 = isStructurallyBonded s p2 p1 := by
    unfold isStructurallyBonded
    generalize p1.getQuarter s = q1
    generalize p2.getQuarter s = q2
    cases q1 with
    | none => cases q2 <;> rfl
    | some v1 => cases q2 with
        | none => rfl
        | some v2 =>
            -- match (some v1, some v2) を簡約する
            dsimp only []
            rw [Bool.and_comm (x := v1.canFormBond) (y := v2.canFormBond)]
            congr 1
            rw [BEq.comm (a := p1.layer),
                Direction.adjacent_symm p1.dir p2.dir,
                LayerIndex.verticallyAdjacent_symm p1.layer p2.layer,
                BEq.comm (a := p1.dir)]

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
def structuralClusterList (s : Shape) (pos : QuarterPos) : List QuarterPos :=
    let allPos := QuarterPos.allValid s
    let n := s.layerCount * 4
    structuralBfs s allPos [] [pos] (n * n)

/-- シェイプ内の全構造クラスタを返す。各クラスタは `QuarterPos` のリスト -/
def allStructuralClustersList (s : Shape) : List (List QuarterPos) :=
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
            let cluster := structuralClusterList s pos
            clusters ++ [cluster]
    ) []

/-- 指定位置から構造結合で到達可能なクラスタを Finset として返す -/
def structuralCluster (s : Shape) (pos : QuarterPos) : Finset QuarterPos :=
    (structuralClusterList s pos).toFinset

/-- シェイプ内の全構造クラスタを Finset のリストとして返す -/
def allStructuralClusters (s : Shape) : List (Finset QuarterPos) :=
    (allStructuralClustersList s).map List.toFinset

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
def groundedPositionsList (s : Shape) : List QuarterPos :=
    let allPos := QuarterPos.allValid s
    -- レイヤ 0 の非空象限をシードとする
    let seeds := allPos.filter fun p =>
        p.layer == 0 &&
        match p.getQuarter s with
        | some q => !q.isEmpty
        | none   => false
    let n := s.layerCount * 4
    -- 複数 seed に対応するため n² + n の fuel を使用
    -- (queue.length ≤ n かつ unvisited ≤ n なので fuel + 1 ≥ seeds.length + n² を満たす)
    groundingBfs s allPos [] seeds (n * n + n)

/-- レイヤ 0 から接地接触チェーンで到達可能な全位置を Finset として返す -/
def groundedPositions (s : Shape) : Finset QuarterPos :=
    (groundedPositionsList s).toFinset

/-- 指定位置が接地しているかを判定する -/
def isGrounded (s : Shape) (pos : QuarterPos) : Bool :=
    pos ∈ groundedPositions s

-- ============================================================
-- 落下単位 (Falling Unit) の列挙
-- ============================================================

/-- 落下単位を表す型。構造クラスタまたは孤立ピン -/
inductive FallingUnit where
    /-- 浮遊する構造クラスタ -/
    | cluster (positions : List QuarterPos)
    /-- 浮遊する孤立ピン -/
    | pin (pos : QuarterPos)
    deriving Repr, DecidableEq, BEq

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

/-- 落下単位が指定された方角列に象限を持つ最小レイヤを返す。なければ none -/
def minLayerAtDir (u : FallingUnit) (dir : Direction) : Option Nat :=
    let layers := u.positions.filterMap fun p =>
        if p.dir == dir then some p.layer else none
    layers.foldl (fun acc l => some (match acc with | some a => min a l | none => l)) none

/-- タイブレーカー: tied ペアの二次ソートキー。
    全方角の minLayerAtDir の合計値（+1、none は 0）。
    - .any 等価 → 同じ値（minLayerAtDir_ext から）
    - rotate180 不変（方角の置換で和は変わらない） -/
def tiebreaker (u : FallingUnit) : Nat :=
    Direction.all.foldl (fun acc d =>
        acc + match u.minLayerAtDir d with | some l => l + 1 | none => 0) 0

end FallingUnit

/-- シェイプの全落下単位（浮遊クラスタ + 浮遊ピン）を列挙する -/
def floatingUnits (s : Shape) : List FallingUnit :=
    let grounded := groundedPositions s
    -- 浮遊クラスタ: 全象限が非接地のクラスタ
    let floatingClusters := (allStructuralClustersList s).filter fun cluster =>
        cluster.all fun p => p ∉ grounded
    -- 浮遊ピン: 接地していないピン
    let floatingPins := (allIsolatedPins s).filter fun p =>
        p ∉ grounded
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

/-- 挿入ソート: u をソート済みリストの適切な位置に挿入する。
    一次キー: shouldProcessBefore、二次キー: tiebreaker (tied ペア用) -/
private def insertSorted (u : FallingUnit) (sorted : List FallingUnit)
        : (fuel : Nat) → List FallingUnit
    | 0 => u :: sorted
    | fuel + 1 =>
        match sorted with
        | [] => [u]
        | v :: rest =>
            -- u が v より先に処理されるべきか判定
            if shouldProcessBefore u v
            then u :: v :: rest
            else if shouldProcessBefore v u then v :: insertSorted u rest fuel
            else -- tied ペア: tiebreaker で決定
                if u.tiebreaker ≤ v.tiebreaker then u :: v :: rest
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
                    isOccupied obstacle (newLayer - 1) p.dir
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
    let extended := if layer < layers.length then layers
        else layers ++ List.replicate (layer + 1 - layers.length) Layer.empty
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
        let obstacle := (s.clearPositions allFallingPos).layers
        -- 各落下単位を逐次処理
        let result := sorted.foldl (fun obs u =>
            let d := landingDistance u obs
            placeFallingUnit s obs u d
        ) obstacle
        -- 正規化して返す
        Shape.ofLayers result |>.bind Shape.normalize

-- ============================================================
-- 180° 回転等変性の基盤補題
-- Rotate180Lemmas.lean に共通補題を集約済み
-- ============================================================

open QuarterPos (getDir_rotate180 getQuarter_rotate180 getQuarter_rotate180_inv)
open Shape (layers_rotate180 clearPositions_rotate180)

/-- isStructurallyBonded は rotate180 で不変 -/
theorem isStructurallyBonded_rotate180 (s : Shape) (p1 p2 : QuarterPos) :
        isStructurallyBonded (s.rotate180) (p1.rotate180) (p2.rotate180) =
        isStructurallyBonded s p1 p2 := by
    simp only [isStructurallyBonded, getQuarter_rotate180]
    simp only [QuarterPos.rotate180, Direction.adjacent_rotate180]
    cases p1.getQuarter s <;> cases p2.getQuarter s <;> try rfl
    rename_i q1 q2
    cases p1.dir <;> cases p2.dir <;> rfl

/-- isGroundingContact は rotate180 で不変 -/
theorem isGroundingContact_rotate180 (s : Shape) (p1 p2 : QuarterPos) :
        isGroundingContact (s.rotate180) (p1.rotate180) (p2.rotate180) =
        isGroundingContact s p1 p2 := by
    simp only [isGroundingContact, getQuarter_rotate180]
    simp only [QuarterPos.rotate180, Direction.adjacent_rotate180]
    cases p1.getQuarter s <;> cases p2.getQuarter s <;> try rfl
    rename_i q1 q2
    cases q1 <;> cases q2 <;> simp only [Quarter.isEmpty] <;> (try rfl) <;>
    simp only [Bool.not_false, Bool.true_and] <;>
    congr 1 <;> cases p1.dir <;> cases p2.dir <;> rfl

-- ============================================================
-- BFS 等変性のヘルパー補題
-- ============================================================

/-- Direction の BEq は rotate180 で保存される -/
private theorem dir_beq_rotate180' (d1 d2 : Direction) :
        (d1.rotate180 == d2.rotate180) = (d1 == d2) := by
    cases d1 <;> cases d2 <;> rfl

/-- QuarterPos の BEq は rotate180 で保存される -/
private theorem quarterPos_beq_rotate180 (p q : QuarterPos) :
        (p.rotate180 == q.rotate180) = (p == q) := by
    show (p.rotate180.layer == q.rotate180.layer && p.rotate180.dir == q.rotate180.dir) =
         (p.layer == q.layer && p.dir == q.dir)
    simp [QuarterPos.rotate180, dir_beq_rotate180']

/-- List.any は rotate180 のマッピングで保存される -/
private theorem list_any_map_rotate180 (l : List QuarterPos) (p : QuarterPos) :
        (l.map QuarterPos.rotate180).any (· == p.rotate180) = l.any (· == p) := by
    rw [List.any_map]
    congr 1
    funext x
    exact quarterPos_beq_rotate180 x p

/-- List.any の cons と rotate180 の関係 -/
private theorem list_any_cons_rotate180 (x : QuarterPos) (l : List QuarterPos)
        (p : QuarterPos) :
        ((x.rotate180 :: l.map QuarterPos.rotate180).any (· == p.rotate180)) =
        ((x :: l).any (· == p)) := by
    simp only [List.any, quarterPos_beq_rotate180, list_any_map_rotate180]

-- ============================================================
-- structuralBfs の rotate180 等変性
-- ============================================================

/-- isStructurallyBonded フィルタの rotate180 マッピング等変性 -/
private theorem filter_isStructurallyBonded_map_rotate180 (s : Shape)
        (pos : QuarterPos) (visited : List QuarterPos)
        (allPos : List QuarterPos) :
        (allPos.map QuarterPos.rotate180).filter (fun p =>
            isStructurallyBonded s.rotate180 pos.rotate180 p &&
            !((pos.rotate180 :: visited.map QuarterPos.rotate180).any (· == p))) =
        (allPos.filter (fun p =>
            isStructurallyBonded s pos p &&
            !((pos :: visited).any (· == p)))).map QuarterPos.rotate180 := by
    induction allPos with
    | nil => rfl
    | cons a as ih =>
        simp only [List.map, List.filter]
        rw [isStructurallyBonded_rotate180, list_any_cons_rotate180]
        cases isStructurallyBonded s pos a && !((pos :: visited).any (· == a)) with
        | true => simp only [List.map]; exact congrArg _ ih
        | false => exact ih

/-- structuralBfs は rotate180 で等変（allPos を map した場合） -/
private theorem structuralBfs_rotate180 (s : Shape)
        (allPos visited queue : List QuarterPos) (fuel : Nat) :
        structuralBfs s.rotate180
            (allPos.map QuarterPos.rotate180)
            (visited.map QuarterPos.rotate180)
            (queue.map QuarterPos.rotate180) fuel =
        (structuralBfs s allPos visited queue fuel).map QuarterPos.rotate180 := by
    induction fuel generalizing visited queue with
    | zero => rfl
    | succ n ih =>
        cases queue with
        | nil => simp [structuralBfs]
        | cons pos rest =>
            show structuralBfs s.rotate180 (allPos.map QuarterPos.rotate180)
                (visited.map QuarterPos.rotate180)
                (pos.rotate180 :: rest.map QuarterPos.rotate180) (n + 1) =
                (structuralBfs s allPos visited (pos :: rest) (n + 1)).map QuarterPos.rotate180
            simp only [structuralBfs]
            rw [list_any_map_rotate180]
            split
            · exact ih visited rest
            · rw [filter_isStructurallyBonded_map_rotate180, ← List.map_append]
              exact ih (pos :: visited) (rest ++ allPos.filter fun p =>
                  isStructurallyBonded s pos p && !((pos :: visited).any (· == p)))

-- ============================================================
-- groundingBfs の rotate180 等変性
-- ============================================================

/-- isGroundingContact フィルタの rotate180 マッピング等変性 -/
private theorem filter_isGroundingContact_map_rotate180 (s : Shape)
        (pos : QuarterPos) (visited : List QuarterPos)
        (allPos : List QuarterPos) :
        (allPos.map QuarterPos.rotate180).filter (fun p =>
            isGroundingContact s.rotate180 pos.rotate180 p &&
            !((pos.rotate180 :: visited.map QuarterPos.rotate180).any (· == p))) =
        (allPos.filter (fun p =>
            isGroundingContact s pos p &&
            !((pos :: visited).any (· == p)))).map QuarterPos.rotate180 := by
    induction allPos with
    | nil => rfl
    | cons a as ih =>
        simp only [List.map, List.filter]
        rw [isGroundingContact_rotate180, list_any_cons_rotate180]
        cases isGroundingContact s pos a && !((pos :: visited).any (· == a)) with
        | true => simp only [List.map]; exact congrArg _ ih
        | false => exact ih

/-- groundingBfs は rotate180 で等変（allPos を map した場合） -/
private theorem groundingBfs_rotate180 (s : Shape)
        (allPos visited queue : List QuarterPos) (fuel : Nat) :
        groundingBfs s.rotate180
            (allPos.map QuarterPos.rotate180)
            (visited.map QuarterPos.rotate180)
            (queue.map QuarterPos.rotate180) fuel =
        (groundingBfs s allPos visited queue fuel).map QuarterPos.rotate180 := by
    induction fuel generalizing visited queue with
    | zero => rfl
    | succ n ih =>
        cases queue with
        | nil => simp [groundingBfs]
        | cons pos rest =>
            show groundingBfs s.rotate180 (allPos.map QuarterPos.rotate180)
                (visited.map QuarterPos.rotate180)
                (pos.rotate180 :: rest.map QuarterPos.rotate180) (n + 1) =
                (groundingBfs s allPos visited (pos :: rest) (n + 1)).map QuarterPos.rotate180
            simp only [groundingBfs]
            rw [list_any_map_rotate180]
            split
            · exact ih visited rest
            · rw [filter_isGroundingContact_map_rotate180, ← List.map_append]
              exact ih (pos :: visited) (rest ++ allPos.filter fun p =>
                  isGroundingContact s pos p && !((pos :: visited).any (· == p)))

-- ============================================================
-- structuralClusterList / groundedPositionsList の rotate180 等変性
-- ============================================================

/-- structuralClusterList を mapped allPos で呼んだ場合の等変性 -/
private theorem structuralClusterList_rotate180_mapped (s : Shape) (pos : QuarterPos) :
        structuralBfs s.rotate180
            ((QuarterPos.allValid s).map QuarterPos.rotate180) []
            [pos.rotate180]
            (s.layerCount * 4 * (s.layerCount * 4)) =
        (structuralClusterList s pos).map QuarterPos.rotate180 := by
    unfold structuralClusterList
    exact structuralBfs_rotate180 s (QuarterPos.allValid s) [] [pos]
        (s.layerCount * 4 * (s.layerCount * 4))

/-- groundedPositionsList を mapped allPos で呼んだ場合の等変性 -/
private theorem groundedPositionsList_rotate180_mapped (s : Shape) :
        let allPos := QuarterPos.allValid s
        let seeds := allPos.filter fun p =>
            p.layer == 0 &&
            match p.getQuarter s with
            | some q => !q.isEmpty
            | none   => false
        groundingBfs s.rotate180
            (allPos.map QuarterPos.rotate180)
            []
            (seeds.map QuarterPos.rotate180)
            (s.layerCount * 4 * (s.layerCount * 4) + s.layerCount * 4) =
        (groundedPositionsList s).map QuarterPos.rotate180 := by
    unfold groundedPositionsList
    exact groundingBfs_rotate180 s (QuarterPos.allValid s) []
        ((QuarterPos.allValid s).filter fun p =>
            p.layer == 0 &&
            match p.getQuarter s with
            | some q => !q.isEmpty
            | none   => false)
        (s.layerCount * 4 * (s.layerCount * 4) + s.layerCount * 4)

-- ============================================================
-- ofLayers / normalize の rotate180 等変性
-- ============================================================

/-- Shape.ofLayers と map Layer.rotate180 の可換性 -/
private theorem ofLayers_rotate180 (ls : List Layer) :
        (Shape.ofLayers ls).map Shape.rotate180 =
        Shape.ofLayers (ls.map Layer.rotate180) := by
    cases ls with
    | nil => rfl
    | cons l rest =>
        simp only [Shape.ofLayers, Option.map]
        congr 1

/-- Option Shape の normalize と rotate180 の可換性 -/
private theorem option_bind_normalize_rotate180 (os : Option Shape) :
        (os.bind Shape.normalize).map Shape.rotate180 =
        (os.map Shape.rotate180).bind Shape.normalize := by
    cases os with
    | none => rfl
    | some s =>
        simp only [Option.bind, Option.map]
        exact s.normalize_map_layers Layer.rotate180 Layer.isEmpty_rotate180

-- ============================================================
-- FallingUnit の rotate180 変換
-- ============================================================

/-- FallingUnit を rotate180 する -/
private def FallingUnit.rotate180 : FallingUnit → FallingUnit
    | .cluster ps => .cluster (ps.map QuarterPos.rotate180)
    | .pin p => .pin p.rotate180

/-- FallingUnit.positions は rotate180 で等変 -/
private theorem FallingUnit.positions_rotate180 (u : FallingUnit) :
        u.rotate180.positions = u.positions.map QuarterPos.rotate180 := by
    cases u with
    | cluster ps => rfl
    | pin p => rfl

/-- QuarterPos.rotate180 は layer を保持 -/
private theorem QuarterPos.rotate180_layer (p : QuarterPos) :
        p.rotate180.layer = p.layer := rfl

/-- QuarterPos.rotate180 の dir フィールド -/
private theorem QuarterPos.rotate180_dir (p : QuarterPos) :
        p.rotate180.dir = p.dir.rotate180 := rfl

/-- map が foldl の関数を保存する場合、foldl (map g l) = foldl l -/
private theorem foldl_map_layer (l : List QuarterPos) (init : Nat) :
        (l.map QuarterPos.rotate180).foldl (fun a q => min a q.layer) init =
        l.foldl (fun a q => min a q.layer) init := by
    induction l generalizing init with
    | nil => rfl
    | cons p ps ih => exact ih _

/-- FallingUnit.minLayer は rotate180 で不変 -/
private theorem FallingUnit.minLayer_rotate180 (u : FallingUnit) :
        u.rotate180.minLayer = u.minLayer := by
    simp only [FallingUnit.minLayer, FallingUnit.positions_rotate180]
    cases u.positions with
    | nil => rfl
    | cons p rest => exact foldl_map_layer rest p.layer

/-- positions の map rotate180 した filterMap は元の filterMap と同じ (layer 列) -/
private theorem filterMap_rotate180_layer (ps : List QuarterPos) (d : Direction) :
        (ps.map QuarterPos.rotate180).filterMap (fun p =>
            if p.dir == d.rotate180 then some p.layer else none) =
        ps.filterMap (fun p => if p.dir == d then some p.layer else none) := by
    rw [List.filterMap_map]
    congr 1
    funext p
    simp only [Function.comp, QuarterPos.rotate180, dir_beq_rotate180']

/-- FallingUnit.minLayerAtDir は rotate180 で等変 -/
private theorem FallingUnit.minLayerAtDir_rotate180 (u : FallingUnit) (d : Direction) :
        u.rotate180.minLayerAtDir (d.rotate180) = u.minLayerAtDir d := by
    unfold FallingUnit.minLayerAtDir
    rw [FallingUnit.positions_rotate180, filterMap_rotate180_layer]

-- ============================================================
-- shouldProcessBefore / sortFallingUnits の rotate180 等変性
-- ============================================================

/-- minLayerAtDir は rotate180 適用後に方角も rotate180 で戻る -/
private theorem FallingUnit.minLayerAtDir_rotate180' (u : FallingUnit) (d : Direction) :
        u.rotate180.minLayerAtDir d = u.minLayerAtDir d.rotate180 := by
    cases d with
    | ne => exact FallingUnit.minLayerAtDir_rotate180 u .sw
    | se => exact FallingUnit.minLayerAtDir_rotate180 u .nw
    | sw => exact FallingUnit.minLayerAtDir_rotate180 u .ne
    | nw => exact FallingUnit.minLayerAtDir_rotate180 u .se

/-- Direction.all.any は rotate180 置換で不変 -/
private theorem Direction.any_rotate180 (f : Direction → Bool) :
        Direction.all.any (f ∘ Direction.rotate180) = Direction.all.any f := by
    simp only [Direction.all, List.any_cons, List.any_nil, Function.comp, Direction.rotate180,
        Bool.or_false]
    cases f Direction.ne <;> cases f Direction.se <;> cases f Direction.sw <;> cases f Direction.nw <;> rfl

/-- shouldProcessBefore は rotate180 で不変 -/
private theorem shouldProcessBefore_rotate180 (a b : FallingUnit) :
        shouldProcessBefore a.rotate180 b.rotate180 =
        shouldProcessBefore a b := by
    unfold shouldProcessBefore
    simp only [Direction.all, List.any_cons, List.any_nil, Bool.or_false]
    -- LHS: 各 a.rotate180.minLayerAtDir X を書き換え
    -- ne のケース
    rw [FallingUnit.minLayerAtDir_rotate180' a Direction.ne,
        FallingUnit.minLayerAtDir_rotate180' b Direction.ne,
        FallingUnit.minLayerAtDir_rotate180' a Direction.se,
        FallingUnit.minLayerAtDir_rotate180' b Direction.se,
        FallingUnit.minLayerAtDir_rotate180' a Direction.sw,
        FallingUnit.minLayerAtDir_rotate180' b Direction.sw,
        FallingUnit.minLayerAtDir_rotate180' a Direction.nw,
        FallingUnit.minLayerAtDir_rotate180' b Direction.nw]
    -- rotate180: ne→sw, se→nw, sw→ne, nw→se を解消
    simp only [Direction.rotate180]
    -- Bool.or の並替え: sw||(nw||(ne||se)) = ne||(se||(sw||nw))
    generalize (match a.minLayerAtDir Direction.sw, b.minLayerAtDir Direction.sw with
        | some la, some lb => decide (la < lb) | x, x_1 => false) = p1
    generalize (match a.minLayerAtDir Direction.nw, b.minLayerAtDir Direction.nw with
        | some la, some lb => decide (la < lb) | x, x_1 => false) = p2
    generalize (match a.minLayerAtDir Direction.ne, b.minLayerAtDir Direction.ne with
        | some la, some lb => decide (la < lb) | x, x_1 => false) = p3
    generalize (match a.minLayerAtDir Direction.se, b.minLayerAtDir Direction.se with
        | some la, some lb => decide (la < lb) | x, x_1 => false) = p4
    cases p1 <;> cases p2 <;> cases p3 <;> cases p4 <;> rfl

/-- tiebreaker は rotate180 で不変 -/
private theorem tiebreaker_rotate180 (u : FallingUnit) :
        u.rotate180.tiebreaker = u.tiebreaker := by
    simp only [FallingUnit.tiebreaker, Direction.all, List.foldl]
    rw [FallingUnit.minLayerAtDir_rotate180' u Direction.ne,
        FallingUnit.minLayerAtDir_rotate180' u Direction.se,
        FallingUnit.minLayerAtDir_rotate180' u Direction.sw,
        FallingUnit.minLayerAtDir_rotate180' u Direction.nw]
    simp only [Direction.rotate180]
    -- 目標: ne→sw, se→nw, sw→ne, nw→se の結果の和が元の和と等しい
    -- 4項の加算なので可換律で閉じる
    omega

/-- insertSorted は rotate180 で等変 -/
private theorem insertSorted_rotate180 (u : FallingUnit) (sorted : List FallingUnit) (fuel : Nat) :
        (insertSorted u sorted fuel).map FallingUnit.rotate180 =
        insertSorted u.rotate180 (sorted.map FallingUnit.rotate180) fuel := by
    induction fuel generalizing sorted with
    | zero => simp [insertSorted]
    | succ n ih =>
        cases sorted with
        | nil => simp [insertSorted, List.map]
        | cons v rest =>
            -- rotate180 後の条件は元の条件と一致
            have hspb1 : shouldProcessBefore u.rotate180 v.rotate180 =
                    shouldProcessBefore u v := shouldProcessBefore_rotate180 u v
            have hspb2 : shouldProcessBefore v.rotate180 u.rotate180 =
                    shouldProcessBefore v u := shouldProcessBefore_rotate180 v u
            have htie : u.rotate180.tiebreaker ≤ v.rotate180.tiebreaker ↔
                    u.tiebreaker ≤ v.tiebreaker := by
                rw [tiebreaker_rotate180, tiebreaker_rotate180]
            -- map を展開して RHS の insertSorted の引数を正規化
            -- 目標:
            --   (insertSorted u (v :: rest) (n+1)).map r180
            --   = insertSorted u.r180 ((v :: rest).map r180) (n+1)
            -- (v :: rest).map r180 = v.r180 :: rest.map r180
            show (insertSorted u (v :: rest) (n + 1)).map FallingUnit.rotate180 =
                insertSorted u.rotate180 (v.rotate180 :: rest.map FallingUnit.rotate180) (n + 1)
            -- 4分岐を by_cases で場合分け
            by_cases h1 : shouldProcessBefore u v
            · -- spb u v = true (h1 : shouldProcessBefore u v = true)
              have lhs : insertSorted u (v :: rest) (n + 1) = u :: v :: rest := by
                  show (if shouldProcessBefore u v then u :: v :: rest
                      else if shouldProcessBefore v u then v :: insertSorted u rest n
                      else if u.tiebreaker ≤ v.tiebreaker then u :: v :: rest
                      else v :: insertSorted u rest n) = _
                  simp [h1]
              have rhs : insertSorted u.rotate180 (v.rotate180 :: rest.map FallingUnit.rotate180) (n + 1) =
                  u.rotate180 :: v.rotate180 :: rest.map FallingUnit.rotate180 := by
                  show (if shouldProcessBefore u.rotate180 v.rotate180 then _
                      else _) = _
                  simp [hspb1, h1]
              rw [lhs, rhs]; simp [List.map]
            · -- spb u v = false
              simp only [Bool.not_eq_true] at h1
              have h1' : shouldProcessBefore u.rotate180 v.rotate180 = false := by
                  rw [hspb1]; exact h1
              by_cases h2 : shouldProcessBefore v u
              · -- spb v u = true
                have lhs : insertSorted u (v :: rest) (n + 1) =
                    v :: insertSorted u rest n := by
                    show (if shouldProcessBefore u v then u :: v :: rest
                        else if shouldProcessBefore v u then v :: insertSorted u rest n
                        else if u.tiebreaker ≤ v.tiebreaker then u :: v :: rest
                        else v :: insertSorted u rest n) = _
                    simp [h1, h2]
                have rhs : insertSorted u.rotate180 (v.rotate180 :: rest.map FallingUnit.rotate180) (n + 1) =
                    v.rotate180 :: insertSorted u.rotate180 (rest.map FallingUnit.rotate180) n := by
                    show (if shouldProcessBefore u.rotate180 v.rotate180 then _
                        else if shouldProcessBefore v.rotate180 u.rotate180 then _
                        else _) = _
                    simp [h1', hspb2, h2]
                rw [lhs, rhs]; simp only [List.map]
                exact congrArg _ (ih rest)
              · -- tied
                simp only [Bool.not_eq_true] at h2
                have h2' : shouldProcessBefore v.rotate180 u.rotate180 = false := by
                    rw [hspb2]; exact h2
                by_cases h3 : u.tiebreaker ≤ v.tiebreaker
                · -- tiebreaker u ≤ tiebreaker v
                  have lhs : insertSorted u (v :: rest) (n + 1) =
                      u :: v :: rest := by
                      show (if shouldProcessBefore u v then u :: v :: rest
                          else if shouldProcessBefore v u then v :: insertSorted u rest n
                          else if u.tiebreaker ≤ v.tiebreaker then u :: v :: rest
                          else v :: insertSorted u rest n) = _
                      simp [h1, h2, h3]
                  have rhs : insertSorted u.rotate180 (v.rotate180 :: rest.map FallingUnit.rotate180) (n + 1) =
                      u.rotate180 :: v.rotate180 :: rest.map FallingUnit.rotate180 := by
                      show (if shouldProcessBefore u.rotate180 v.rotate180 then _
                          else if shouldProcessBefore v.rotate180 u.rotate180 then _
                          else if u.rotate180.tiebreaker ≤ v.rotate180.tiebreaker then _
                          else _) = _
                      simp [h1', h2', htie.mpr h3]
                  rw [lhs, rhs]; simp [List.map]
                · -- tiebreaker u > tiebreaker v
                  have lhs : insertSorted u (v :: rest) (n + 1) =
                      v :: insertSorted u rest n := by
                      show (if shouldProcessBefore u v then u :: v :: rest
                          else if shouldProcessBefore v u then v :: insertSorted u rest n
                          else if u.tiebreaker ≤ v.tiebreaker then u :: v :: rest
                          else v :: insertSorted u rest n) = _
                      simp [h1, h2, h3]
                  have rhs : insertSorted u.rotate180 (v.rotate180 :: rest.map FallingUnit.rotate180) (n + 1) =
                      v.rotate180 :: insertSorted u.rotate180 (rest.map FallingUnit.rotate180) n := by
                      show (if shouldProcessBefore u.rotate180 v.rotate180 then _
                          else if shouldProcessBefore v.rotate180 u.rotate180 then _
                          else if u.rotate180.tiebreaker ≤ v.rotate180.tiebreaker then _
                          else _) = _
                      simp [h1', h2', show ¬(u.rotate180.tiebreaker ≤ v.rotate180.tiebreaker) from fun h => h3 (htie.mp h)]
                  rw [lhs, rhs]; simp only [List.map]
                  exact congrArg _ (ih rest)

/-- sortFallingUnits は rotate180 で等変 -/
private theorem sortFallingUnits_rotate180 (units : List FallingUnit) :
        (sortFallingUnits units).map FallingUnit.rotate180 =
        sortFallingUnits (units.map FallingUnit.rotate180) := by
    simp only [sortFallingUnits]
    -- foldl と map rotate180 の交換を一般化帰納法で証明
    suffices h : ∀ (acc : List FallingUnit),
        (units.foldl (fun sorted u => insertSorted u sorted (sorted.length + 1)) acc).map FallingUnit.rotate180 =
        (units.map FallingUnit.rotate180).foldl (fun sorted u => insertSorted u sorted (sorted.length + 1)) (acc.map FallingUnit.rotate180) from h []
    induction units with
    | nil => intro acc; rfl
    | cons u rest ih =>
        intro acc
        simp only [List.map, List.foldl]
        rw [ih (insertSorted u acc (acc.length + 1))]
        congr 1
        rw [insertSorted_rotate180]
        congr 1
        simp [List.length_map]

-- ============================================================
-- sortFallingUnits の置換性（Perm）
-- ============================================================

/-- insertSorted の結果は入力の置換である -/
private theorem insertSorted_perm (u : FallingUnit) (sorted : List FallingUnit) (fuel : Nat) :
        (insertSorted u sorted fuel).Perm (u :: sorted) := by
    induction fuel generalizing sorted with
    | zero =>
        -- insertSorted u sorted 0 = u :: sorted (定義的等式)
        unfold insertSorted
        exact List.Perm.refl _
    | succ n ih =>
        cases sorted with
        | nil => exact List.Perm.refl _
        | cons v rest =>
            simp only [insertSorted]
            split
            · -- spb u v = true: u :: v :: rest — そのまま
              exact List.Perm.refl _
            · -- spb u v = false
              split
              · -- spb v u = true: v :: insertSorted u rest fuel
                exact ((ih rest).cons v).trans (List.Perm.swap u v rest)
              · -- tied: tiebreaker で分岐
                split
                · -- u.tiebreaker ≤ v.tiebreaker: u :: v :: rest
                  exact List.Perm.refl _
                · -- else: v :: insertSorted u rest fuel
                  exact ((ih rest).cons v).trans (List.Perm.swap u v rest)

/-- sortFallingUnits の結果は入力の置換である -/
private theorem sortFallingUnits_perm (units : List FallingUnit) :
        (sortFallingUnits units).Perm units := by
    simp only [sortFallingUnits]
    -- 一般化: acc を保持しながら帰納法
    suffices h : ∀ (acc : List FallingUnit),
        (units.foldl (fun sorted u => insertSorted u sorted (sorted.length + 1)) acc).Perm
            (acc ++ units) by
      simpa using h []
    induction units with
    | nil =>
        intro acc
        simp only [List.foldl, List.append_nil]
        exact List.Perm.refl _
    | cons u rest ih =>
        intro acc
        simp only [List.foldl]
        -- insertSorted u acc ... ~ u :: acc → foldl 結果 ~ (u :: acc) ++ rest
        have h_ins := insertSorted_perm u acc (acc.length + 1)
        have h_foldl := ih (insertSorted u acc (acc.length + 1))
        -- h_foldl : foldl ... (insertSorted u acc ...) ~ (insertSorted u acc ...) ++ rest
        -- h_ins : (insertSorted u acc ...) ~ u :: acc
        -- 目標: foldl ... ~ acc ++ (u :: rest)
        exact h_foldl.trans ((h_ins.append (List.Perm.refl rest)).trans
            (by simp only [List.cons_append]; exact List.perm_middle.symm))

-- ============================================================
-- sortFallingUnits の位置集合保存性
-- ============================================================

/-- insertSorted は flatMap positions の .any メンバーシップを保存する -/
private theorem insertSorted_any_positions (u : FallingUnit) (sorted : List FallingUnit)
        (fuel : Nat) (p : QuarterPos) :
        ((insertSorted u sorted fuel).flatMap FallingUnit.positions).any (· == p) =
        ((u :: sorted).flatMap FallingUnit.positions).any (· == p) := by
    induction fuel generalizing sorted with
    | zero => simp only [insertSorted]
    | succ n ih =>
        cases sorted with
        | nil => rfl
        | cons v rest =>
            simp only [insertSorted]
            split
            · -- spb u v = true: u :: v :: rest → そのまま
              rfl
            · -- spb u v = false
              split
              · -- spb v u = true: v :: insertSorted u rest fuel
                simp only [List.flatMap_cons, List.any_append]
                rw [ih]
                simp only [List.flatMap_cons, List.any_append]
                cases u.positions.any (· == p) <;>
                    cases v.positions.any (· == p) <;>
                    simp
              · -- tied: tiebreaker で分岐
                split
                · -- u.tiebreaker ≤ v.tiebreaker: u :: v :: rest
                  rfl
                · -- else: v :: insertSorted u rest fuel
                  simp only [List.flatMap_cons, List.any_append]
                  rw [ih]
                  simp only [List.flatMap_cons, List.any_append]
                  cases u.positions.any (· == p) <;>
                      cases v.positions.any (· == p) <;>
                      simp

/-- sortFallingUnits は flatMap positions の .any メンバーシップを保存する -/
private theorem sortFallingUnits_any_positions (units : List FallingUnit) (p : QuarterPos) :
        ((sortFallingUnits units).flatMap FallingUnit.positions).any (· == p) =
        (units.flatMap FallingUnit.positions).any (· == p) := by
    simp only [sortFallingUnits]
    -- foldl と flatMap の交換を帰納法で示す
    suffices h : ∀ (acc : List FallingUnit),
        ((units.foldl (fun sorted u => insertSorted u sorted (sorted.length + 1)) acc).flatMap
            FallingUnit.positions).any (· == p) =
        ((acc ++ units).flatMap FallingUnit.positions).any (· == p) by
      have := h []
      simp only [List.nil_append] at this
      exact this
    induction units with
    | nil => intro acc; simp [List.append_nil]
    | cons u rest ih =>
        intro acc
        simp only [List.foldl]
        rw [ih]
        -- ゴール: ((acc ++ [u inserted]) ++ rest).flatMap.any = (acc ++ (u :: rest)).flatMap.any
        -- insertSorted の位置保存性を使う
        simp only [List.flatMap_append, List.any_append]
        rw [insertSorted_any_positions]
        simp only [List.flatMap_cons, List.any_append]
        -- Bool の or 結合律・交換律で閉じる
        cases (acc.flatMap FallingUnit.positions).any (· == p) <;>
            cases u.positions.any (· == p) <;>
            cases (rest.flatMap FallingUnit.positions).any (· == p) <;>
            simp

-- ============================================================
-- 汎用 BFS との対応 + メンバーシップ等変性
-- ============================================================

/-- structuralBfs は genericBfs (isStructurallyBonded s) と等しい -/
private theorem structuralBfs_eq_generic (s : Shape)
        (allPos vis queue : List QuarterPos) (fuel : Nat) :
        structuralBfs s allPos vis queue fuel =
        genericBfs (isStructurallyBonded s) allPos vis queue fuel := by
    induction fuel generalizing vis queue with
    | zero => rfl
    | succ n ih =>
        cases queue with
        | nil => rfl
        | cons pos rest =>
            simp only [structuralBfs, genericBfs]
            split <;> exact ih ..

/-- groundingBfs は genericBfs (isGroundingContact s) と等しい -/
private theorem groundingBfs_eq_generic (s : Shape)
        (allPos vis queue : List QuarterPos) (fuel : Nat) :
        groundingBfs s allPos vis queue fuel =
        genericBfs (isGroundingContact s) allPos vis queue fuel := by
    induction fuel generalizing vis queue with
    | zero => rfl
    | succ n ih =>
        cases queue with
        | nil => rfl
        | cons pos rest =>
            simp only [groundingBfs, genericBfs]
            split <;> exact ih ..

/-- allValid のメンバーシップは layer < layerCount と同値 -/
private theorem allValid_any_iff_layer' (s : Shape) (p : QuarterPos) :
        (QuarterPos.allValid s).any (· == p) = true ↔ p.layer < s.layerCount := by
    constructor
    · intro h
      rw [List.any_eq_true] at h
      obtain ⟨x, h_mem, h_eq⟩ := h; have := eq_of_beq h_eq; subst this
      simp only [QuarterPos.allValid] at h_mem
      rw [List.mem_flatMap] at h_mem
      obtain ⟨li, h_li, h_dir⟩ := h_mem
      rw [List.mem_map] at h_dir
      obtain ⟨d, _, h_mk⟩ := h_dir
      rw [← h_mk]; exact List.mem_range.mp h_li
    · intro h
      rw [List.any_eq_true]
      exact ⟨p, by
          simp only [QuarterPos.allValid, List.mem_flatMap]
          exact ⟨p.layer, List.mem_range.mpr h,
              List.mem_map.mpr ⟨p.dir, List.mem_of_elem_eq_true (by cases p.dir <;> rfl),
                  by cases p; rfl⟩⟩,
          BEq.rfl⟩

/-- allValid の長さは layerCount * 4 -/
private theorem allValid_length' (s : Shape) :
        (QuarterPos.allValid s).length = s.layerCount * 4 := by
    simp only [QuarterPos.allValid, Shape.layerCount]
    generalize s.layers.length = n
    induction n with
    | zero => simp
    | succ k ih =>
        rw [List.range_succ, List.flatMap_append, List.length_append, ih]
        simp [List.flatMap_cons, List.flatMap_nil, List.map, Direction.all]
        omega

/-- isStructurallyBonded s p q = true ならば q.layer < s.layerCount -/
private theorem isStructurallyBonded_valid (s : Shape) (p q : QuarterPos)
        (h : isStructurallyBonded s p q = true) :
        q.layer < s.layerCount := by
    simp only [isStructurallyBonded] at h
    cases hq : q.getQuarter s with
    | none => simp [hq] at h
    | some _ =>
        simp only [Shape.layerCount]
        unfold QuarterPos.getQuarter at hq
        cases hl : s.layers[q.layer]? with
        | none => simp [hl] at hq
        | some _ => exact (List.getElem?_eq_some_iff.mp hl).1

/-- isGroundingContact s p q = true ならば q.layer < s.layerCount -/
private theorem isGroundingContact_valid (s : Shape) (p q : QuarterPos)
        (h : isGroundingContact s p q = true) :
        q.layer < s.layerCount := by
    simp only [isGroundingContact] at h
    cases hq : q.getQuarter s with
    | none => simp [hq] at h
    | some _ =>
        simp only [Shape.layerCount]
        unfold QuarterPos.getQuarter at hq
        cases hl : s.layers[q.layer]? with
        | none => simp [hl] at hq
        | some _ => exact (List.getElem?_eq_some_iff.mp hl).1

/-- isGroundingContact s p q = true ならば p.layer < s.layerCount -/
private theorem isGroundingContact_valid_fst (s : Shape) (p q : QuarterPos)
        (h : isGroundingContact s p q = true) :
        p.layer < s.layerCount := by
    simp only [isGroundingContact] at h
    cases hp : p.getQuarter s with
    | none => simp [hp] at h
    | some _ =>
        simp only [Shape.layerCount]
        unfold QuarterPos.getQuarter at hp
        cases hl : s.layers[p.layer]? with
        | none => simp [hl] at hp
        | some _ => exact (List.getElem?_eq_some_iff.mp hl).1

/-- 構造結合到達可能性は rotate180 で保存される -/
private theorem structuralReachable_rotate180 (s : Shape) (p q : QuarterPos)
        (h : GenericReachable (isStructurallyBonded s) p q) :
        GenericReachable (isStructurallyBonded s.rotate180) p.rotate180 q.rotate180 := by
    induction h with
    | refl => exact .refl
    | step h_bond _ ih =>
        exact .step (isStructurallyBonded_rotate180 s _ _ ▸ h_bond) ih

/-- 接地接触到達可能性は rotate180 で保存される -/
private theorem groundingReachable_rotate180 (s : Shape) (p q : QuarterPos)
        (h : GenericReachable (isGroundingContact s) p q) :
        GenericReachable (isGroundingContact s.rotate180) p.rotate180 q.rotate180 := by
    induction h with
    | refl => exact .refl
    | step h_bond _ ih =>
        exact .step (isGroundingContact_rotate180 s _ _ ▸ h_bond) ih

/-- 構造クラスタの健全性: 結果は start から到達可能 -/
private theorem structuralClusterList_sound (s : Shape) (start p : QuarterPos) :
        (structuralClusterList s start).any (· == p) = true →
        GenericReachable (isStructurallyBonded s) start p := by
    intro h; unfold structuralClusterList at h
    rw [structuralBfs_eq_generic] at h
    match genericBfs_sound (isStructurallyBonded s) _ [] [start] _ p h with
    | .inl h_vis => simp [List.any] at h_vis
    | .inr ⟨q, h_q, h_reach⟩ =>
        rw [List.any_cons, Bool.or_eq_true_iff] at h_q
        cases h_q with
        | inl h_eq => exact eq_of_beq h_eq ▸ h_reach
        | inr h_rest => simp [List.any] at h_rest

/-- 構造的到達可能性は canFormBond を保存する -/
private theorem structuralReachable_canFormBond (s : Shape) (pos q : QuarterPos)
        (h : GenericReachable (isStructurallyBonded s) pos q)
        (h_start : ∃ v, pos.getQuarter s = some v ∧ v.canFormBond = true) :
        ∃ w, q.getQuarter s = some w ∧ w.canFormBond = true := by
    induction h with
    | refl => exact h_start
    | @step a b c h_bond _ ih =>
        apply ih; clear ih h_start
        -- isStructurallyBonded s a b = true から b の canFormBond を取得
        have h_isb := h_bond; unfold isStructurallyBonded at h_isb
        split at h_isb
        · next v1 v2 _ hv2 =>
          exact ⟨v2, hv2, by simp only [Bool.and_eq_true] at h_isb; exact h_isb.1.2⟩
        · exact absurd h_isb (by decide)

/-- 構造クラスタの完全性: start から到達可能な位置は全て結果に含まれる -/
private theorem structuralClusterList_complete (s : Shape) (start p : QuarterPos)
        (h_lc : s.layerCount > 0)
        (h_reach : GenericReachable (isStructurallyBonded s) start p) :
        (structuralClusterList s start).any (· == p) = true := by
    unfold structuralClusterList
    rw [structuralBfs_eq_generic]
    have h_inv : GenericBFSInv (isStructurallyBonded s) (QuarterPos.allValid s)
        (genericBfs (isStructurallyBonded s) (QuarterPos.allValid s) [] [start]
            (s.layerCount * 4 * (s.layerCount * 4))) [] := by
      apply genericBfs_invariant_preserved
      · exact genericBfsInv_initial _ _ _
      · have h_filter : (QuarterPos.allValid s).filter (fun p =>
            !(([] : List QuarterPos).any (· == p))) = QuarterPos.allValid s :=
            List.filter_eq_self.mpr (by intro x _; simp [List.any])
        simp only [h_filter, List.length, allValid_length']
        omega
      · intro p q h
        exact (allValid_any_iff_layer' s p).mpr (isStructurallyBonded_valid s q p
            (isStructurallyBonded_symm s p q ▸ h))
    have h_start_mem : (genericBfs (isStructurallyBonded s) (QuarterPos.allValid s) [] [start]
        (s.layerCount * 4 * (s.layerCount * 4))).any (· == start) = true :=
        genericBfs_contains_start _ _ _ _ (Nat.mul_pos (by omega) (by omega))
    exact genericBfs_closed_contains_reachable _ _ _ h_inv start p h_start_mem h_reach
        (fun q r h_bond =>
            (allValid_any_iff_layer' s r).mpr (isStructurallyBonded_valid s q r h_bond))

/-- 2つの構造クラスタが位置を共有すれば、一方のシードはもう一方に含まれる -/
private theorem structuralClusterList_shared_contains_seed (s : Shape) (pos1 pos2 p : QuarterPos)
        (h_lc : s.layerCount > 0)
        (hp1 : (structuralClusterList s pos1).any (· == p) = true)
        (hp2 : (structuralClusterList s pos2).any (· == p) = true) :
        (structuralClusterList s pos1).any (· == pos2) = true := by
    have h_r1 := structuralClusterList_sound s pos1 p hp1
    have h_r2 := structuralClusterList_sound s pos2 p hp2
    have h_r2_sym := h_r2.symm (isStructurallyBonded_symm s)
    exact structuralClusterList_complete s pos1 pos2 h_lc (h_r1.trans h_r2_sym)

/-- groundedPositionsList の健全性：BFS 結果にメンバーがあれば有効 seed から到達可能 -/
private theorem groundedPositionsList_sound (s : Shape) (p : QuarterPos)
        (h : (groundedPositionsList s).any (· == p) = true) :
        ∃ seed, seed ∈ (QuarterPos.allValid s).filter (fun q =>
            q.layer == 0 && match q.getQuarter s with
            | some q => !q.isEmpty | none => false) ∧
        GenericReachable (isGroundingContact s) seed p := by
    unfold groundedPositionsList at h
    rw [groundingBfs_eq_generic] at h
    match genericBfs_sound (isGroundingContact s) (QuarterPos.allValid s) []
            _ _ p h with
    | .inl h_vis => simp [List.any] at h_vis
    | .inr ⟨seed, h_seed, h_reach⟩ =>
        exact ⟨seed, by
            rw [List.any_eq_true] at h_seed
            obtain ⟨y, hy, hye⟩ := h_seed; exact eq_of_beq hye ▸ hy,
            h_reach⟩

/-- groundedPositionsList の完全性：有効 seed から到達可能なら BFS 結果に含まれる -/
private theorem groundedPositionsList_complete (s : Shape) (seed p : QuarterPos)
        (h_seed : seed ∈ (QuarterPos.allValid s).filter (fun q =>
            q.layer == 0 && match q.getQuarter s with
            | some q => !q.isEmpty | none => false))
        (h_reach : GenericReachable (isGroundingContact s) seed p) :
        (groundedPositionsList s).any (· == p) = true := by
    unfold groundedPositionsList; rw [groundingBfs_eq_generic]
    -- fuel 条件（invariant_preserved と queue_in_result で共有）
    have h_fuel : (s.layerCount * 4 * (s.layerCount * 4) + s.layerCount * 4) + 1 ≥
            ((QuarterPos.allValid s).filter fun p =>
                p.layer == 0 && match p.getQuarter s with
                | some q => !q.isEmpty | none => false).length +
            ((QuarterPos.allValid s).filter fun p =>
                !(([] : List QuarterPos).any (· == p))).length *
            ((QuarterPos.allValid s).filter fun p =>
                !(([] : List QuarterPos).any (· == p))).length := by
        have h_filter : (QuarterPos.allValid s).filter (fun p =>
            !(([] : List QuarterPos).any (· == p))) = QuarterPos.allValid s :=
            List.filter_eq_self.mpr (by intro x _; simp [List.any])
        simp only [h_filter, allValid_length']
        have := List.length_filter_le (fun p =>
            p.layer == 0 && match p.getQuarter s with
            | some q => !q.isEmpty | none => false) (QuarterPos.allValid s)
        rw [allValid_length' s] at this; omega
    -- BFS 不変条件保存
    have h_inv := genericBfs_invariant_preserved (isGroundingContact s)
        (QuarterPos.allValid s) []
        ((QuarterPos.allValid s).filter fun p =>
            p.layer == 0 && match p.getQuarter s with
            | some q => !q.isEmpty | none => false)
        (s.layerCount * 4 * (s.layerCount * 4) + s.layerCount * 4)
        (by intro v hv; simp [List.any] at hv)
        h_fuel
        (fun p q h =>
            (allValid_any_iff_layer' s p).mpr
                (isGroundingContact_valid_fst s p q h))
    -- seed のレイヤ有効性
    have h_seed_layer : seed.layer < s.layerCount := by
        have ⟨h_allValid, _⟩ := List.mem_filter.mp h_seed
        exact (allValid_any_iff_layer' s seed).mp
            (List.any_eq_true.mpr ⟨seed, h_allValid, BEq.rfl⟩)
    -- seed が BFS 結果に含まれる
    have h_seed_in := genericBfs_queue_in_result
        (isGroundingContact s) (QuarterPos.allValid s) []
        ((QuarterPos.allValid s).filter fun p =>
            p.layer == 0 && match p.getQuarter s with
            | some q => !q.isEmpty | none => false)
        (s.layerCount * 4 * (s.layerCount * 4) + s.layerCount * 4)
        seed
        (.inr (List.any_eq_true.mpr ⟨seed, h_seed, BEq.rfl⟩))
        ((allValid_any_iff_layer' s seed).mpr h_seed_layer)
        h_fuel
        (fun a b h =>
            (allValid_any_iff_layer' s a).mpr
                (isGroundingContact_valid_fst s a b h))
    -- 閉包で p の所属を導出
    exact genericBfs_closed_contains_reachable _ _ _ h_inv
        seed p h_seed_in h_reach
        (fun q r h_bond =>
            (allValid_any_iff_layer' s r).mpr
                (isGroundingContact_valid s q r h_bond))

/-- 接地 seed の rotate180 変換: seeds(s.r180) → seeds(s) -/
private theorem grounding_seed_rotate180 (s : Shape) (seed : QuarterPos)
        (h : seed ∈ (QuarterPos.allValid s).filter (fun q =>
            q.layer == 0 && match q.getQuarter s.rotate180 with
            | some q => !q.isEmpty | none => false)) :
        seed.rotate180 ∈ (QuarterPos.allValid s).filter (fun q =>
            q.layer == 0 && match q.getQuarter s with
            | some q => !q.isEmpty | none => false) := by
    have ⟨h_allValid, h_pred⟩ := List.mem_filter.mp h
    have h_layer : seed.layer < s.layerCount :=
        (allValid_any_iff_layer' s seed).mp
            (List.any_eq_true.mpr ⟨seed, h_allValid, BEq.rfl⟩)
    have h_r180_allValid : seed.rotate180 ∈ QuarterPos.allValid s := by
        have h_any := (allValid_any_iff_layer' s seed.rotate180).mpr h_layer
        rw [List.any_eq_true] at h_any
        obtain ⟨y, hy, hye⟩ := h_any; exact eq_of_beq hye ▸ hy
    exact List.mem_filter.mpr ⟨h_r180_allValid, by
        simp only [← getQuarter_rotate180_inv]; exact h_pred⟩

/-- 接地 seed の rotate180 正変換: seeds(s) → seeds(s.r180) -/
private theorem grounding_seed_to_rotate180 (s : Shape) (seed : QuarterPos)
        (h : seed ∈ (QuarterPos.allValid s).filter (fun q =>
            q.layer == 0 && match q.getQuarter s with
            | some q => !q.isEmpty | none => false)) :
        seed.rotate180 ∈ (QuarterPos.allValid s).filter (fun q =>
            q.layer == 0 && match q.getQuarter s.rotate180 with
            | some q => !q.isEmpty | none => false) := by
    have ⟨h_allValid, h_pred⟩ := List.mem_filter.mp h
    have h_layer : seed.layer < s.layerCount :=
        (allValid_any_iff_layer' s seed).mp
            (List.any_eq_true.mpr ⟨seed, h_allValid, BEq.rfl⟩)
    have h_r180_allValid : seed.rotate180 ∈ QuarterPos.allValid s := by
        have h_any := (allValid_any_iff_layer' s seed.rotate180).mpr h_layer
        rw [List.any_eq_true] at h_any
        obtain ⟨y, hy, hye⟩ := h_any; exact eq_of_beq hye ▸ hy
    exact List.mem_filter.mpr ⟨h_r180_allValid, by
        simp only [getQuarter_rotate180]; exact h_pred⟩

/-- .any (· == p) と List.mem の等価性（LawfulBEq 前提） -/
private theorem any_beq_iff_mem (l : List QuarterPos) (p : QuarterPos) :
        l.any (· == p) = true ↔ p ∈ l := by
    constructor
    · intro h
      rw [List.any_eq_true] at h
      obtain ⟨x, hx, he⟩ := h
      exact eq_of_beq he ▸ hx
    · intro h
      exact List.any_eq_true.mpr ⟨p, h, BEq.rfl⟩

/-- p ∉ groundedPositions s ↔ (groundedPositionsList s).any (· == p) = false -/
private theorem not_mem_groundedPositions_iff (s : Shape) (p : QuarterPos) :
        p ∉ groundedPositions s ↔ (groundedPositionsList s).any (· == p) = false := by
    constructor
    · intro h
      cases hb : (groundedPositionsList s).any (· == p) with
      | false => rfl
      | true =>
          have : p ∈ groundedPositions s := by
              unfold groundedPositions; rw [List.mem_toFinset]
              exact (any_beq_iff_mem _ _).mp hb
          exact absurd this h
    · intro h hp
      have : (groundedPositionsList s).any (· == p) = true := by
          unfold groundedPositions at hp; rw [List.mem_toFinset] at hp
          exact (any_beq_iff_mem _ _).mpr hp
      rw [h] at this; exact absurd this (by decide)

/-- decide (p ∉ groundedPositions s) は !((groundedPositionsList s).any (· == p)) と等値 -/
private theorem decide_not_mem_groundedPositions (s : Shape) (p : QuarterPos) :
        decide (p ∉ groundedPositions s) = !((groundedPositionsList s).any (· == p)) := by
    cases h : (groundedPositionsList s).any (· == p) with
    | false =>
        simp only [Bool.not_false]
        exact decide_eq_true ((not_mem_groundedPositions_iff s p).mpr h)
    | true =>
        simp only [Bool.not_true]
        have : p ∈ groundedPositions s := by
            unfold groundedPositions; rw [List.mem_toFinset]
            exact (any_beq_iff_mem _ _).mp h
        exact decide_eq_false (not_not_intro this)

/-- structuralCluster の rotate180 等変性（Finset.image 形式）。
    rotate180 してから構造クラスタ算出 = 構造クラスタ算出してから Finset.image。
    BFS の健全性・完全性・到達可能性の等変性から直接導出。 -/
theorem structuralCluster_rotate180 (s : Shape) (start : QuarterPos) :
        structuralCluster s.rotate180 start.rotate180 =
        (structuralCluster s start).image QuarterPos.rotate180 := by
    ext p
    simp only [structuralCluster, Finset.mem_image, List.mem_toFinset]
    constructor
    · intro hp
      -- BFS 健全性: p は start.r180 から到達可能
      have h_reach := structuralClusterList_sound s.rotate180 start.rotate180 p
          ((any_beq_iff_mem _ _).mpr hp)
      -- 等変性の逆方向: s での到達可能性に変換
      have h_back : GenericReachable (isStructurallyBonded s) start p.rotate180 := by
          have := structuralReachable_rotate180 s.rotate180 start.rotate180 p h_reach
          simp only [Shape.rotate180_rotate180, QuarterPos.rotate180_rotate180] at this
          exact this
      refine ⟨p.rotate180, ?_, by simp⟩
      -- BFS 完全性: 到達可能なら結果に含まれる
      cases h_lc : s.layerCount with
      | zero =>
          -- layerCount = 0 なら BFS 結果は空 → hp に矛盾
          exfalso
          unfold structuralClusterList at hp
          rw [structuralBfs_eq_generic, CrystalBond.allValid_rotate180_eq,
              Shape.layerCount_rotate180] at hp
          simp [h_lc, genericBfs] at hp
      | succ n =>
          exact (any_beq_iff_mem _ _).mp
              (structuralClusterList_complete s start p.rotate180 (by omega) h_back)
    · rintro ⟨q, hq, rfl⟩
      -- BFS 健全性 + 等変性: q.r180 は start.r180 から s.r180 で到達可能
      have h_reach := structuralClusterList_sound s start q
          ((any_beq_iff_mem _ _).mpr hq)
      have h_r180 := structuralReachable_rotate180 s start q h_reach
      -- BFS 完全性
      cases h_lc : s.layerCount with
      | zero =>
          exfalso
          unfold structuralClusterList at hq
          rw [structuralBfs_eq_generic] at hq; simp [h_lc, genericBfs] at hq
      | succ n =>
          exact (any_beq_iff_mem _ _).mp
              (structuralClusterList_complete s.rotate180 start.rotate180 q.rotate180
                  (by rw [Shape.layerCount_rotate180]; omega) h_r180)

/-- groundedPositions の rotate180 等変性（Finset.image 形式）。
    rotate180 してから接地位置算出 = 接地位置算出してから Finset.image。
    BFS の健全性・完全性・到達可能性の等変性から直接導出。 -/
theorem groundedPositions_rotate180 (s : Shape) :
        groundedPositions s.rotate180 =
        (groundedPositions s).image QuarterPos.rotate180 := by
    ext p
    simp only [groundedPositions, Finset.mem_image, List.mem_toFinset]
    constructor
    · intro hp
      -- BFS 健全性: seed' から p への到達可能性（s.r180 上）
      have h_any := (any_beq_iff_mem _ _).mpr hp
      obtain ⟨seed', h_seed', h_reach'⟩ := groundedPositionsList_sound s.rotate180 p h_any
      -- 等変性の逆方向: s での seed'.r180 → p.r180 の到達可能性
      have h_reach_back : GenericReachable (isGroundingContact s)
              seed'.rotate180 p.rotate180 := by
          have := groundingReachable_rotate180 s.rotate180 seed' p h_reach'
          simp only [Shape.rotate180_rotate180] at this
          exact this
      -- seed'.r180 は s の有効 seed（allValid_rotate180_eq で allValid を統一）
      have h_seed_valid := grounding_seed_rotate180 s seed'
          (CrystalBond.allValid_rotate180_eq s ▸ h_seed')
      refine ⟨p.rotate180, ?_, by simp⟩
      exact (any_beq_iff_mem _ _).mp
          (groundedPositionsList_complete s seed'.rotate180 p.rotate180
              h_seed_valid h_reach_back)
    · rintro ⟨q, hq, rfl⟩
      -- BFS 健全性: seed から q への到達可能性（s 上）
      have h_any := (any_beq_iff_mem _ _).mpr hq
      obtain ⟨seed, h_seed, h_reach⟩ := groundedPositionsList_sound s q h_any
      -- 等変性: s.r180 での seed.r180 → q.r180 の到達可能性
      have h_reach_r180 := groundingReachable_rotate180 s seed q h_reach
      -- seed.r180 は s.r180 の有効 seed（allValid_rotate180_eq で allValid を統一）
      have h_seed_r180 := grounding_seed_to_rotate180 s seed h_seed
      rw [← CrystalBond.allValid_rotate180_eq] at h_seed_r180
      exact (any_beq_iff_mem _ _).mp
          (groundedPositionsList_complete s.rotate180 seed.rotate180 q.rotate180
              h_seed_r180 h_reach_r180)

-- ============================================================
-- Finset ベースのメンバーシップ等変性補題
-- structuralCluster_rotate180 / groundedPositions_rotate180 から導出
-- ============================================================

/-- structuralCluster のメンバーシップは rotate180 で保存される -/
private theorem mem_structuralCluster_rotate180 (s : Shape) (start p : QuarterPos) :
        p ∈ structuralCluster s start ↔
        p.rotate180 ∈ structuralCluster s.rotate180 start.rotate180 := by
    rw [structuralCluster_rotate180, Finset.mem_image]
    constructor
    · exact fun h => ⟨p, h, rfl⟩
    · rintro ⟨q, hq, hqe⟩
      have := congr_arg QuarterPos.rotate180 hqe
      simp only [QuarterPos.rotate180_rotate180] at this
      exact this ▸ hq

/-- groundedPositions のメンバーシップは rotate180 で保存される -/
private theorem mem_groundedPositions_rotate180 (s : Shape) (p : QuarterPos) :
        p ∈ groundedPositions s ↔
        p.rotate180 ∈ groundedPositions s.rotate180 := by
    rw [groundedPositions_rotate180, Finset.mem_image]
    constructor
    · exact fun h => ⟨p, h, rfl⟩
    · rintro ⟨q, hq, hqe⟩
      have := congr_arg QuarterPos.rotate180 hqe
      simp only [QuarterPos.rotate180_rotate180] at this
      exact this ▸ hq

-- ============================================================
-- floatingUnits_isEmpty_rotate180 のヘルパー補題群
-- ============================================================

/-- 接地接触は対称的である -/
private theorem isGroundingContact_symm (s : Shape) (p1 p2 : QuarterPos) :
        isGroundingContact s p1 p2 = isGroundingContact s p2 p1 := by
    unfold isGroundingContact
    generalize p1.getQuarter s = q1
    generalize p2.getQuarter s = q2
    cases q1 with
    | none => cases q2 <;> rfl
    | some v1 => cases q2 with
        | none => rfl
        | some v2 =>
            dsimp only []
            rw [Bool.and_comm (x := !v1.isEmpty) (y := !v2.isEmpty)]
            congr 1
            have h_match_symm : (match v1, v2 with
                    | .pin, _ | _, .pin => false
                    | _, _ => true : Bool) =
                (match v2, v1 with
                    | .pin, _ | _, .pin => false
                    | _, _ => true : Bool) := by
                cases v1 <;> cases v2 <;> rfl
            rw [BEq.comm (a := p1.layer),
                LayerIndex.verticallyAdjacent_symm p1.layer p2.layer,
                BEq.comm (a := p1.dir),
                Direction.adjacent_symm p1.dir p2.dir, h_match_symm]

/-- GenericReachable の推移律 -/
private theorem GenericReachable_trans {edge : α → α → Bool}
        (h1 : GenericReachable edge a b) (h2 : GenericReachable edge b c) :
        GenericReachable edge a c := by
    induction h1 with
    | refl => exact h2
    | step h_bond _ ih => exact .step h_bond (ih h2)

/-- 対称エッジでの GenericReachable 逆転 -/
private theorem GenericReachable_reverse {edge : α → α → Bool}
        (h_symm : ∀ x y, edge x y = edge y x)
        (h : GenericReachable edge a b) :
        GenericReachable edge b a := by
    induction h with
    | refl => exact .refl
    | step h_bond _ ih =>
        exact GenericReachable_trans ih (.step (h_symm _ _ ▸ h_bond) .refl)

/-- 構造結合は接地接触に含まれる -/
private theorem isStructurallyBonded_implies_isGroundingContact (s : Shape) (p1 p2 : QuarterPos)
        (h : isStructurallyBonded s p1 p2 = true) :
        isGroundingContact s p1 p2 = true := by
    simp only [isStructurallyBonded] at h
    simp only [isGroundingContact]
    cases hq1 : p1.getQuarter s with
    | none => simp_all
    | some v1 => cases hq2 : p2.getQuarter s with
        | none => simp_all
        | some v2 =>
            simp only [hq1, hq2] at h ⊢
            revert h
            cases v1 <;> cases v2 <;>
                simp [Quarter.canFormBond, Quarter.isEmpty] <;>
                (intro h;
                 cases h1 : (p1.layer == p2.layer) <;>
                 cases h2 : (p1.dir == p2.dir) <;>
                 cases h3 : (p1.dir.adjacent p2.dir) <;>
                 cases h4 : (LayerIndex.verticallyAdjacent p1.layer p2.layer) <;>
                 simp_all (config := { decide := true }))

/-- エッジ述語の包含による GenericReachable の単調性 -/
private theorem GenericReachable_mono {edge1 edge2 : α → α → Bool}
        (h_sub : ∀ a b, edge1 a b = true → edge2 a b = true)
        (h : GenericReachable edge1 a b) :
        GenericReachable edge2 a b := by
    induction h with
    | refl => exact .refl
    | step h_bond _ ih => exact .step (h_sub _ _ h_bond) ih

/-- groundedPositionsList の BFS 不変条件 -/
private theorem groundedPositionsList_inv (s : Shape) :
        GenericBFSInv (isGroundingContact s) (QuarterPos.allValid s)
            (groundedPositionsList s) [] := by
    unfold groundedPositionsList
    rw [groundingBfs_eq_generic]
    apply genericBfs_invariant_preserved
    · intro v hv; simp [List.any] at hv
    · have h_filter : (QuarterPos.allValid s).filter (fun p =>
          !(([] : List QuarterPos).any (· == p))) = QuarterPos.allValid s :=
          List.filter_eq_self.mpr (by intro x _; simp [List.any])
      simp only [h_filter, allValid_length']
      have := List.length_filter_le (fun p =>
          p.layer == 0 && match p.getQuarter s with
          | some q => !q.isEmpty | none => false) (QuarterPos.allValid s)
      rw [allValid_length' s] at this; omega
    · intro p q h
      exact (allValid_any_iff_layer' s p).mpr
          (isGroundingContact_valid_fst s p q h)

/-- allStructuralClustersList は全ての bondable 位置をカバーする -/
private theorem allStructuralClustersList_covers (s : Shape) (p : QuarterPos)
        (h_valid : p.layer < s.layerCount)
        (h_bondable : match p.getQuarter s with | some q => q.canFormBond = true | none => False) :
        (allStructuralClustersList s).any (fun c => c.any (· == p)) = true := by
    unfold allStructuralClustersList
    -- p が bondable リストに含まれることを示す
    have h_p_mem : p ∈ (QuarterPos.allValid s).filter (fun pos =>
            match pos.getQuarter s with | some q => q.canFormBond | none => false) := by
        rw [List.mem_filter]
        exact ⟨by
            have h_any := (allValid_any_iff_layer' s p).mpr h_valid
            rw [List.any_eq_true] at h_any
            obtain ⟨x, hx, hxe⟩ := h_any; exact eq_of_beq hxe ▸ hx,
          by revert h_bondable; cases p.getQuarter s with
             | none => intro h; exact h.elim
             | some q => intro h; exact h⟩
    -- foldl 不変条件: p ∈ remaining ∨ acc がカバー → 結果がカバー
    suffices h_inv : ∀ (remaining : List QuarterPos) (acc : List (List QuarterPos)),
        (p ∈ remaining ∨ acc.any (fun c => c.any (· == p)) = true) →
        (remaining.foldl (fun clusters pos =>
            if clusters.any (fun cluster => cluster.any (· == pos)) then clusters
            else clusters ++ [structuralClusterList s pos]) acc).any
            (fun c => c.any (· == p)) = true by
      exact h_inv _ [] (.inl h_p_mem)
    intro remaining acc h_or
    induction remaining generalizing acc with
    | nil => exact h_or.elim (fun h => by cases h) id
    | cons pos rest ih =>
        dsimp only [List.foldl]
        cases h_cov : acc.any (fun cluster => cluster.any (· == pos)) with
        | true =>
            simp only [ite_true]
            exact ih acc (h_or.elim (fun h_mem => by
                cases h_mem with
                | head => exact .inr h_cov
                | tail _ h => exact .inl h) .inr)
        | false =>
            exact ih (acc ++ [structuralClusterList s pos]) (h_or.elim (fun h_mem => by
                cases h_mem with
                | head =>
                    right; rw [List.any_append]
                    simp only [Bool.or_eq_true]
                    right; simp only [List.any_cons, List.any_nil, Bool.or_false]
                    unfold structuralClusterList; rw [structuralBfs_eq_generic]
                    cases hn : s.layerCount with
                    | zero => omega
                    | succ k => exact genericBfs_contains_start _ _ _ _ (Nat.mul_pos (by omega) (by omega))
                | tail _ h => exact .inl h) (fun h => .inr (by
                    rw [List.any_append]; simp only [Bool.or_eq_true]; exact .inl h)))

/-- allStructuralClustersList の各クラスタは structuralClusterList s pos として生成される -/
private theorem allStructuralClustersList_is_structuralClusterList (s : Shape) (c : List QuarterPos)
        (hc : c ∈ allStructuralClustersList s) :
        ∃ pos, c = structuralClusterList s pos ∧ pos.layer < s.layerCount ∧
            (∃ q, pos.getQuarter s = some q ∧ q.canFormBond = true) := by
    unfold allStructuralClustersList at hc
    -- foldl 不変条件: acc の全クラスタが structuralClusterList pos の形
    suffices ∀ (remaining : List QuarterPos) (acc : List (List QuarterPos)),
        (∀ c' ∈ acc, ∃ pos, c' = structuralClusterList s pos ∧ pos.layer < s.layerCount ∧
            (∃ q, pos.getQuarter s = some q ∧ q.canFormBond = true)) →
        (∀ pos ∈ remaining, pos.layer < s.layerCount ∧
            (∃ q, pos.getQuarter s = some q ∧ q.canFormBond = true)) →
        c ∈ remaining.foldl (fun clusters pos =>
            if clusters.any (fun cluster => cluster.any (· == pos)) then clusters
            else clusters ++ [structuralClusterList s pos]) acc →
        ∃ pos, c = structuralClusterList s pos ∧ pos.layer < s.layerCount ∧
            (∃ q, pos.getQuarter s = some q ∧ q.canFormBond = true) by
      exact this _ [] (fun _ h => nomatch h) (fun pos h_mem => by
          rw [List.mem_filter] at h_mem
          obtain ⟨h_allValid, h_bond⟩ := h_mem
          refine ⟨(allValid_any_iff_layer' s pos).mp
              (List.any_eq_true.mpr ⟨pos, h_allValid, BEq.rfl⟩), ?_⟩
          cases hq : pos.getQuarter s with
          | none => simp [hq] at h_bond
          | some q =>
              cases q with
              | empty => simp [hq, Quarter.canFormBond] at h_bond
              | pin => simp [hq, Quarter.canFormBond] at h_bond
              | crystal c => exact ⟨.crystal c, rfl, rfl⟩
              | colored r c => exact ⟨.colored r c, rfl, rfl⟩) hc
    intro remaining acc h_inv h_props hc
    induction remaining generalizing acc with
    | nil => exact h_inv c hc
    | cons pos rest ih =>
        dsimp only [List.foldl] at hc
        have h_pos_props := h_props pos (.head _)
        have h_rest_props := fun p hp => h_props p (.tail _ hp)
        cases h_cov : acc.any (fun cluster => cluster.any (· == pos))
        · -- false: pos は新規 → structuralClusterList s pos を追加
          simp only [h_cov] at hc
          exact ih (acc ++ [structuralClusterList s pos])
              (fun c' hc' => by
                  rw [List.mem_append, List.mem_singleton] at hc'
                  cases hc' with
                  | inl h => exact h_inv c' h
                  | inr h => exact ⟨pos, h, h_pos_props⟩) h_rest_props hc
        · -- true: pos は既存 → スキップ
          simp only [h_cov, ite_true] at hc
          exact ih acc h_inv h_rest_props hc

-- ============================================================
-- allStructuralClustersList の位置素性（クラスタ間素性）
-- ============================================================

/-- allStructuralClustersList foldl 不変条件:
    異なるインデックスのクラスタは位置を共有しない -/
private theorem allStructuralClustersList_disjoint (s : Shape)
        (i j : Nat) (hi : i < (allStructuralClustersList s).length)
        (hj : j < (allStructuralClustersList s).length) (h_ne : i ≠ j)
        (p : QuarterPos)
        (hp1 : ((allStructuralClustersList s)[i]).any (· == p) = true) :
        ((allStructuralClustersList s)[j]).any (· == p) = false := by
    unfold allStructuralClustersList at hi hj hp1 ⊢
    -- foldl 不変条件:
    -- INV1: 各クラスタは structuralClusterList s pos の形（pos.layer < s.layerCount）
    -- INV2: 位置を共有するインデックスは同一
    suffices ∀ (remaining : List QuarterPos) (acc : List (List QuarterPos)),
        (∀ (k : Nat) (hk : k < acc.length), ∃ pos,
            acc[k] = structuralClusterList s pos ∧ pos.layer < s.layerCount) →
        (∀ (a b : Nat) (ha : a < acc.length) (hb : b < acc.length),
            a ≠ b → ∀ q, acc[a].any (· == q) = true → acc[b].any (· == q) = false) →
        (∀ pos ∈ remaining, pos.layer < s.layerCount) →
        let result := remaining.foldl (fun clusters pos =>
            if clusters.any (fun cluster => cluster.any (· == pos)) then clusters
            else clusters ++ [structuralClusterList s pos]) acc
        ∀ (a b : Nat) (ha : a < result.length) (hb : b < result.length),
            a ≠ b → ∀ q, result[a].any (· == q) = true → result[b].any (· == q) = false by
      exact this _ [] (fun _ hk => absurd hk (by simp [List.length])) (fun _ _ ha => absurd ha (by simp [List.length]))
          (fun pos h_mem => by
              rw [List.mem_filter] at h_mem
              exact (allValid_any_iff_layer' s pos).mp
                  (List.any_eq_true.mpr ⟨pos, h_mem.1, BEq.rfl⟩))
          i j hi hj h_ne p hp1
    intro remaining
    induction remaining with
    | nil =>
      intro acc _ h_disj _
      dsimp only [List.foldl]
      exact h_disj
    | cons pos rest ih =>
      intro acc h_inv1 h_disj h_props
      have h_pos_layer := h_props pos (.head _)
      have h_rest_props := fun p hp => h_props p (.tail _ hp)
      dsimp only [List.foldl]
      split <;> rename_i h_cov
      · -- pos は既存クラスタにカバー → スキップ
        exact ih acc h_inv1 h_disj h_rest_props
      · -- pos は新規
        -- pos が既存クラスタに含まれないことの展開
        have h_pos_not_in : ∀ (k : Nat) (hk : k < acc.length),
            acc[k].any (· == pos) = false := by
          intro k hk
          cases h_eq : acc[k].any (· == pos) with
          | false => rfl
          | true =>
            have : acc.any (fun c => c.any (· == pos)) = true :=
                List.any_eq_true.mpr ⟨acc[k], List.getElem_mem hk, h_eq⟩
            rw [this] at h_cov; exact absurd h_cov (by decide)
        -- 新不変条件 1
        have h_inv1' : ∀ (k : Nat) (hk : k < (acc ++ [structuralClusterList s pos]).length),
            ∃ p, (acc ++ [structuralClusterList s pos])[k] = structuralClusterList s p ∧
            p.layer < s.layerCount := by
          intro k hk
          rw [List.length_append, List.length_singleton] at hk
          by_cases hk_lt : k < acc.length
          · rw [List.getElem_append_left hk_lt]; exact h_inv1 k hk_lt
          · have hk_eq : k = acc.length := by omega
            subst hk_eq
            rw [List.getElem_append_right (by omega)]
            exact ⟨pos, by simp, h_pos_layer⟩
        -- 新不変条件 2: 直接素性
        have h_disj' : ∀ (a b : Nat)
            (ha : a < (acc ++ [structuralClusterList s pos]).length)
            (hb : b < (acc ++ [structuralClusterList s pos]).length),
            a ≠ b → ∀ q, (acc ++ [structuralClusterList s pos])[a].any (· == q) = true →
            (acc ++ [structuralClusterList s pos])[b].any (· == q) = false := by
          intro a b ha hb h_ne_ab q hq_a
          rw [List.length_append, List.length_singleton] at ha hb
          by_cases ha_lt : a < acc.length <;> by_cases hb_lt : b < acc.length
          · -- a, b 共に acc 内
            rw [List.getElem_append_left ha_lt] at hq_a
            rw [List.getElem_append_left hb_lt]
            exact h_disj a b ha_lt hb_lt h_ne_ab q hq_a
          · -- a は acc 内, b は新規クラスタ
            have hb_eq : b = acc.length := by omega
            subst hb_eq
            rw [List.getElem_append_left ha_lt] at hq_a
            rw [List.getElem_append_right (by omega)]
            simp only [Nat.sub_self, List.getElem_cons_zero]
            cases h_nc_q : (structuralClusterList s pos).any (· == q) with
            | false => rfl
            | true =>
              obtain ⟨pos_a, h_eq_a, h_la⟩ := h_inv1 a ha_lt
              rw [h_eq_a] at hq_a
              have h_lc : s.layerCount > 0 := by omega
              have h_pos_in := structuralClusterList_shared_contains_seed
                  s pos_a pos q h_lc hq_a h_nc_q
              rw [← h_eq_a] at h_pos_in
              have h_pos_not := h_pos_not_in a ha_lt
              rw [h_pos_in] at h_pos_not; exact absurd h_pos_not (by decide)
          · -- a は新規クラスタ, b は acc 内
            have ha_eq : a = acc.length := by omega
            subst ha_eq
            rw [List.getElem_append_right (by omega)] at hq_a
            simp only [Nat.sub_self] at hq_a
            rw [List.getElem_append_left hb_lt]
            cases h_acc_q : acc[b].any (· == q) with
            | false => rfl
            | true =>
              obtain ⟨pos_b, h_eq_b, h_lb⟩ := h_inv1 b hb_lt
              rw [h_eq_b] at h_acc_q
              have h_lc : s.layerCount > 0 := by omega
              have h_pos_in := structuralClusterList_shared_contains_seed
                  s pos_b pos q h_lc h_acc_q hq_a
              rw [← h_eq_b] at h_pos_in
              have h_pos_not := h_pos_not_in b hb_lt
              rw [h_pos_in] at h_pos_not; exact absurd h_pos_not (by decide)
          · omega
        exact ih (acc ++ [structuralClusterList s pos])
            h_inv1' h_disj' h_rest_props

/-- 非空かつ非接地の位置が存在すれば floatingUnits は非空 -/
private theorem ungrounded_nonempty_implies_floatingUnits_nonempty (s : Shape) (p : QuarterPos)
        (h_valid : p.layer < s.layerCount)
        (h_ne : ∃ q, p.getQuarter s = some q ∧ !q.isEmpty = true)
        (h_ug : p ∉ groundedPositions s) :
        (floatingUnits s).isEmpty = false := by
    have h_ug_bool := (not_mem_groundedPositions_iff s p).mp h_ug
    obtain ⟨q, hq_some, hq_ne⟩ := h_ne
    -- 非空象限はピンか結合可能のいずれか
    have h_cases : q = .pin ∨ q.canFormBond = true := by
        cases q with
        | empty => simp [Quarter.isEmpty] at hq_ne
        | pin => exact .inl rfl
        | crystal => exact .inr rfl
        | colored => exact .inr rfl
    -- p は allValid に含まれる
    have h_p_allValid : p ∈ QuarterPos.allValid s := by
        have h_any := (allValid_any_iff_layer' s p).mpr h_valid
        rw [List.any_eq_true] at h_any
        obtain ⟨x, hx, hxe⟩ := h_any
        exact eq_of_beq hxe ▸ hx
    -- isEmpty = false を ∃ u ∈ floatingUnits s から導出
    suffices ∃ u, u ∈ floatingUnits s by
        obtain ⟨u, hu⟩ := this
        cases hl : floatingUnits s with
        | nil => rw [hl] at hu; nomatch hu
        | cons _ _ => rfl
    cases h_cases with
    | inl h_pin =>
        -- p はピン → floatingPins に含まれる
        subst h_pin
        exact ⟨.pin p, by
            unfold floatingUnits
            simp_rw [decide_not_mem_groundedPositions]
            apply List.mem_append_right
            exact List.mem_map.mpr ⟨p, List.mem_filter.mpr
                ⟨by unfold allIsolatedPins
                    exact List.mem_filter.mpr ⟨h_p_allValid, by rw [hq_some]⟩,
                 by simp [h_ug_bool]⟩, rfl⟩⟩
    | inr h_bond =>
        -- p は結合可能 → allStructuralClustersList のクラスタに含まれる
        have h_bondable : match p.getQuarter s with
                | some q => q.canFormBond = true | none => False := by
            rw [hq_some]; exact h_bond
        have h_covers := allStructuralClustersList_covers s p h_valid h_bondable
        rw [List.any_eq_true] at h_covers
        obtain ⟨c, hc_mem, hc_has_p⟩ := h_covers
        -- c = structuralClusterList s pos
        obtain ⟨pos, hc_is_sc, _, _⟩ :=
            allStructuralClustersList_is_structuralClusterList s c hc_mem
        -- c 内の全位置が非接地であることを示す
        have h_all_ug : c.all
                (fun x => !((groundedPositionsList s).any (· == x))) = true := by
            rw [List.all_eq_true]
            intro x hx
            cases h_x_ground : (groundedPositionsList s).any (· == x) with
            | false => rfl
            | true =>
                -- x が接地 → p も接地 → 矛盾
                exfalso
                -- 構造クラスタ内パスの導出
                have h_x_in_sc : (structuralClusterList s pos).any (· == x) = true := by
                    rw [← hc_is_sc]; exact List.any_eq_true.mpr ⟨x, hx, BEq.rfl⟩
                have h_p_in_sc := hc_is_sc ▸ hc_has_p
                have h_reach_pos_x := structuralClusterList_sound s pos x h_x_in_sc
                have h_reach_pos_p := structuralClusterList_sound s pos p h_p_in_sc
                -- x → pos → p（逆転 + 推移）
                have h_reach_x_pos := GenericReachable_reverse
                    (fun a b => isStructurallyBonded_symm s a b) h_reach_pos_x
                have h_reach_x_p :=
                    GenericReachable_trans h_reach_x_pos h_reach_pos_p
                -- 構造結合 → 接地接触
                have h_reach_gc := GenericReachable_mono
                    (fun a b => isStructurallyBonded_implies_isGroundingContact s a b)
                    h_reach_x_p
                -- BFS 閉包性から p も接地 → 矛盾
                have h_p_grounded := genericBfs_closed_contains_reachable
                    (isGroundingContact s) (QuarterPos.allValid s)
                    (groundedPositionsList s) (groundedPositionsList_inv s) x p
                    h_x_ground h_reach_gc
                    (fun a b h =>
                        (allValid_any_iff_layer' s b).mpr
                            (isGroundingContact_valid s a b h))
                rw [h_ug_bool] at h_p_grounded
                exact absurd h_p_grounded (by decide)
        -- c は浮遊クラスタ → floatingUnits に含まれる
        exact ⟨.cluster c, by
            unfold floatingUnits
            simp_rw [decide_not_mem_groundedPositions]
            apply List.mem_append_left
            exact List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc_mem, h_all_ug⟩, rfl⟩⟩

/-- floatingUnits が非空なら非空かつ非接地の位置が存在する -/
private theorem floatingUnits_nonempty_implies_exists_ungrounded (s : Shape)
        (h : (floatingUnits s).isEmpty = false) :
        ∃ p : QuarterPos, p.layer < s.layerCount ∧
            (∃ q, p.getQuarter s = some q ∧ !q.isEmpty = true) ∧
            p ∉ groundedPositions s := by
    -- floatingUnits s が非空なので要素を取得
    obtain ⟨u, hu_mem⟩ : ∃ u, u ∈ floatingUnits s := by
        cases hfl : floatingUnits s with
        | nil => rw [hfl] at h; simp at h
        | cons hd tl => exact ⟨hd, .head _⟩
    -- floatingUnits の定義を展開してメンバーシップ情報を抽出
    unfold floatingUnits at hu_mem
    simp_rw [decide_not_mem_groundedPositions] at hu_mem
    rw [List.mem_append] at hu_mem
    cases hu_mem with
    | inl h_cluster =>
        -- 浮遊クラスタから位置を抽出
        rw [List.mem_map] at h_cluster
        obtain ⟨c, hc_filt, _⟩ := h_cluster
        rw [List.mem_filter] at hc_filt
        obtain ⟨hc_in_all, hc_all_ug⟩ := hc_filt
        -- c = structuralClusterList s pos
        obtain ⟨pos, hc_is_sc, h_pos_valid, q_pos, hq_pos, h_pos_bond⟩ :=
            allStructuralClustersList_is_structuralClusterList s c hc_in_all
        -- pos ∈ c（BFS 開始位置は結果に含まれる）
        have h_pos_in_c : pos ∈ c := by
            have h_any : c.any (· == pos) = true := by
                rw [hc_is_sc]; unfold structuralClusterList; rw [structuralBfs_eq_generic]
                have h_n_pos : s.layerCount * 4 > 0 := by omega
                exact genericBfs_contains_start _ _ _ _ (Nat.mul_pos h_n_pos h_n_pos)
            rw [List.any_eq_true] at h_any
            obtain ⟨y, hy, hye⟩ := h_any
            have := eq_of_beq hye; subst this; exact hy
        -- pos は非接地
        have h_pos_ug : (groundedPositionsList s).any (· == pos) = false := by
            have := (List.all_eq_true.mp hc_all_ug) pos h_pos_in_c
            revert this; cases (groundedPositionsList s).any (· == pos) <;> simp
        -- pos は非空（canFormBond → not empty）
        have h_pos_ne : !q_pos.isEmpty = true := by
            cases q_pos <;> simp [Quarter.canFormBond] at h_pos_bond
                <;> simp [Quarter.isEmpty]
        exact ⟨pos, h_pos_valid, ⟨q_pos, hq_pos, h_pos_ne⟩,
            (not_mem_groundedPositions_iff s pos).mpr h_pos_ug⟩
    | inr h_pin =>
        -- 浮遊ピンから位置を抽出
        rw [List.mem_map] at h_pin
        obtain ⟨p', hp'_filt, _⟩ := h_pin
        rw [List.mem_filter] at hp'_filt
        obtain ⟨hp'_in_iso, hp'_ug⟩ := hp'_filt
        -- p' ∈ allIsolatedPins s → allValid + ピン条件
        unfold allIsolatedPins at hp'_in_iso
        rw [List.mem_filter] at hp'_in_iso
        obtain ⟨hp'_allValid, hp'_is_pin⟩ := hp'_in_iso
        -- p' は valid
        have h_p'_valid : p'.layer < s.layerCount :=
            (allValid_any_iff_layer' s p').mp
                (List.any_eq_true.mpr ⟨p', hp'_allValid, BEq.rfl⟩)
        -- p' は非空（ピンは非空）
        have h_p'_ne : ∃ q, p'.getQuarter s = some q ∧ !q.isEmpty = true := by
            cases hq : p'.getQuarter s with
            | none => simp [hq] at hp'_is_pin
            | some q =>
                cases q <;> simp_all [Quarter.isEmpty]
        -- p' は非接地
        have h_p'_ug : (groundedPositionsList s).any (· == p') = false := by
            revert hp'_ug; cases (groundedPositionsList s).any (· == p') <;> simp
        exact ⟨p', h_p'_valid, h_p'_ne,
            (not_mem_groundedPositions_iff s p').mpr h_p'_ug⟩

/-- floatingUnits が非空なら s.rotate180 でも非空 -/
private theorem floatingUnits_nonempty_implies_rotate180_nonempty (s : Shape)
        (h : (floatingUnits s).isEmpty = false) :
        (floatingUnits s.rotate180).isEmpty = false := by
    -- 非空・非接地の位置 p を抽出
    obtain ⟨p, h_valid, ⟨q, hq, h_ne⟩, h_ug⟩ :=
        floatingUnits_nonempty_implies_exists_ungrounded s h
    -- p.rotate180 は s.rotate180 でも非空・非接地
    apply ungrounded_nonempty_implies_floatingUnits_nonempty s.rotate180 p.rotate180
    · -- p.rotate180.layer < s.rotate180.layerCount
      rw [Shape.layerCount_rotate180]; exact h_valid
    · -- p.rotate180 の象限は非空
      exact ⟨q, by rw [getQuarter_rotate180]; exact hq, h_ne⟩
    · -- p.rotate180 は s.rotate180 で非接地
      exact fun h => h_ug ((mem_groundedPositions_rotate180 s p).mpr h)

/-- floatingUnits の isEmpty は rotate180 で不変 -/
theorem floatingUnits_isEmpty_rotate180 (s : Shape) :
        (floatingUnits s).isEmpty = (floatingUnits s.rotate180).isEmpty := by
    cases h : (floatingUnits s).isEmpty <;>
        cases h' : (floatingUnits s.rotate180).isEmpty
    · rfl
    · -- h: isEmpty = false, h': isEmpty r180 = true → s 非空なのに s.r180 空で矛盾
      exfalso
      have := floatingUnits_nonempty_implies_rotate180_nonempty s h
      rw [h'] at this; exact absurd this (by simp)
    · -- h: isEmpty = true, h': isEmpty r180 = false → s.r180 非空なのに s 空で矛盾
      exfalso
      have := floatingUnits_nonempty_implies_rotate180_nonempty s.rotate180 h'
      rw [Shape.rotate180_rotate180] at this; rw [h] at this; exact absurd this (by simp)
    · rfl

-- ============================================================
-- landingDistance / placeFallingUnit の rotate180 等変性
-- ============================================================

/-- isOccupied は rotate180 で等変 -/
private theorem isOccupied_rotate180 (obs : List Layer) (layer : Nat) (d : Direction) :
        isOccupied (obs.map Layer.rotate180) layer (d.rotate180) =
        isOccupied obs layer d := by
    simp only [isOccupied, List.getElem?_map]
    cases obs[layer]? with
    | none => rfl
    | some l => simp only [Option.map_some, getDir_rotate180]

/-- landed 判定 (positions.any) は rotate180 で不変 -/
private theorem landed_rotate180 (positions : List QuarterPos) (obs : List Layer) (d : Nat) :
        (positions.map QuarterPos.rotate180).any (fun p =>
            let newLayer := p.layer - d
            newLayer == 0 || isOccupied (obs.map Layer.rotate180) (newLayer - 1) p.dir) =
        positions.any (fun p =>
            let newLayer := p.layer - d
            newLayer == 0 || isOccupied obs (newLayer - 1) p.dir) := by
    induction positions with
    | nil => rfl
    | cons p rest ih =>
        simp only [List.map, List.any]
        rw [ih]
        congr 1
        simp only [QuarterPos.rotate180]
        congr 1
        exact isOccupied_rotate180 obs _ _

/-- landingDistance.check は rotate180 で不変 -/
private theorem landingDistance_check_rotate180 (positions : List QuarterPos) (obs : List Layer)
        (maxDrop d fuel : Nat) :
        landingDistance.check (obs.map Layer.rotate180) (positions.map QuarterPos.rotate180) maxDrop d fuel =
        landingDistance.check obs positions maxDrop d fuel := by
    induction fuel generalizing d with
    | zero => rfl
    | succ n ih =>
        simp only [landingDistance.check]
        split
        · rfl
        · rw [landed_rotate180]
          split
          · rfl
          · exact ih (d + 1)

/-- landingDistance は rotate180 で不変 -/
private theorem landingDistance_rotate180 (u : FallingUnit) (obs : List Layer) :
        landingDistance u.rotate180 (obs.map Layer.rotate180) = landingDistance u obs := by
    simp only [landingDistance]
    simp only [FallingUnit.minLayer_rotate180, FallingUnit.positions_rotate180]
    exact landingDistance_check_rotate180 u.positions obs u.minLayer 1 (u.minLayer + 1)

/-- setDir と rotate180 の可換性（一般版） -/
private theorem setDir_rotate180 (l : Layer) (d : Direction) (q : Quarter) :
        (QuarterPos.setDir l d q).rotate180 =
        QuarterPos.setDir (l.rotate180) (d.rotate180) q := by
    cases d <;> rfl

/-- replicate Layer.empty の map rotate180 -/
private theorem replicate_empty_rotate180 (n : Nat) :
        (List.replicate n Layer.empty).map Layer.rotate180 = List.replicate n Layer.empty := by
    induction n with
    | zero => rfl
    | succ n ih =>
        show Layer.empty.rotate180 :: (List.replicate n Layer.empty).map Layer.rotate180 =
             Layer.empty :: List.replicate n Layer.empty
        rw [ih]
        rfl

/-- placeQuarter は rotate180 で等変 -/
private theorem placeQuarter_rotate180 (layers : List Layer) (lay : Nat) (d : Direction) (q : Quarter) :
        (placeQuarter layers lay d q).map Layer.rotate180 =
        placeQuarter (layers.map Layer.rotate180) lay (d.rotate180) q := by
    simp only [placeQuarter, List.length_map]
    -- if 分岐を場合分け
    if h : lay < layers.length then
        simp only [h, ↓reduceIte, List.getElem?_map]
        cases layers[lay]? with
        | none => rfl
        | some l => simp only [Option.map_some]; rw [List.map_set, setDir_rotate180]
    else
        simp only [h, ↓reduceIte]
        -- 拡張リストを ext とする
        have hext : List.map Layer.rotate180 layers ++ List.replicate (lay + 1 - layers.length) Layer.empty =
            (layers ++ List.replicate (lay + 1 - layers.length) Layer.empty).map Layer.rotate180 := by
            rw [List.map_append, replicate_empty_rotate180]
        rw [hext, List.getElem?_map]
        cases (layers ++ List.replicate (lay + 1 - layers.length) Layer.empty)[lay]? with
        | none => rfl
        | some l =>
            simp only [Option.map_some]
            rw [List.map_set, setDir_rotate180]

/-- placeFallingUnit は rotate180 で等変 -/
private theorem placeFallingUnit_rotate180 (origShape : Shape) (obs : List Layer)
        (u : FallingUnit) (dropDist : Nat) :
        (placeFallingUnit origShape obs u dropDist).map Layer.rotate180 =
        placeFallingUnit origShape.rotate180 (obs.map Layer.rotate180) u.rotate180 dropDist := by
    simp only [placeFallingUnit, FallingUnit.positions_rotate180]
    -- u.positions について帰納法（acc を一般化）
    suffices h : ∀ (acc : List Layer),
        (u.positions.foldl (fun obs p =>
            match p.getQuarter origShape with
            | some q => placeQuarter obs (p.layer - dropDist) p.dir q
            | none => obs) acc).map Layer.rotate180 =
        (u.positions.map QuarterPos.rotate180).foldl (fun obs p =>
            match p.getQuarter origShape.rotate180 with
            | some q => placeQuarter obs (p.layer - dropDist) p.dir q
            | none => obs) (acc.map Layer.rotate180) from h obs
    intro acc
    induction u.positions generalizing acc with
    | nil => rfl
    | cons p rest ih =>
        simp only [List.foldl_cons, List.map_cons]
        -- step の等変性を示す
        have hstep : (match p.getQuarter origShape with
            | some q => placeQuarter acc (p.layer - dropDist) p.dir q
            | none => acc).map Layer.rotate180 =
            (match p.rotate180.getQuarter origShape.rotate180 with
            | some q => placeQuarter (acc.map Layer.rotate180)
                (p.rotate180.layer - dropDist) p.rotate180.dir q
            | none => acc.map Layer.rotate180) := by
            rw [getQuarter_rotate180]
            cases p.getQuarter origShape with
            | none => rfl
            | some q =>
                rw [QuarterPos.rotate180_layer, QuarterPos.rotate180_dir]
                exact placeQuarter_rotate180 ..
        rw [ih, hstep]

/-- flatMap + map の交換則 -/
private theorem flatMap_map_rotate180 (units : List FallingUnit) :
        (units.map FallingUnit.rotate180).flatMap FallingUnit.positions =
        (units.flatMap FallingUnit.positions).map QuarterPos.rotate180 := by
    induction units with
    | nil => rfl
    | cons u rest ih =>
        simp only [List.map_cons, List.flatMap_cons, List.map_append]
        rw [FallingUnit.positions_rotate180, ih]

/-- sorted.foldl (placeFallingUnit + landingDistance) の rotate180 等変性 -/
private theorem foldl_place_rotate180 (s : Shape) (sorted : List FallingUnit) (obs : List Layer) :
        (sorted.foldl (fun obs u =>
            let d := landingDistance u obs
            placeFallingUnit s obs u d
        ) obs).map Layer.rotate180 =
        (sorted.map FallingUnit.rotate180).foldl (fun obs u =>
            let d := landingDistance u obs
            placeFallingUnit s.rotate180 obs u d
        ) (obs.map Layer.rotate180) := by
    induction sorted generalizing obs with
    | nil => rfl
    | cons u rest ih =>
        simp only [List.foldl_cons, List.map_cons]
        rw [ih]
        congr 1
        rw [landingDistance_rotate180, placeFallingUnit_rotate180]

-- ============================================================
-- 浮遊位置の .any メンバーシップ等変性
-- ============================================================

/-- 非空・非接地・valid な位置は floatingUnits の位置に含まれる -/
private theorem ungrounded_in_floatingUnits_positions (s : Shape) (p : QuarterPos)
        (h_valid : p.layer < s.layerCount)
        (h_ne : ∃ q, p.getQuarter s = some q ∧ !q.isEmpty = true)
        (h_ug : p ∉ groundedPositions s) :
        ((floatingUnits s).flatMap FallingUnit.positions).any (· == p) = true := by
    have h_ug_bool := (not_mem_groundedPositions_iff s p).mp h_ug
    obtain ⟨q, hq_some, hq_ne⟩ := h_ne
    have h_cases : q = .pin ∨ q.canFormBond = true := by
        cases q with
        | empty => simp [Quarter.isEmpty] at hq_ne
        | pin => exact .inl rfl
        | crystal => exact .inr rfl
        | colored => exact .inr rfl
    have h_p_allValid : p ∈ QuarterPos.allValid s := by
        have h_any := (allValid_any_iff_layer' s p).mpr h_valid
        rw [List.any_eq_true] at h_any
        obtain ⟨x, hx, hxe⟩ := h_any; exact eq_of_beq hxe ▸ hx
    cases h_cases with
    | inl h_pin =>
        subst h_pin
        rw [List.any_eq_true]
        exact ⟨p, List.mem_flatMap.mpr ⟨.pin p, by
            unfold floatingUnits
            simp_rw [decide_not_mem_groundedPositions]
            apply List.mem_append_right
            exact List.mem_map.mpr ⟨p, List.mem_filter.mpr
                ⟨by unfold allIsolatedPins
                    exact List.mem_filter.mpr ⟨h_p_allValid, by rw [hq_some]⟩,
                 by simp [h_ug_bool]⟩, rfl⟩,
            by simp [FallingUnit.positions]⟩, BEq.rfl⟩
    | inr h_bond =>
        have h_bondable : match p.getQuarter s with
                | some qq => qq.canFormBond = true | none => False := by
            rw [hq_some]; exact h_bond
        have h_covers := allStructuralClustersList_covers s p h_valid h_bondable
        rw [List.any_eq_true] at h_covers
        obtain ⟨c, hc_mem, hc_has_p⟩ := h_covers
        obtain ⟨pos, hc_is_sc, _, _⟩ :=
            allStructuralClustersList_is_structuralClusterList s c hc_mem
        have h_all_ug : c.all
                (fun x => !((groundedPositionsList s).any (· == x))) = true := by
            rw [List.all_eq_true]; intro x hx
            cases h_x_ground : (groundedPositionsList s).any (· == x) with
            | false => rfl
            | true =>
                exfalso
                have h_x_in_sc : (structuralClusterList s pos).any (· == x) = true :=
                    hc_is_sc ▸ List.any_eq_true.mpr ⟨x, hx, BEq.rfl⟩
                have h_p_in_sc := hc_is_sc ▸ hc_has_p
                have h_reach_pos_x := structuralClusterList_sound s pos x h_x_in_sc
                have h_reach_pos_p := structuralClusterList_sound s pos p h_p_in_sc
                have h_reach_x_pos := GenericReachable_reverse
                    (fun a b => isStructurallyBonded_symm s a b) h_reach_pos_x
                have h_reach_x_p :=
                    GenericReachable_trans h_reach_x_pos h_reach_pos_p
                have h_reach_gc := GenericReachable_mono
                    (fun a b => isStructurallyBonded_implies_isGroundingContact s a b) h_reach_x_p
                have h_p_grounded := genericBfs_closed_contains_reachable
                    (isGroundingContact s) (QuarterPos.allValid s)
                    (groundedPositionsList s) (groundedPositionsList_inv s) x p
                    h_x_ground h_reach_gc
                    (fun a b hh =>
                        (allValid_any_iff_layer' s b).mpr
                            (isGroundingContact_valid s a b hh))
                rw [h_ug_bool] at h_p_grounded; exact absurd h_p_grounded (by decide)
        rw [List.any_eq_true]
        have h_p_mem : p ∈ c := by
            rw [List.any_eq_true] at hc_has_p
            obtain ⟨y, hy, hye⟩ := hc_has_p; exact eq_of_beq hye ▸ hy
        exact ⟨p, List.mem_flatMap.mpr ⟨.cluster c, by
            unfold floatingUnits
            simp_rw [decide_not_mem_groundedPositions]
            apply List.mem_append_left
            exact List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc_mem, h_all_ug⟩, rfl⟩,
            h_p_mem⟩, BEq.rfl⟩

/-- floatingUnits の位置にある象限は非空である -/
private theorem floatingUnits_positions_getQuarter (s : Shape) (p : QuarterPos)
        (h : ((floatingUnits s).flatMap FallingUnit.positions).any (· == p) = true) :
        p.layer < s.layerCount ∧
        (∃ q, p.getQuarter s = some q ∧ !q.isEmpty = true) ∧
        p ∉ groundedPositions s := by
    rw [List.any_eq_true] at h
    obtain ⟨q, hq_mem, hq_eq⟩ := h
    have := eq_of_beq hq_eq; subst this
    rw [List.mem_flatMap] at hq_mem
    obtain ⟨u, hu_mem, hq_in_u⟩ := hq_mem
    unfold floatingUnits at hu_mem
    simp_rw [decide_not_mem_groundedPositions] at hu_mem
    simp only [List.mem_append, List.mem_map] at hu_mem
    cases hu_mem with
    | inl h_cluster =>
        obtain ⟨c, hc_filt, hc_eq⟩ := h_cluster; subst hc_eq
        rw [List.mem_filter] at hc_filt
        obtain ⟨hc_in_all, hc_all_ug⟩ := hc_filt
        obtain ⟨pos, hc_is_sc, _, qq, hqq, h_bond⟩ :=
            allStructuralClustersList_is_structuralClusterList s c hc_in_all
        have h_q_in_sc : (structuralClusterList s pos).any (· == q) = true :=
            hc_is_sc ▸ List.any_eq_true.mpr ⟨q, hq_in_u, BEq.rfl⟩
        -- q は canFormBond (構造的到達可能性から)
        have h_reach := structuralClusterList_sound s pos q h_q_in_sc
        have h_q_bond := structuralReachable_canFormBond s pos q h_reach ⟨qq, hqq, h_bond⟩
        obtain ⟨w, hw, hwb⟩ := h_q_bond
        -- q.layer < s.layerCount: getQuarter が some → layer は範囲内
        have h_q_valid : q.layer < s.layerCount := by
            simp only [Shape.layerCount]
            have hq := hw; unfold QuarterPos.getQuarter at hq
            cases hl : s.layers[q.layer]? with
            | none => simp [hl] at hq
            | some _ => exact (List.getElem?_eq_some_iff.mp hl).1
        -- q は非接地
        have h_q_ug : (groundedPositionsList s).any (· == q) = false := by
            have := (List.all_eq_true.mp hc_all_ug) q hq_in_u
            revert this; cases (groundedPositionsList s).any (· == q) <;> simp
        -- q は非空
        have h_q_ne : ∃ qq', q.getQuarter s = some qq' ∧ !qq'.isEmpty = true :=
            ⟨w, hw, by cases w <;> simp [Quarter.canFormBond, Quarter.isEmpty] at hwb ⊢⟩
        exact ⟨h_q_valid, h_q_ne, (not_mem_groundedPositions_iff s q).mpr h_q_ug⟩
    | inr h_pin =>
        obtain ⟨p0, hp0_filt, hp0_eq⟩ := h_pin; subst hp0_eq
        rw [List.mem_filter] at hp0_filt
        obtain ⟨hp0_iso, hp0_ug⟩ := hp0_filt
        simp only [FallingUnit.positions, List.mem_singleton] at hq_in_u; subst hq_in_u
        unfold allIsolatedPins at hp0_iso
        rw [List.mem_filter] at hp0_iso
        obtain ⟨hp0_allValid, hp0_is_pin⟩ := hp0_iso
        have h_valid : q.layer < s.layerCount :=
            (allValid_any_iff_layer' s q).mp
                (List.any_eq_true.mpr ⟨q, hp0_allValid, BEq.rfl⟩)
        have h_ne : ∃ qq', q.getQuarter s = some qq' ∧ !qq'.isEmpty = true := by
            cases hgq : q.getQuarter s with
            | none => simp [hgq] at hp0_is_pin
            | some v => cases v <;> simp_all [Quarter.isEmpty]
        have h_ug : (groundedPositionsList s).any (· == q) = false := by
            revert hp0_ug; cases (groundedPositionsList s).any (· == q) <;> simp
        exact ⟨h_valid, h_ne, (not_mem_groundedPositions_iff s q).mpr h_ug⟩

/-- 浮遊単位の位置メンバーシップは rotate180 で保存される -/
theorem falling_positions_any_rotate180 (s : Shape) (p : QuarterPos) :
        ((floatingUnits s).flatMap FallingUnit.positions).any (· == p) =
        ((floatingUnits s.rotate180).flatMap FallingUnit.positions).any (· == p.rotate180) := by
    cases h : ((floatingUnits s).flatMap FallingUnit.positions).any (· == p) with
    | true =>
        symm
        -- p は valid, non-empty, non-grounded
        obtain ⟨h_valid, ⟨q, hq, hq_ne⟩, h_ug⟩ := floatingUnits_positions_getQuarter s p h
        -- p.r180 は s.r180 で valid, non-empty, non-grounded
        apply ungrounded_in_floatingUnits_positions s.rotate180 p.rotate180
        · rw [Shape.layerCount_rotate180]; exact h_valid
        · exact ⟨q, by rw [getQuarter_rotate180]; exact hq, hq_ne⟩
        · exact fun h => h_ug ((mem_groundedPositions_rotate180 s p).mpr h)
    | false =>
        symm
        cases h' : ((floatingUnits s.rotate180).flatMap FallingUnit.positions).any
                (· == p.rotate180) with
        | false => rfl
        | true =>
            exfalso
            obtain ⟨h_valid', ⟨q', hq', hq_ne'⟩, h_ug'⟩ :=
                floatingUnits_positions_getQuarter s.rotate180 p.rotate180 h'
            have h_should_be_true := ungrounded_in_floatingUnits_positions s p
                (by rw [← Shape.layerCount_rotate180]; exact h_valid')
                ⟨q', by rw [← getQuarter_rotate180]; exact hq', hq_ne'⟩
                (fun hp => h_ug' ((mem_groundedPositions_rotate180 s p).mp hp))
            rw [h] at h_should_be_true; exact absurd h_should_be_true (by decide)

/-- QuarterPos の BEq は rotate180 で交換可能: (x.r180 == p) = (x == p.r180) -/
private theorem beq_rotate180_comm (x p : QuarterPos) :
        (x.rotate180 == p) = (x == p.rotate180) := by
    have h := quarterPos_beq_rotate180 x p.rotate180
    simp only [QuarterPos.rotate180_rotate180] at h
    exact h

/-- List.map QuarterPos.rotate180 後の .any と rotate180 の関係（公開版） -/
theorem any_map_rotate180_beq (ps : List QuarterPos) (p : QuarterPos) :
        (ps.map QuarterPos.rotate180).any (· == p) =
        ps.any (· == p.rotate180) := by
    induction ps with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.map, List.any, ih, beq_rotate180_comm]

-- ============================================================
-- settle_foldl_eq: foldl 等価性の証明基盤
-- ============================================================

/-- .any BEq メンバーシップ等価から任意述語の .any 等価を導く -/
private theorem any_pred_ext {l1 l2 : List QuarterPos}
        (h : ∀ p, l1.any (· == p) = l2.any (· == p)) (f : QuarterPos → Bool) :
        l1.any f = l2.any f := by
    cases h1 : l1.any f with
    | true =>
        symm; rw [List.any_eq_true] at h1 ⊢
        obtain ⟨x, hx_mem, hfx⟩ := h1
        have : l1.any (· == x) = true := List.any_eq_true.mpr ⟨x, hx_mem, BEq.rfl⟩
        rw [h] at this
        obtain ⟨y, hy_mem, hy_beq⟩ := List.any_eq_true.mp this
        have hyx : y = x := eq_of_beq (show (y == x) = true from hy_beq)
        exact ⟨x, hyx ▸ hy_mem, hfx⟩
    | false =>
        symm; cases h2 : l2.any f with
        | false => rfl
        | true =>
            exfalso
            obtain ⟨x, hx_mem, hfx⟩ := List.any_eq_true.mp h2
            have : l2.any (· == x) = true := List.any_eq_true.mpr ⟨x, hx_mem, BEq.rfl⟩
            rw [← h] at this
            obtain ⟨y, hy_mem, hy_beq⟩ := List.any_eq_true.mp this
            have hyx : y = x := eq_of_beq (show (y == x) = true from hy_beq)
            have : l1.any f = true := List.any_eq_true.mpr ⟨x, hyx ▸ hy_mem, hfx⟩
            rw [h1] at this; exact Bool.false_ne_true this

/-- foldl min は初期値以下 -/
private theorem foldl_min_le_init (l : List QuarterPos) (init : Nat) :
        l.foldl (fun acc q => min acc q.layer) init ≤ init := by
    induction l generalizing init with
    | nil => simp [List.foldl]
    | cons x xs ih =>
        simp only [List.foldl]
        exact Nat.le_trans (ih (min init x.layer)) (Nat.min_le_left init x.layer)

/-- foldl min はリスト要素の layer 以下 -/
private theorem foldl_min_le_elem (l : List QuarterPos) (init : Nat) (q : QuarterPos)
        (hq : q ∈ l) :
        l.foldl (fun acc p => min acc p.layer) init ≤ q.layer := by
    induction l generalizing init with
    | nil => nomatch hq
    | cons x xs ih =>
        simp only [List.foldl]
        cases hq with
        | head =>
            exact Nat.le_trans (foldl_min_le_init xs (min init q.layer))
                (Nat.min_le_right init q.layer)
        | tail _ hmem =>
            exact ih (min init x.layer) hmem

/-- cons リストの foldl min はどの要素の layer 以下 -/
private theorem foldl_min_le_mem (p : QuarterPos) (rest : List QuarterPos) (x : QuarterPos)
        (hx : x ∈ p :: rest) :
        rest.foldl (fun acc q => min acc q.layer) p.layer ≤ x.layer := by
    cases hx with
    | head => exact foldl_min_le_init rest p.layer
    | tail _ hmem => exact foldl_min_le_elem rest p.layer x hmem

/-- foldl min の結果は init か、リスト要素の layer に等しい -/
private theorem foldl_min_attained (l : List QuarterPos) (init : Nat) :
        l.foldl (fun acc q => min acc q.layer) init = init ∨
        ∃ q ∈ l, l.foldl (fun acc q => min acc q.layer) init = q.layer := by
    induction l generalizing init with
    | nil => exact Or.inl rfl
    | cons x xs ih =>
        simp only [List.foldl]
        cases ih (min init x.layer) with
        | inl heq =>
            by_cases hle : init ≤ x.layer
            · exact Or.inl (heq.trans (Nat.min_eq_left hle))
            · exact Or.inr ⟨x, .head xs, heq.trans (by omega)⟩
        | inr hexist =>
            obtain ⟨q, hq_mem, hq_eq⟩ := hexist
            exact Or.inr ⟨q, .tail x hq_mem, hq_eq⟩

/-- .any BEq 等価リストの逆方向メンバーシップ -/
private theorem mem_of_any_beq_eq {l1 l2 : List QuarterPos}
        (h : ∀ p, l1.any (· == p) = l2.any (· == p))
        {x : QuarterPos} (hx : x ∈ l2) : x ∈ l1 := by
    have : l2.any (· == x) = true := List.any_eq_true.mpr ⟨x, hx, BEq.rfl⟩
    rw [← h] at this
    obtain ⟨y, hy_mem, hy_beq⟩ := List.any_eq_true.mp this
    have hyx : y = x := eq_of_beq hy_beq
    subst hyx; exact hy_mem

/-- positions の .any BEq 等価な FallingUnit は同じ minLayer を持つ -/
private theorem minLayer_ext {u1 u2 : FallingUnit}
        (h : ∀ p, u1.positions.any (· == p) = u2.positions.any (· == p)) :
        u1.minLayer = u2.minLayer := by
    simp only [FallingUnit.minLayer]
    -- positions をローカル変数に一般化する
    generalize hl1 : u1.positions = l1
    generalize hl2 : u2.positions = l2
    rw [hl1, hl2] at h
    cases l1 with
    | nil =>
        simp only []
        cases l2 with
        | nil => rfl
        | cons p2 rest2 =>
            exfalso
            have : (p2 :: rest2).any (· == p2) = true :=
                List.any_eq_true.mpr ⟨p2, .head rest2, BEq.rfl⟩
            rw [← h] at this; exact Bool.false_ne_true this
    | cons p1 rest1 =>
        cases l2 with
        | nil =>
            simp only []
            exfalso
            have : (p1 :: rest1).any (· == p1) = true :=
                List.any_eq_true.mpr ⟨p1, .head rest1, BEq.rfl⟩
            rw [h] at this; exact Bool.false_ne_true this
        | cons p2 rest2 =>
            simp only []
            apply Nat.le_antisymm
            · -- rest1.foldl ... p1.layer ≤ rest2.foldl ... p2.layer
              cases foldl_min_attained rest2 p2.layer with
              | inl heq =>
                  rw [heq]
                  exact foldl_min_le_mem p1 rest1 p2
                      (mem_of_any_beq_eq h (.head rest2))
              | inr hexist =>
                  obtain ⟨q, hq_mem, hq_eq⟩ := hexist
                  rw [hq_eq]
                  exact foldl_min_le_mem p1 rest1 q
                      (mem_of_any_beq_eq h (.tail p2 hq_mem))
            · -- rest2.foldl ... p2.layer ≤ rest1.foldl ... p1.layer
              cases foldl_min_attained rest1 p1.layer with
              | inl heq =>
                  rw [heq]
                  exact foldl_min_le_mem p2 rest2 p1
                      (mem_of_any_beq_eq (fun p => (h p).symm) (.head rest1))
              | inr hexist =>
                  obtain ⟨q, hq_mem, hq_eq⟩ := hexist
                  rw [hq_eq]
                  exact foldl_min_le_mem p2 rest2 q
                      (mem_of_any_beq_eq (fun p => (h p).symm) (.tail p1 hq_mem))

/-- positions の .any 等価な FallingUnit は同じ landingDistance を持つ -/
private theorem landingDistance_ext {u1 u2 : FallingUnit}
        (h : ∀ p, u1.positions.any (· == p) = u2.positions.any (· == p))
        (obs : List Layer) :
        landingDistance u1 obs = landingDistance u2 obs := by
    have h_ml : u1.minLayer = u2.minLayer := minLayer_ext h
    simp only [landingDistance]
    rw [h_ml]
    suffices ∀ d fuel, landingDistance.check obs u1.positions u2.minLayer d fuel =
                       landingDistance.check obs u2.positions u2.minLayer d fuel from
        this 1 (u2.minLayer + 1)
    intro d fuel
    induction fuel generalizing d with
    | zero => rfl
    | succ n ih =>
        simp only [landingDistance.check, any_pred_ext h, ih]

-- ============================================================
-- placeFallingUnit_ext / settle_foldl_eq の補助補題群
-- ============================================================

/-- setDir は異なる方角で可換 -/
private theorem setDir_setDir_comm (l : Layer) {d1 d2 : Direction}
        (q1 q2 : Quarter) (h : d1 ≠ d2) :
        QuarterPos.setDir (QuarterPos.setDir l d1 q1) d2 q2 =
        QuarterPos.setDir (QuarterPos.setDir l d2 q2) d1 q1 := by
    cases d1 <;> cases d2 <;> simp_all [QuarterPos.setDir]

/-- setDir は同方角で上書き -/
private theorem setDir_setDir_same (l : Layer) (d : Direction) (q1 q2 : Quarter) :
        QuarterPos.setDir (QuarterPos.setDir l d q1) d q2 =
        QuarterPos.setDir l d q2 := by
    cases d <;> rfl

/-- placeQuarter の完全な getElem? 特性 -/
private theorem placeQuarter_getElem?_full (obs : List Layer) (lay i : Nat)
        (d : Direction) (q : Quarter) :
        (placeQuarter obs lay d q)[i]? =
        if i < max obs.length (lay + 1) then
          if i = lay then some (QuarterPos.setDir (obs.getD lay Layer.empty) d q)
          else some (obs.getD i Layer.empty)
        else none := by
    -- placeQuarter の let 束縛を場合分けで展開
    by_cases hlt : lay < obs.length
    · -- lay < obs.length の場合: extended = obs
      have hmax : max obs.length (lay + 1) = obs.length := by omega
      have hpq : placeQuarter obs lay d q =
          obs.set lay (QuarterPos.setDir (obs.getD lay Layer.empty) d q) := by
        unfold placeQuarter
        simp only [hlt, ite_true, List.getElem?_eq_getElem hlt]
        congr 1
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
        rfl
      rw [hpq, hmax]
      by_cases hi : i < obs.length
      · rw [if_pos hi]
        by_cases heq : i = lay
        · subst heq; rw [if_pos rfl]
          simp [hi, List.getD_eq_getElem?_getD]
        · rw [if_neg heq]
          have hne : lay ≠ i := fun h => heq h.symm
          simp [hne, hi, List.getD_eq_getElem?_getD]
      · rw [if_neg hi]
        rw [List.getElem?_eq_none_iff.mpr (by simp; omega)]
    · -- lay ≥ obs.length の場合: extended = obs ++ replicate ...
      have hmax : max obs.length (lay + 1) = lay + 1 := by omega
      have hext_len : (obs ++ List.replicate (lay + 1 - obs.length) Layer.empty).length =
          lay + 1 := by simp [List.length_append, List.length_replicate]; omega
      have hlay : lay < (obs ++ List.replicate (lay + 1 - obs.length) Layer.empty).length := by
        rw [hext_len]; omega
      have hpq : placeQuarter obs lay d q =
          (obs ++ List.replicate (lay + 1 - obs.length) Layer.empty).set lay
          (QuarterPos.setDir Layer.empty d q) := by
        unfold placeQuarter
        simp only [show ¬(lay < obs.length) from by omega, ite_false,
            List.getElem?_eq_getElem hlay]
        congr 1
        rw [List.getElem_append_right (by omega)]
        simp [List.getElem_replicate]
      have hgetD_lay : obs.getD lay Layer.empty = Layer.empty := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr (by omega)]
        rfl
      rw [hpq, hmax, hgetD_lay]
      by_cases hi : i < lay + 1
      · rw [if_pos hi]
        by_cases heq : i = lay
        · subst heq; rw [if_pos rfl]
          simp [hext_len]
        · rw [if_neg heq]
          have hne : lay ≠ i := fun h => heq h.symm
          simp only [List.getElem?_set, hne, ite_false, hext_len]
          rw [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append]
          split
          · rename_i hi2; rw [List.getElem?_eq_getElem hi2]; rfl
          · rename_i hi2
            simp only [List.getElem?_replicate]
            split
            · have : obs[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
              simp [this]
            · omega
      · rw [if_neg hi]
        rw [List.getElem?_eq_none_iff.mpr (by simp [List.length_set, hext_len]; omega)]

/-- placeQuarter の結果のリスト長 -/
private theorem placeQuarter_length (obs : List Layer) (lay : Nat)
        (d : Direction) (q : Quarter) :
        (placeQuarter obs lay d q).length = max obs.length (lay + 1) := by
    apply Nat.le_antisymm
    · -- ≤: index = max では getElem? が none
      exact List.getElem?_eq_none_iff.mp (by
        have := placeQuarter_getElem?_full obs lay (max obs.length (lay + 1)) d q
        rw [if_neg (by omega)] at this; exact this)
    · -- ≥: length < max なら index = length で some が返り矛盾
      have : ¬((placeQuarter obs lay d q).length < max obs.length (lay + 1)) := by
        intro hlt
        have h := placeQuarter_getElem?_full obs lay (placeQuarter obs lay d q).length d q
        rw [List.getElem?_eq_none_iff.mpr (by omega), if_pos hlt] at h
        split at h <;> contradiction
      omega

/-- placeQuarter の getD 特性（範囲内） -/
private theorem placeQuarter_getD (obs : List Layer) (lay i : Nat)
        (d : Direction) (q : Quarter)
        (hi : i < max obs.length (lay + 1)) :
        (placeQuarter obs lay d q).getD i Layer.empty =
        if i = lay then QuarterPos.setDir (obs.getD lay Layer.empty) d q
        else obs.getD i Layer.empty := by
    rw [List.getD_eq_getElem?_getD, placeQuarter_getElem?_full, if_pos hi]
    split <;> simp

/-- placeQuarter の getD 特性（i ≠ lay のとき境界条件不要） -/
private theorem placeQuarter_getD_ne (obs : List Layer) (lay i : Nat)
        (d : Direction) (q : Quarter) (hne : i ≠ lay) :
        (placeQuarter obs lay d q).getD i Layer.empty = obs.getD i Layer.empty := by
    rw [List.getD_eq_getElem?_getD, placeQuarter_getElem?_full]
    by_cases hi : i < max obs.length (lay + 1)
    · rw [if_pos hi, if_neg hne]; simp
    · rw [if_neg hi]
      simp only [Option.getD_none, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none_iff.mpr (show obs.length ≤ i by omega)]

/-- placeQuarter は同引数で冪等 -/
private theorem placeQuarter_idem (obs : List Layer) (lay : Nat)
        (d : Direction) (q : Quarter) :
        placeQuarter (placeQuarter obs lay d q) lay d q =
        placeQuarter obs lay d q := by
    apply List.ext_getElem?; intro i
    rw [placeQuarter_getElem?_full, placeQuarter_getElem?_full]
    simp only [placeQuarter_length,
        show max (max obs.length (lay + 1)) (lay + 1) = max obs.length (lay + 1) from by omega]
    split
    · rename_i hi
      split
      · rename_i heq; subst heq
        congr 1
        rw [placeQuarter_getD _ _ _ _ _ (by omega)]
        simp [setDir_setDir_same]
      · rename_i hne; congr 1
        rw [placeQuarter_getD _ _ _ _ _ (by omega)]
        simp [hne]
    · rfl

/-- placeQuarter は異なる対象レイヤで可換 -/
private theorem placeQuarter_comm_layer_ne (obs : List Layer)
        (l1 l2 : Nat) (d1 d2 : Direction) (q1 q2 : Quarter)
        (hne : l1 ≠ l2) :
        placeQuarter (placeQuarter obs l1 d1 q1) l2 d2 q2 =
        placeQuarter (placeQuarter obs l2 d2 q2) l1 d1 q1 := by
    apply List.ext_getElem?; intro i
    simp only [placeQuarter_getElem?_full, placeQuarter_length]
    have hmax : max (max obs.length (l1 + 1)) (l2 + 1) =
                max (max obs.length (l2 + 1)) (l1 + 1) := by omega
    rw [hmax]
    by_cases hi : i < max (max obs.length (l2 + 1)) (l1 + 1)
    · rw [if_pos hi, if_pos hi]
      by_cases hil2 : i = l2
      · subst hil2
        rw [if_pos rfl, if_neg (Ne.symm hne)]
        congr 1
        rw [placeQuarter_getD_ne _ _ _ _ _ (Ne.symm hne)]
        rw [placeQuarter_getD _ _ _ _ _ (by omega)]
        simp
      · rw [if_neg hil2]
        by_cases hil1 : i = l1
        · subst hil1
          rw [if_pos rfl]
          congr 1
          rw [placeQuarter_getD _ _ _ _ _ (by omega)]
          rw [placeQuarter_getD_ne _ _ _ _ _ hne]
          simp
        · rw [if_neg hil1]
          congr 1
          rw [placeQuarter_getD_ne _ _ _ _ _ hil1]
          rw [placeQuarter_getD_ne _ _ _ _ _ hil2]
    · rw [if_neg hi, if_neg hi]

/-- placeQuarter は同レイヤ・異方角で可換 -/
private theorem placeQuarter_comm_dir_ne (obs : List Layer)
        (lay : Nat) (d1 d2 : Direction) (q1 q2 : Quarter)
        (hne : d1 ≠ d2) :
        placeQuarter (placeQuarter obs lay d1 q1) lay d2 q2 =
        placeQuarter (placeQuarter obs lay d2 q2) lay d1 q1 := by
    apply List.ext_getElem?; intro i
    simp only [placeQuarter_getElem?_full, placeQuarter_length,
        show max (max obs.length (lay + 1)) (lay + 1) = max obs.length (lay + 1) from by omega]
    split
    · rename_i hi
      split
      · rename_i heq; subst heq
        congr 1
        rw [placeQuarter_getD _ _ _ _ _ (by omega)]
        rw [placeQuarter_getD _ _ _ _ _ (by omega)]
        simp [setDir_setDir_comm _ _ _ hne]
      · rename_i hne2; congr 1
        rw [placeQuarter_getD _ _ _ _ _ (by omega)]
        rw [placeQuarter_getD _ _ _ _ _ (by omega)]
        simp [hne2]
    · rfl

/-- 可換・冪等な操作の foldl 吸収: x ∈ l のとき事前適用は吸収される
    可換性・冪等性は述語 S を満たす要素間でのみ要求される -/
private theorem foldl_absorb {β : Type}
        (f : β → QuarterPos → β) (S : QuarterPos → Prop)
        (h_comm : ∀ p1 p2, S p1 → S p2 → p1 ≠ p2 → ∀ s, f (f s p1) p2 = f (f s p2) p1)
        (h_idem : ∀ p, S p → ∀ s, f (f s p) p = f s p)
        (x : QuarterPos) (hsx : S x)
        (l : List QuarterPos) (hl : ∀ y, y ∈ l → S y) (hx : x ∈ l)
        (init : β) :
        l.foldl f (f init x) = l.foldl f init := by
    induction l generalizing init with
    | nil => contradiction
    | cons y ys ih =>
        simp only [List.foldl_cons]
        have hsy : S y := hl y (.head ys)
        have hys : ∀ z, z ∈ ys → S z := fun z hz => hl z (.tail y hz)
        cases List.mem_cons.mp hx with
        | inl heq =>
            subst heq; rw [h_idem x hsx]
        | inr hx_ys =>
            by_cases hxy : x = y
            · subst hxy; rw [h_idem x hsx]
            · rw [h_comm x y hsx hsy hxy]; exact ih hys hx_ys _

/-- 可換・冪等な操作の foldl 抽出: x 要素を前に出せる
    可換性・冪等性は述語 S を満たす要素間でのみ要求される -/
private theorem foldl_extract {β : Type}
        (f : β → QuarterPos → β) (S : QuarterPos → Prop)
        (h_comm : ∀ p1 p2, S p1 → S p2 → p1 ≠ p2 → ∀ s, f (f s p1) p2 = f (f s p2) p1)
        (h_idem : ∀ p, S p → ∀ s, f (f s p) p = f s p)
        (x : QuarterPos) (hsx : S x)
        (l : List QuarterPos) (hl : ∀ y, y ∈ l → S y) (hx : x ∈ l)
        (init : β) :
        l.foldl f init = (l.filter (! · == x)).foldl f (f init x) := by
    induction l generalizing init with
    | nil => contradiction
    | cons y ys ih =>
        simp only [List.foldl_cons, List.filter_cons]
        have hsy : S y := hl y (.head ys)
        have hys : ∀ z, z ∈ ys → S z := fun z hz => hl z (.tail y hz)
        cases List.mem_cons.mp hx with
        | inl heq =>
            subst heq
            simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            by_cases hxys : x ∈ ys
            · rw [foldl_absorb f S h_comm h_idem x hsx ys hys hxys]
              exact ih hys hxys _
            · congr 1; symm
              rw [List.filter_eq_self]
              intro a ha
              cases hab : (a == x) with
              | false => rfl
              | true => exact absurd (eq_of_beq hab ▸ ha) hxys
        | inr hx_ys =>
            by_cases hxy : y = x
            · -- subst hxy で x が y に置換される
              subst hxy
              simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              rw [foldl_absorb f S h_comm h_idem y hsy ys hys hx_ys]
              exact ih hys hx_ys _
            · have : (! (y == x)) = true := by simp [hxy]
              simp only [this, ↓reduceIte, List.foldl_cons]
              rw [h_comm x y hsx hsy (Ne.symm hxy)]
              exact ih hys hx_ys _

/-- .any BEq 等価なリストは可換・冪等な foldl で同一結果を生む
    可換性・冪等性は述語 S を満たす要素間でのみ要求される -/
private theorem foldl_any_eq_of_comm_idem {β : Type}
        (f : β → QuarterPos → β) (S : QuarterPos → Prop)
        (h_comm : ∀ p1 p2, S p1 → S p2 → p1 ≠ p2 → ∀ s, f (f s p1) p2 = f (f s p2) p1)
        (h_idem : ∀ p, S p → ∀ s, f (f s p) p = f s p)
        (l1 l2 : List QuarterPos)
        (hl1 : ∀ y, y ∈ l1 → S y) (hl2 : ∀ y, y ∈ l2 → S y)
        (h : ∀ p, l1.any (· == p) = l2.any (· == p))
        (init : β) :
        l1.foldl f init = l2.foldl f init := by
    induction l1 generalizing l2 init with
    | nil =>
        cases l2 with
        | nil => rfl
        | cons y ys =>
            exfalso
            have : (y :: ys).any (· == y) = true :=
                List.any_eq_true.mpr ⟨y, .head ys, beq_self_eq_true y⟩
            rw [← h] at this
            exact Bool.false_ne_true this
    | cons x xs ih =>
        simp only [List.foldl_cons]
        have hsx : S x := hl1 x (.head xs)
        have hl1_xs : ∀ z, z ∈ xs → S z := fun z hz => hl1 z (.tail x hz)
        -- x ∈ l2
        have hx_l2 : x ∈ l2 := by
            have h1 : l2.any (· == x) = true := by
                rw [← h]
                exact List.any_eq_true.mpr ⟨x, .head xs, beq_self_eq_true x⟩
            obtain ⟨y, hy_mem, hy_beq⟩ := List.any_eq_true.mp h1
            exact eq_of_beq hy_beq ▸ hy_mem
        by_cases hx_xs : x ∈ xs
        · -- x ∈ xs: xs の .any は l1 の .any と同じ
          have h_any_xs : ∀ p, xs.any (· == p) = l2.any (· == p) := by
              intro p
              have hp := h p
              simp only [List.any_cons] at hp
              cases hbool : (x == p) with
              | true =>
                  simp only [hbool, Bool.true_or] at hp
                  have h_xs_true : xs.any (· == p) = true :=
                      List.any_eq_true.mpr ⟨x, hx_xs, hbool⟩
                  rw [h_xs_true]; exact hp
              | false =>
                  simp only [hbool, Bool.false_or] at hp
                  exact hp
          rw [foldl_absorb f S h_comm h_idem x hsx xs hl1_xs hx_xs]
          exact ih l2 hl1_xs hl2 h_any_xs _
        · -- x ∉ xs: filter で x を除去
          have hl2_filter : ∀ y, y ∈ l2.filter (! · == x) → S y :=
              fun y hy => hl2 y (List.mem_filter.mp hy).1
          have h_any_filter : ∀ p, xs.any (· == p) =
                  (l2.filter (! · == x)).any (· == p) := by
              intro p
              rw [List.any_filter]
              by_cases hpx : p = x
              · -- p = x case: rw で置換（subst を避ける）
                rw [hpx]
                have h_lhs : xs.any (· == x) = false := by
                    rw [Bool.eq_false_iff]
                    intro h_contra
                    have ⟨a, ha, hax⟩ := List.any_eq_true.mp h_contra
                    exact hx_xs (eq_of_beq hax ▸ ha)
                have h_rhs : l2.any (fun a => (! (a == x)) && (a == x)) = false := by
                    rw [Bool.eq_false_iff]
                    intro h_contra
                    have ⟨a, _, hax⟩ := List.any_eq_true.mp h_contra
                    simp at hax
                rw [h_lhs, h_rhs]
              · have hne_comm : (! (x == p)) = true := by
                    simp [ne_eq]; exact Ne.symm hpx
                -- (fun a => (!(a == x)) && (a == p)) を (· == p) に簡約
                have h_filter_eq : (fun a : QuarterPos => (!(a == x)) && (a == p)) = (· == p) := by
                    funext a
                    cases hap : (a == p) with
                    | false => simp
                    | true =>
                        -- a = p なので !(a == x) = !(p == x) = true
                        have haeqp : a = p := eq_of_beq hap
                        rw [haeqp]
                        rw [show (p == x) = (x == p) from BEq.comm]
                        simp [hne_comm]
                simp only [h_filter_eq]
                have hp := h p
                simp only [List.any_cons] at hp
                cases hbool : (x == p) with
                | true => exact absurd (eq_of_beq hbool) (Ne.symm hpx)
                | false => simp only [hbool, Bool.false_or] at hp; exact hp
          rw [foldl_extract f S h_comm h_idem x hsx l2 hl2 hx_l2]
          exact ih _ hl1_xs hl2_filter h_any_filter _

/-- minLayer 以下の d に対し、positions 内の全要素の layer ≥ d -/
private theorem minLayer_le_layer {u : FallingUnit} {p : QuarterPos}
        (hp : p ∈ u.positions) (d : Nat) (hd : d ≤ u.minLayer) :
        d ≤ p.layer := by
    suffices h : u.minLayer ≤ p.layer by omega
    unfold FallingUnit.minLayer
    cases u with
    | cluster ps =>
        match ps, hp with
        | p' :: rest, hmem => exact foldl_min_le_mem p' rest p hmem
    | pin q =>
        simp only [FallingUnit.positions, List.mem_singleton] at hp
        subst hp
        simp [FallingUnit.positions]

/-- positions の .any 等価な FallingUnit は同じ placeFallingUnit 結果を持つ
    （dropDist が minLayer 以下であることが前提条件） -/
private theorem placeFallingUnit_ext {u1 u2 : FallingUnit}
        (h : ∀ p, u1.positions.any (· == p) = u2.positions.any (· == p))
        (s : Shape) (obs : List Layer) (d : Nat)
        (hd : d ≤ u1.minLayer) :
        placeFallingUnit s obs u1 d = placeFallingUnit s obs u2 d := by
    simp only [placeFallingUnit]
    -- step 関数の定義
    let step : List Layer → QuarterPos → List Layer := fun obs p =>
        match p.getQuarter s with
        | some q => placeQuarter obs (p.layer - d) p.dir q
        | none => obs
    -- 述語 S: d ≤ p.layer を満たす要素
    let S : QuarterPos → Prop := fun p => d ≤ p.layer
    have h_ml : u1.minLayer = u2.minLayer := minLayer_ext h
    -- l1, l2 の全要素が S を満たす
    have hl1 : ∀ y, y ∈ u1.positions → S y :=
        fun y hy => minLayer_le_layer hy d hd
    have hl2 : ∀ y, y ∈ u2.positions → S y :=
        fun y hy => minLayer_le_layer hy d (h_ml ▸ hd)
    -- step の可換性（S を満たす異なる要素間）
    have h_step_comm : ∀ p1 p2, S p1 → S p2 → p1 ≠ p2 →
            ∀ acc, step (step acc p1) p2 = step (step acc p2) p1 := by
        intro p1 p2 hs1 hs2 hne acc
        simp only [step]
        cases hgq1 : p1.getQuarter s <;> cases hgq2 : p2.getQuarter s
        · rfl
        · simp
        · simp
        · rename_i q1 q2
          -- d ≤ p.layer → p.layer - d は忠実 → 異なるセルへの書き込み
          by_cases hl : p1.layer - d = p2.layer - d
          · have hleq : p1.layer = p2.layer := by omega
            have hdeq : p1.dir ≠ p2.dir := by
                intro hd_eq
                exact hne (by cases p1; cases p2; simp_all)
            rw [hl]; exact placeQuarter_comm_dir_ne _ _ _ _ _ _ hdeq
          · exact placeQuarter_comm_layer_ne _ _ _ _ _ _ _ hl
    -- step の冪等性（S を満たす要素）
    have h_step_idem : ∀ p, S p → ∀ acc, step (step acc p) p = step acc p := by
        intro p _ acc
        simp only [step]
        cases p.getQuarter s with
        | none => rfl
        | some q => exact placeQuarter_idem _ _ _ _
    exact foldl_any_eq_of_comm_idem step S h_step_comm h_step_idem
        _ _ hl1 hl2 h _

/-- landingDistance.check は常に maxDrop 以下を返す -/
private theorem landingDistance_check_le (obs : List Layer) (positions : List QuarterPos)
        (maxDrop d fuel : Nat) (hd : d ≤ maxDrop + 1) (hf : d + fuel = maxDrop + 2) :
        landingDistance.check obs positions maxDrop d fuel ≤ maxDrop := by
    induction fuel generalizing d with
    | zero => omega
    | succ n ih =>
        simp only [landingDistance.check]
        split
        · -- d > maxDrop → maxDrop ≤ maxDrop
          omega
        · -- ¬(d > maxDrop) → d ≤ maxDrop
          split
          · -- landed → d ≤ maxDrop
            omega
          · -- ¬landed → 再帰
            exact ih (d + 1) (by omega) (by omega)

/-- landingDistance は minLayer 以下 -/
private theorem landingDistance_le_minLayer (u : FallingUnit) (obs : List Layer) :
        landingDistance u obs ≤ u.minLayer := by
    simp only [landingDistance]
    exact landingDistance_check_le obs u.positions u.minLayer 1 (u.minLayer + 1)
        (by omega) (by omega)

/-- 2つのソート済みリストの flatMap positions .any は全 p について一致する -/
private theorem settle_flatMap_any_eq (s : Shape) (p : QuarterPos) :
        ((sortFallingUnits ((floatingUnits s).map FallingUnit.rotate180)).flatMap
            FallingUnit.positions).any (· == p) =
        ((sortFallingUnits (floatingUnits s.rotate180)).flatMap
            FallingUnit.positions).any (· == p) := by
    rw [sortFallingUnits_any_positions, sortFallingUnits_any_positions,
        flatMap_map_rotate180, any_map_rotate180_beq]
    have := falling_positions_any_rotate180 s p.rotate180
    rw [QuarterPos.rotate180_rotate180] at this
    exact this

/-- positions .any BEq 等価リストペアの同一インデックスにある要素対は同じ foldl 結果を生む -/
private theorem foldl_pointwise_ext (s : Shape)
        (l1 l2 : List FallingUnit) (obs : List Layer)
        (h_len : l1.length = l2.length)
        (h_any : ∀ (i : Nat) (hi : i < l1.length) (p : QuarterPos),
            (l1[i]'hi).positions.any (· == p) =
            (l2[i]'(h_len ▸ hi)).positions.any (· == p)) :
        l1.foldl (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs =
        l2.foldl (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs := by
    induction l1 generalizing l2 obs with
    | nil =>
        cases l2 with
        | nil => rfl
        | cons _ _ => simp at h_len
    | cons u1 rest1 ih =>
        cases l2 with
        | nil => simp at h_len
        | cons u2 rest2 =>
            simp only [List.foldl_cons]
            -- u1 と u2 は .any 等価 (i=0 のケース)
            have h_any_head : ∀ p, u1.positions.any (· == p) = u2.positions.any (· == p) :=
                fun p => h_any 0 (by simp) p
            -- landingDistance が一致
            have h_ld : landingDistance u1 obs = landingDistance u2 obs :=
                landingDistance_ext h_any_head obs
            -- placeFallingUnit が一致
            have h_d_le : landingDistance u1 obs ≤ u1.minLayer :=
                landingDistance_le_minLayer u1 obs
            have h_pfu : placeFallingUnit s obs u1 (landingDistance u1 obs) =
                         placeFallingUnit s obs u2 (landingDistance u2 obs) := by
                rw [h_ld]
                exact placeFallingUnit_ext h_any_head s obs (landingDistance u2 obs)
                    (h_ld ▸ h_d_le)
            rw [h_pfu]
            -- 残りのリストに対して帰納法仮定を適用
            exact ih rest2 _ (by simpa using h_len)
                (fun i hi p => h_any (i + 1) (by simp; omega) p)

/-- getDir は setDir の異なる方角で不変 -/
private theorem getDir_setDir_ne (l : Layer) (d d' : Direction) (q : Quarter)
        (hne : d ≠ d') :
        QuarterPos.getDir (QuarterPos.setDir l d q) d' = QuarterPos.getDir l d' := by
    cases d <;> cases d' <;> simp_all [QuarterPos.setDir, QuarterPos.getDir]

/-- isOccupied は placeQuarter の異なる方角で不変 -/
private theorem isOccupied_placeQuarter_ne_dir (obs : List Layer) (lay lay' : Nat)
        (d d' : Direction) (q : Quarter) (hne : d ≠ d') :
        isOccupied (placeQuarter obs lay d q) lay' d' = isOccupied obs lay' d' := by
    show (match (placeQuarter obs lay d q)[lay']? with
          | some l => !(QuarterPos.getDir l d').isEmpty
          | none   => false) =
         (match obs[lay']? with
          | some l => !(QuarterPos.getDir l d').isEmpty
          | none   => false)
    rw [placeQuarter_getElem?_full]
    by_cases h1 : lay' < max obs.length (lay + 1)
    · simp only [if_pos h1]
      by_cases h2 : lay' = lay
      · subst h2; simp only [ite_true]
        -- ゴール: !(QuarterPos.getDir (QuarterPos.setDir (obs.getD lay' Layer.empty) d q) d').isEmpty
        --       = match obs[lay']? with | some l => !(QuarterPos.getDir l d').isEmpty | none => false
        rw [getDir_setDir_ne _ _ _ _ hne, List.getD_eq_getElem?_getD]
        cases obs[lay']? with
        | some => rfl
        | none => cases d' <;> rfl
      · simp only [if_neg h2]
        rw [List.getD_eq_getElem?_getD]
        cases obs[lay']? with
        | some => rfl
        | none => cases d' <;> rfl
    · simp only [if_neg h1]
      have hge : obs.length ≤ lay' := by omega
      rw [List.getElem?_eq_none_iff.mpr hge]

/-- isOccupied は placeFallingUnit の、positions と方角が素な場合に不変 -/
private theorem isOccupied_placeFallingUnit_ne_dir (s : Shape) (obs : List Layer)
        (u : FallingUnit) (d : Nat) (lay : Nat) (dir : Direction)
        (h_no_dir : u.positions.any (fun p => p.dir == dir) = false) :
        isOccupied (placeFallingUnit s obs u d) lay dir = isOccupied obs lay dir := by
    unfold placeFallingUnit
    suffices h : ∀ (ps : List QuarterPos) (acc : List Layer),
        ps.any (fun p => p.dir == dir) = false →
        isOccupied (ps.foldl (fun obs p =>
            match p.getQuarter s with
            | some q => placeQuarter obs (p.layer - d) p.dir q
            | none => obs) acc) lay dir = isOccupied acc lay dir by
      exact h u.positions obs h_no_dir
    intro ps
    induction ps with
    | nil => intro _ _; rfl
    | cons p rest ih =>
      intro acc hany
      simp only [List.any_cons] at hany
      have hne : p.dir ≠ dir := by
        intro heq; simp [heq] at hany
      have hrest : rest.any (fun p => p.dir == dir) = false := by
        cases hp : (p.dir == dir) with
        | false => simpa [hp] using hany
        | true => exact absurd (beq_iff_eq.mp hp) hne
      simp only [List.foldl_cons]
      rw [ih _ hrest]
      split
      · next q _ =>
        exact isOccupied_placeQuarter_ne_dir acc _ lay p.dir dir q hne
      · rfl

/-- 着地判定は placeFallingUnit の方角素なユニットで不変 -/
private theorem landed_placeFallingUnit_ne_dir (s : Shape) (obs : List Layer)
        (u : FallingUnit) (drop : Nat) (positions : List QuarterPos) (d : Nat)
        (h_no_dir : ∀ p, p ∈ positions → u.positions.any (fun q => q.dir == p.dir) = false) :
        positions.any (fun p =>
            let newLayer := p.layer - d
            newLayer == 0 || isOccupied (placeFallingUnit s obs u drop) (newLayer - 1) p.dir) =
        positions.any (fun p =>
            let newLayer := p.layer - d
            newLayer == 0 || isOccupied obs (newLayer - 1) p.dir) := by
    induction positions with
    | nil => rfl
    | cons p rest ih =>
        simp only [List.any_cons]
        rw [ih (fun q hq => h_no_dir q (.tail p hq))]
        congr 1
        have h_p := h_no_dir p (.head rest)
        congr 1
        exact isOccupied_placeFallingUnit_ne_dir s obs u drop _ _ h_p

/-- landingDistance.check は方角素な placeFallingUnit で不変 -/
private theorem landingDistance_check_placeFallingUnit_ne_dir (s : Shape) (obs : List Layer)
        (u : FallingUnit) (drop : Nat) (positions : List QuarterPos)
        (maxDrop d fuel : Nat)
        (h_no_dir : ∀ p, p ∈ positions → u.positions.any (fun q => q.dir == p.dir) = false) :
        landingDistance.check (placeFallingUnit s obs u drop) positions maxDrop d fuel =
        landingDistance.check obs positions maxDrop d fuel := by
    induction fuel generalizing d with
    | zero => rfl
    | succ n ih =>
        simp only [landingDistance.check]
        split
        · rfl
        · rw [landed_placeFallingUnit_ne_dir s obs u drop positions d h_no_dir]
          split
          · rfl
          · exact ih (d + 1)

/-- landingDistance は方角素な placeFallingUnit で不変 -/
private theorem landingDistance_placeFallingUnit_ne_dir (s : Shape) (obs : List Layer)
        (u v : FallingUnit) (d : Nat)
        (h_no_dir : ∀ p, p ∈ v.positions →
            u.positions.any (fun q => q.dir == p.dir) = false) :
        landingDistance v (placeFallingUnit s obs u d) = landingDistance v obs := by
    simp only [landingDistance]
    exact landingDistance_check_placeFallingUnit_ne_dir s obs u d v.positions
        v.minLayer 1 (v.minLayer + 1) h_no_dir

/-- placeQuarter は方角が異なれば（任意のレイヤで）可換 -/
private theorem placeQuarter_comm_of_dir_ne (obs : List Layer)
        (lay1 lay2 : Nat) (d1 d2 : Direction) (q1 q2 : Quarter)
        (hne : d1 ≠ d2) :
        placeQuarter (placeQuarter obs lay1 d1 q1) lay2 d2 q2 =
        placeQuarter (placeQuarter obs lay2 d2 q2) lay1 d1 q1 := by
    by_cases hl : lay1 = lay2
    · subst hl; exact placeQuarter_comm_dir_ne obs lay1 d1 d2 q1 q2 hne
    · exact placeQuarter_comm_layer_ne obs lay1 lay2 d1 d2 q1 q2 hl

/-- 単一 placeQuarter は方角素な foldl-step 列を通過する -/
private theorem foldl_placeQuarter_comm_ne_dir (s : Shape)
        (ups : List QuarterPos) (drop : Nat) (acc : List Layer)
        (lay : Nat) (d : Direction) (q : Quarter)
        (h_ne : ∀ r, r ∈ ups → r.dir ≠ d) :
        ups.foldl (fun obs r =>
            match r.getQuarter s with
            | some q' => placeQuarter obs (r.layer - drop) r.dir q'
            | none => obs
        ) (placeQuarter acc lay d q) =
        placeQuarter (ups.foldl (fun obs r =>
            match r.getQuarter s with
            | some q' => placeQuarter obs (r.layer - drop) r.dir q'
            | none => obs
        ) acc) lay d q := by
    induction ups generalizing acc with
    | nil => rfl
    | cons r rest ih =>
        simp only [List.foldl_cons]
        have hr_ne : r.dir ≠ d := h_ne r (.head rest)
        have hrest : ∀ r', r' ∈ rest → r'.dir ≠ d :=
            fun r' hr' => h_ne r' (.tail r hr')
        -- r.getQuarter s で場合分け
        match hgq : QuarterPos.getQuarter s r with
        | some q' =>
            -- placeQuarter の可換性で通過
            simp only [placeQuarter_comm_of_dir_ne acc lay (r.layer - drop)
                d r.dir q q' (Ne.symm hr_ne)]
            exact ih (placeQuarter acc (r.layer - drop) r.dir q') hrest
        | none =>
            exact ih acc hrest

/-- 方角素なリストの foldl-step は可換 -/
private theorem foldl_comm_ne_dir (s : Shape)
        (ups vps : List QuarterPos) (du dv : Nat) (obs : List Layer)
        (h_vu : ∀ p, p ∈ vps →
            ups.any (fun q => q.dir == p.dir) = false) :
        vps.foldl (fun obs p =>
            match p.getQuarter s with
            | some q => placeQuarter obs (p.layer - dv) p.dir q
            | none => obs)
          (ups.foldl (fun obs p =>
            match p.getQuarter s with
            | some q => placeQuarter obs (p.layer - du) p.dir q
            | none => obs) obs) =
        ups.foldl (fun obs p =>
            match p.getQuarter s with
            | some q => placeQuarter obs (p.layer - du) p.dir q
            | none => obs)
          (vps.foldl (fun obs p =>
            match p.getQuarter s with
            | some q => placeQuarter obs (p.layer - dv) p.dir q
            | none => obs) obs) := by
    induction vps generalizing obs with
    | nil => rfl
    | cons p rest ih =>
        dsimp only [List.foldl_cons]
        -- p の方角は ups の全要素と異なる
        have hp : ups.any (fun q => q.dir == p.dir) = false :=
            h_vu p (.head rest)
        have hrest : ∀ q, q ∈ rest →
            ups.any (fun r => r.dir == q.dir) = false :=
            fun q hq => h_vu q (.tail p hq)
        -- ups 内の全要素 r について r.dir ≠ p.dir を導出
        have h_ne : ∀ r, r ∈ ups → r.dir ≠ p.dir := by
            intro r hr heq
            have : ups.any (fun q => q.dir == p.dir) = true :=
                List.any_eq_true.mpr ⟨r, hr, by simp [heq]⟩
            simp_all
        -- p.getQuarter s で場合分け
        match hgq : QuarterPos.getQuarter s p with
        | some q' =>
            -- placeQuarter を ups.foldl の内側に通す
            -- NOTE: simp only [hgq] は linter 上は unused だが rw のために必要
            set_option linter.unusedSimpArgs false in
            simp only [hgq]
            rw [← foldl_placeQuarter_comm_ne_dir s ups du obs
                (p.layer - dv) p.dir q' h_ne]
            exact ih (placeQuarter obs (p.layer - dv) p.dir q') hrest
        | none =>
            -- none ケースは恒等変換なので IH をそのまま適用
            set_option linter.unusedSimpArgs false in
            simp only [hgq]
            exact ih obs hrest

/-- placeFallingUnit は方角素なユニットペアで可換 -/
private theorem placeFallingUnit_comm_ne_dir (s : Shape) (obs : List Layer)
        (u v : FallingUnit) (du dv : Nat)
        (_h_uv : ∀ p, p ∈ u.positions →
            v.positions.any (fun q => q.dir == p.dir) = false)
        (h_vu : ∀ p, p ∈ v.positions →
            u.positions.any (fun q => q.dir == p.dir) = false) :
        placeFallingUnit s (placeFallingUnit s obs u du) v dv =
        placeFallingUnit s (placeFallingUnit s obs v dv) u du := by
    simp only [placeFallingUnit]
    exact foldl_comm_ne_dir s u.positions v.positions du dv obs h_vu

/-- 方角素なユニットの settle step は可換 -/
private theorem settleStep_comm_ne_dir (s : Shape) (obs : List Layer)
        (u v : FallingUnit)
        (h_uv : ∀ p, p ∈ u.positions →
            v.positions.any (fun q => q.dir == p.dir) = false)
        (h_vu : ∀ p, p ∈ v.positions →
            u.positions.any (fun q => q.dir == p.dir) = false) :
        placeFallingUnit s
            (placeFallingUnit s obs u (landingDistance u obs))
            v (landingDistance v (placeFallingUnit s obs u (landingDistance u obs))) =
        placeFallingUnit s
            (placeFallingUnit s obs v (landingDistance v obs))
            u (landingDistance u (placeFallingUnit s obs v (landingDistance v obs))) := by
    -- landingDistance は方角素な placeFallingUnit で不変
    rw [landingDistance_placeFallingUnit_ne_dir s obs u v (landingDistance u obs) h_vu]
    rw [landingDistance_placeFallingUnit_ne_dir s obs v u (landingDistance v obs) h_uv]
    -- placeFallingUnit は方角素なペアで可換
    exact placeFallingUnit_comm_ne_dir s obs u v
        (landingDistance u obs) (landingDistance v obs) h_uv h_vu

-- ============================================================
-- tied 要素の方角非共有性と foldl 可換性
-- ============================================================

/-- foldl-min-option の補助関数（定義の一致問題を回避するため独立定義） -/
private def foldMinOption : Option Nat → Nat → Option Nat :=
    fun acc l => some (match acc with | some a => min a l | none => l)

/-- foldMinOption (some init) rest = some v → v = init ∨ v ∈ rest -/
private theorem foldMinOption_some_mem (rest : List Nat) (init v : Nat)
        (h : rest.foldl foldMinOption (some init) = some v) :
        v = init ∨ v ∈ rest := by
    induction rest generalizing init with
    | nil => simp [List.foldl] at h; exact .inl h.symm
    | cons b tail ih =>
        simp only [List.foldl_cons, foldMinOption] at h
        cases ih (min init b) h with
        | inl heq =>
            cases Nat.le_total init b with
            | inl hle => rw [Nat.min_eq_left hle] at heq; exact .inl heq
            | inr hle => rw [Nat.min_eq_right hle] at heq; exact .inr (heq ▸ .head tail)
        | inr hmem => exact .inr (.tail b hmem)

/-- foldMinOption none layers = some v → v ∈ layers -/
private theorem foldMinOption_none_mem (layers : List Nat) (v : Nat)
        (h : layers.foldl foldMinOption none = some v) :
        v ∈ layers := by
    cases layers with
    | nil => simp [List.foldl] at h
    | cons a rest =>
        simp only [List.foldl_cons, foldMinOption] at h
        cases foldMinOption_some_mem rest a v h with
        | inl heq => exact heq ▸ .head rest
        | inr hmem => exact .tail a hmem

/-- foldMinOption (some init) rest は常に some を返す -/
private theorem foldMinOption_some_isSome (rest : List Nat) (init : Nat) :
        ∃ v, rest.foldl foldMinOption (some init) = some v := by
    induction rest generalizing init with
    | nil => exact ⟨init, rfl⟩
    | cons y ys ih => simp only [List.foldl_cons, foldMinOption]; exact ih (min init y)

/-- foldMinOption (some init) rest = some v → v ≤ init -/
private theorem foldMinOption_some_le_init (rest : List Nat) (init v : Nat)
        (h : rest.foldl foldMinOption (some init) = some v) :
        v ≤ init := by
    induction rest generalizing init with
    | nil =>
        simp only [List.foldl, Option.some.injEq] at h
        omega
    | cons y ys ih =>
        simp only [List.foldl_cons, foldMinOption] at h
        exact Nat.le_trans (ih (min init y) h) (Nat.min_le_left init y)

/-- foldMinOption (some init) rest = some v → 任意の m ∈ rest に対して v ≤ m -/
private theorem foldMinOption_some_le_mem (rest : List Nat) (init v : Nat)
        (h : rest.foldl foldMinOption (some init) = some v) (m : Nat) (hm : m ∈ rest) :
        v ≤ m := by
    induction rest generalizing init with
    | nil => nomatch hm
    | cons y ys ih =>
        simp only [List.foldl_cons, foldMinOption] at h
        cases hm with
        | head _ =>
            exact Nat.le_trans (foldMinOption_some_le_init ys (min init m) v h)
                (Nat.min_le_right init m)
        | tail _ hm_ys =>
            exact ih (min init y) h hm_ys

/-- foldMinOption none layers = some v → 任意の m ∈ layers に対して v ≤ m -/
private theorem foldMinOption_none_le (layers : List Nat) (v : Nat)
        (h : layers.foldl foldMinOption none = some v) (m : Nat) (hm : m ∈ layers) :
        v ≤ m := by
    cases layers with
    | nil => nomatch hm
    | cons y ys =>
        simp only [List.foldl_cons, foldMinOption] at h
        cases hm with
        | head _ => exact foldMinOption_some_le_init ys m v h
        | tail _ hm_ys => exact foldMinOption_some_le_mem ys y v h m hm_ys

/-- minLayerAtDir が some を返すなら、その方角・レイヤの位置が実在する -/
private theorem minLayerAtDir_some_witness (u : FallingUnit) (dir : Direction) (l : Nat)
        (h : u.minLayerAtDir dir = some l) :
        ∃ p, p ∈ u.positions ∧ p.dir = dir ∧ p.layer = l := by
    simp only [FallingUnit.minLayerAtDir] at h
    change (u.positions.filterMap fun p =>
        if p.dir == dir then some p.layer else none).foldl foldMinOption none = some l at h
    have h_layers := foldMinOption_none_mem _ l h
    rw [List.mem_filterMap] at h_layers
    obtain ⟨p, hp_mem, hp_eq⟩ := h_layers
    by_cases hd : (p.dir == dir) = true
    · simp only [hd, ite_true] at hp_eq
      exact ⟨p, hp_mem, eq_of_beq hd, Option.some.inj hp_eq⟩
    · simp only [hd, ite_false, reduceCtorEq] at hp_eq

/-- 指定方角の位置が存在するなら minLayerAtDir は some -/
private theorem minLayerAtDir_some_of_mem (u : FallingUnit) (dir : Direction) (p : QuarterPos)
        (hp : p ∈ u.positions) (hd : p.dir = dir) :
        ∃ l, u.minLayerAtDir dir = some l := by
    simp only [FallingUnit.minLayerAtDir]
    change ∃ l, (u.positions.filterMap fun q =>
        if q.dir == dir then some q.layer else none).foldl foldMinOption none = some l
    have h_ne : (u.positions.filterMap fun q =>
            if q.dir == dir then some q.layer else none) ≠ [] := by
        intro h_empty
        have : p.layer ∈ (u.positions.filterMap fun q =>
                if q.dir == dir then some q.layer else none) :=
            List.mem_filterMap.mpr ⟨p, hp, by simp [hd]⟩
        rw [h_empty] at this; exact absurd this List.not_mem_nil
    -- 非空リスト: 先頭を取得して foldl が some を返すことを示す
    have ⟨a, rest, hl⟩ : ∃ a rest, (u.positions.filterMap fun q =>
            if q.dir == dir then some q.layer else none) = a :: rest := by
        cases h_list : (u.positions.filterMap fun q =>
            if q.dir == dir then some q.layer else none) with
        | nil => exact absurd h_list h_ne
        | cons a rest => exact ⟨a, rest, rfl⟩
    rw [hl]
    simp only [List.foldl_cons]
    change ∃ l, rest.foldl foldMinOption (foldMinOption none a) = some l
    simp only [foldMinOption]
    exact foldMinOption_some_isSome rest a

/-- shouldProcessBefore u v = false のとき、共有方角の minLayerAtDir で u ≥ v -/
private theorem spb_false_minLayerAtDir_ge (u v : FallingUnit) (dir : Direction)
        (h : shouldProcessBefore u v = false)
        (lu lv : Nat)
        (hu : u.minLayerAtDir dir = some lu)
        (hv : v.minLayerAtDir dir = some lv) :
        lu ≥ lv := by
    -- shouldProcessBefore u v = false → Direction.all.any (fun dir => ...) = false
    -- 展開して dir ケース分析
    simp only [shouldProcessBefore, Direction.all, List.any_cons, List.any_nil, Bool.or_false] at h
    -- h は4方角の or = false。各方角でケース分け。
    rcases dir with _ | _ | _ | _ <;> simp_all [FallingUnit.minLayerAtDir]

/-- shouldProcessBefore 双方向 false + 位置非共有 → 方角列非共有
    （tied 要素は列を共有しない） -/
private theorem tied_no_shared_dir (u v : FallingUnit)
        (h_tied_uv : shouldProcessBefore u v = false)
        (h_tied_vu : shouldProcessBefore v u = false)
        (h_disj : ∀ p, p ∈ u.positions → v.positions.any (· == p) = false) :
        ∀ p, p ∈ u.positions → v.positions.any (fun q => q.dir == p.dir) = false := by
    intro p hp
    -- v.positions.any (dir == p.dir) が true だと仮定して矛盾を導く
    -- Bool は Decidable なので cases で分場合分け
    cases h_any : v.positions.any (fun q => q.dir == p.dir) with
    | false => rfl
    | true =>
        -- v に p.dir を持つ位置 q が存在する
        obtain ⟨q, hq_mem, hq_dir⟩ := List.any_eq_true.mp h_any
        have hd : q.dir = p.dir := eq_of_beq hq_dir
        -- minLayerAtDir が some であることを示す
        obtain ⟨lu, hlu⟩ := minLayerAtDir_some_of_mem u p.dir p hp rfl
        obtain ⟨lv, hlv⟩ := minLayerAtDir_some_of_mem v p.dir q hq_mem hd
        -- shouldProcessBefore 双方 false → lu ≥ lv ∧ lv ≥ lu → lu = lv
        have h_ge := spb_false_minLayerAtDir_ge u v p.dir h_tied_uv lu lv hlu hlv
        have h_le := spb_false_minLayerAtDir_ge v u p.dir h_tied_vu lv lu hlv hlu
        have h_eq : lu = lv := by omega
        -- minLayerAtDir_some_witness: v に (lv, p.dir) の位置が存在
        obtain ⟨q', hq'_mem, hq'_dir, hq'_layer⟩ := minLayerAtDir_some_witness v p.dir lv hlv
        -- u に (lu, p.dir) の位置が存在
        obtain ⟨p', hp'_mem, hp'_dir, hp'_layer⟩ := minLayerAtDir_some_witness u p.dir lu hlu
        -- p' と q' は同じ (layer, dir) → q' = p'
        have h_qp : q' = p' := by
            have hl : q'.layer = p'.layer := by rw [hq'_layer, hp'_layer, h_eq]
            have hd' : q'.dir = p'.dir := by rw [hq'_dir, hp'_dir]
            exact match q', p', hl, hd' with
            | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl
        -- h_disj p' hp'_mem : v.positions.any (· == p') = false
        have h_p'_disj := h_disj p' hp'_mem
        -- だが q' ∈ v.positions で q' = p' → v.positions.any (· == p') = true
        have : v.positions.any (· == p') = true := by
            apply List.any_eq_true.mpr
            exact ⟨q', hq'_mem, h_qp ▸ beq_self_eq_true q'⟩
        rw [this] at h_p'_disj
        exact absurd h_p'_disj (by decide)

/-- tied + 位置非共有の逆方向版 -/
private theorem tied_no_shared_dir_rev (u v : FallingUnit)
        (h_tied_uv : shouldProcessBefore u v = false)
        (h_tied_vu : shouldProcessBefore v u = false)
        (h_disj : ∀ p, p ∈ v.positions → u.positions.any (· == p) = false) :
        ∀ p, p ∈ v.positions → u.positions.any (fun q => q.dir == p.dir) = false :=
    tied_no_shared_dir v u h_tied_vu h_tied_uv h_disj

/-- 先頭 2 要素が方角素なら foldl 結果はスワップで不変 -/
private theorem foldl_settle_head_swap (s : Shape) (u v : FallingUnit)
        (rest : List FallingUnit) (obs : List Layer)
        (h_uv : ∀ p, p ∈ u.positions → v.positions.any (fun q => q.dir == p.dir) = false)
        (h_vu : ∀ p, p ∈ v.positions → u.positions.any (fun q => q.dir == p.dir) = false) :
        (u :: v :: rest).foldl (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs =
        (v :: u :: rest).foldl (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs := by
    simp only [List.foldl_cons]
    congr 1
    exact settleStep_comm_ne_dir s obs u v h_uv h_vu

-- ============================================================
-- positions .any 拡張性（ext）補題群
-- ============================================================

/-- minLayerAtDir は positions .any にのみ依存する -/
private theorem minLayerAtDir_ext {u1 u2 : FallingUnit}
        (h : ∀ p, u1.positions.any (· == p) = u2.positions.any (· == p))
        (dir : Direction) :
        u1.minLayerAtDir dir = u2.minLayerAtDir dir := by
    cases h1 : u1.minLayerAtDir dir with
    | none =>
        -- u1 に dir 方角の位置がない → u2 にもない
        cases h2 : u2.minLayerAtDir dir with
        | none => rfl
        | some l2 =>
            exfalso
            obtain ⟨p2, hp2_mem, hp2_dir, _⟩ := minLayerAtDir_some_witness u2 dir l2 h2
            -- p2 ∈ u2.positions → p2 ∈ u1.positions (by .any 等価)
            have hp2_in_u1 : p2 ∈ u1.positions :=
                mem_of_any_beq_eq h hp2_mem
            -- u1 に dir を持つ位置が存在 → minLayerAtDir ≠ none
            obtain ⟨l, hl⟩ := minLayerAtDir_some_of_mem u1 dir p2 hp2_in_u1 hp2_dir
            rw [hl] at h1; exact absurd h1 (by simp [reduceCtorEq])
    | some l1 =>
        cases h2 : u2.minLayerAtDir dir with
        | none =>
            exfalso
            obtain ⟨p1, hp1_mem, hp1_dir, _⟩ := minLayerAtDir_some_witness u1 dir l1 h1
            have hp1_in_u2 : p1 ∈ u2.positions :=
                mem_of_any_beq_eq (fun p => (h p).symm) hp1_mem
            obtain ⟨l, hl⟩ := minLayerAtDir_some_of_mem u2 dir p1 hp1_in_u2 hp1_dir
            rw [hl] at h2; exact absurd h2 (by simp [reduceCtorEq])
        | some l2 =>
            -- 両方 some → l1 = l2
            congr 1
            apply Nat.le_antisymm
            · -- l1 ≤ l2: l2 の witness p2 が u1 にも属し、l1 ≤ p2.layer
              obtain ⟨p2, hp2_mem, hp2_dir, hp2_layer⟩ :=
                  minLayerAtDir_some_witness u2 dir l2 h2
              have hp2_in_u1 : p2 ∈ u1.positions :=
                  mem_of_any_beq_eq h hp2_mem
              -- minLayerAtDir は dir フィルタ後の最小値 → l1 ≤ p2.layer
              -- p2 ∈ u1.positions ∧ p2.dir = dir → u1.minLayerAtDir dir ≤ p2.layer
              simp only [FallingUnit.minLayerAtDir] at h1
              change (u1.positions.filterMap fun p =>
                  if p.dir == dir then some p.layer else none).foldl
                  foldMinOption none = some l1 at h1
              have : p2.layer ∈ (u1.positions.filterMap fun p =>
                  if p.dir == dir then some p.layer else none) := by
                  rw [List.mem_filterMap]
                  exact ⟨p2, hp2_in_u1, by simp [show (p2.dir == dir) = true from by
                      rw [hp2_dir]; exact BEq.rfl]⟩
              rw [← hp2_layer]
              exact foldMinOption_none_le _ l1 h1 p2.layer this
            · obtain ⟨p1, hp1_mem, hp1_dir, hp1_layer⟩ :=
                  minLayerAtDir_some_witness u1 dir l1 h1
              have hp1_in_u2 : p1 ∈ u2.positions :=
                  mem_of_any_beq_eq (fun p => (h p).symm) hp1_mem
              simp only [FallingUnit.minLayerAtDir] at h2
              change (u2.positions.filterMap fun p =>
                  if p.dir == dir then some p.layer else none).foldl
                  foldMinOption none = some l2 at h2
              have : p1.layer ∈ (u2.positions.filterMap fun p =>
                  if p.dir == dir then some p.layer else none) := by
                  rw [List.mem_filterMap]
                  exact ⟨p1, hp1_in_u2, by simp [show (p1.dir == dir) = true from by
                      rw [hp1_dir]; exact BEq.rfl]⟩
              rw [← hp1_layer]
              exact foldMinOption_none_le _ l2 h2 p1.layer this

/-- shouldProcessBefore は positions .any にのみ依存する -/
private theorem shouldProcessBefore_ext {u1 u2 v1 v2 : FallingUnit}
        (hu : ∀ p, u1.positions.any (· == p) = u2.positions.any (· == p))
        (hv : ∀ p, v1.positions.any (· == p) = v2.positions.any (· == p)) :
        shouldProcessBefore u1 v1 = shouldProcessBefore u2 v2 := by
    simp only [shouldProcessBefore]
    congr 1
    funext dir
    rw [minLayerAtDir_ext hu dir, minLayerAtDir_ext hv dir]

/-- tiebreaker は positions .any にのみ依存する -/
private theorem tiebreaker_ext {u1 u2 : FallingUnit}
        (h : ∀ p, u1.positions.any (· == p) = u2.positions.any (· == p)) :
        u1.tiebreaker = u2.tiebreaker := by
    simp only [FallingUnit.tiebreaker, Direction.all, List.foldl]
    rw [minLayerAtDir_ext h .ne, minLayerAtDir_ext h .se,
        minLayerAtDir_ext h .sw, minLayerAtDir_ext h .nw]

-- ============================================================
-- insertSorted / sortFallingUnits の pointwise .any 等価保存
-- ============================================================

/-- insertSorted の結果の長さ -/
private theorem insertSorted_length (u : FallingUnit) (sorted : List FallingUnit) (fuel : Nat) :
        (insertSorted u sorted fuel).length = sorted.length + 1 := by
    induction fuel generalizing sorted with
    | zero => simp [insertSorted]
    | succ n ih =>
        cases sorted with
        | nil => simp [insertSorted]
        | cons v rest =>
            simp only [insertSorted]
            split
            · simp
            · split
              · simp [ih rest]
              · split
                · simp
                · simp [ih rest]

/-- sortFallingUnits の結果の長さ -/
private theorem sortFallingUnits_length (units : List FallingUnit) :
        (sortFallingUnits units).length = units.length := by
    exact (sortFallingUnits_perm units).length_eq

/-- positions .any 等価な要素を pointwise .any 等価なソート済みリストに挿入すると、
    結果も pointwise .any 等価になる -/
private theorem insertSorted_pointwise_ext
        {u1 u2 : FallingUnit}
        (hu : ∀ p, u1.positions.any (· == p) = u2.positions.any (· == p))
        {sorted1 sorted2 : List FallingUnit}
        (h_len : sorted1.length = sorted2.length)
        (h_pw : ∀ (i : Nat) (hi : i < sorted1.length) (p : QuarterPos),
            (sorted1[i]'hi).positions.any (· == p) =
            (sorted2[i]'(h_len ▸ hi)).positions.any (· == p))
        (fuel : Nat) :
        (insertSorted u1 sorted1 fuel).length = (insertSorted u2 sorted2 fuel).length ∧
        ∀ (i : Nat) (hi : i < (insertSorted u1 sorted1 fuel).length) (p : QuarterPos),
            ((insertSorted u1 sorted1 fuel)[i]'hi).positions.any (· == p) =
            ((insertSorted u2 sorted2 fuel)[i]'(by
                rw [insertSorted_length] at hi ⊢
                rw [h_len] at hi; exact hi)).positions.any (· == p) := by
    induction fuel generalizing sorted1 sorted2 with
    | zero =>
        -- fuel = 0: insertSorted u sorted 0 = u :: sorted
        simp only [insertSorted]
        constructor
        · simp [h_len]
        · intro i hi p
          cases i with
          | zero => exact hu p
          | succ j => exact h_pw j (by simp at hi; omega) p
    | succ n ih =>
        cases sorted1 with
        | nil =>
            -- sorted1 = [] → sorted2 = []
            have : sorted2 = [] := by
                cases sorted2 with
                | nil => rfl
                | cons _ _ => simp at h_len
            subst this
            simp only [insertSorted]
            exact ⟨rfl, fun i hi p => by cases i with | zero => exact hu p | succ j => simp at hi⟩
        | cons v1 rest1 =>
            -- sorted1 = v1 :: rest1 → sorted2 = v2 :: rest2
            cases sorted2 with
            | nil => simp at h_len
            | cons v2 rest2 =>
                -- v1 と v2 は .any 等価 (i=0)
                have h_v : ∀ p, v1.positions.any (· == p) = v2.positions.any (· == p) :=
                    fun p => h_pw 0 (by simp) p
                -- rest1 と rest2 は pointwise .any 等価
                have h_rest_len : rest1.length = rest2.length := by simp at h_len; exact h_len
                have h_rest_pw : ∀ (i : Nat) (hi : i < rest1.length) (p : QuarterPos),
                        (rest1[i]'hi).positions.any (· == p) =
                        (rest2[i]'(h_rest_len ▸ hi)).positions.any (· == p) :=
                    fun i hi p => h_pw (i + 1) (by simp; omega) p
                -- shouldProcessBefore の等価性
                have h_spb_uv : shouldProcessBefore u1 v1 = shouldProcessBefore u2 v2 :=
                    shouldProcessBefore_ext hu h_v
                have h_spb_vu : shouldProcessBefore v1 u1 = shouldProcessBefore v2 u2 :=
                    shouldProcessBefore_ext h_v hu
                -- tiebreaker の等価性
                have h_tie : u1.tiebreaker = u2.tiebreaker :=
                    tiebreaker_ext hu
                have h_tie_v : v1.tiebreaker = v2.tiebreaker :=
                    tiebreaker_ext h_v
                -- 条件分岐: by_cases で分岐
                by_cases h1 : shouldProcessBefore u1 v1
                · -- spb u1 v1 = true → spb u2 v2 = true
                  have h1' : shouldProcessBefore u2 v2 = true := h_spb_uv ▸ h1
                  have lhs : insertSorted u1 (v1 :: rest1) (n + 1) = u1 :: v1 :: rest1 := by
                      show (if shouldProcessBefore u1 v1 then u1 :: v1 :: rest1
                          else if shouldProcessBefore v1 u1 then v1 :: insertSorted u1 rest1 n
                          else if u1.tiebreaker ≤ v1.tiebreaker then u1 :: v1 :: rest1
                          else v1 :: insertSorted u1 rest1 n) = _
                      simp [h1]
                  have rhs : insertSorted u2 (v2 :: rest2) (n + 1) = u2 :: v2 :: rest2 := by
                      show (if shouldProcessBefore u2 v2 then u2 :: v2 :: rest2
                          else _) = _
                      simp [h1']
                  simp only [lhs, rhs]
                  constructor
                  · simp [h_len]
                  · intro i hi p
                    cases i with
                    | zero => exact hu p
                    | succ j =>
                        cases j with
                        | zero => exact h_v p
                        | succ k =>
                            simp only [List.getElem_cons_succ]
                            exact h_pw (k + 1) (by simp at hi ⊢; omega) p
                · -- spb u1 v1 = false
                  simp only [Bool.not_eq_true] at h1
                  have h1' : shouldProcessBefore u2 v2 = false := h_spb_uv ▸ h1
                  by_cases h2 : shouldProcessBefore v1 u1
                  · -- spb v u = true
                    have h2' : shouldProcessBefore v2 u2 = true := h_spb_vu ▸ h2
                    have lhs : insertSorted u1 (v1 :: rest1) (n + 1) =
                        v1 :: insertSorted u1 rest1 n := by
                        show (if shouldProcessBefore u1 v1 then u1 :: v1 :: rest1
                            else if shouldProcessBefore v1 u1 then v1 :: insertSorted u1 rest1 n
                            else if u1.tiebreaker ≤ v1.tiebreaker then u1 :: v1 :: rest1
                            else v1 :: insertSorted u1 rest1 n) = _
                        simp [h1, h2]
                    have rhs : insertSorted u2 (v2 :: rest2) (n + 1) =
                        v2 :: insertSorted u2 rest2 n := by
                        show (if shouldProcessBefore u2 v2 then _
                            else if shouldProcessBefore v2 u2 then v2 :: insertSorted u2 rest2 n
                            else _) = _
                        simp [h1', h2']
                    simp only [lhs, rhs]
                    have ih_result := ih h_rest_len h_rest_pw
                    constructor
                    · simp [ih_result.1]
                    · intro i hi p
                      cases i with
                      | zero => exact h_v p
                      | succ j => exact ih_result.2 j (by simp at hi; exact hi) p
                  · -- tied
                    simp only [Bool.not_eq_true] at h2
                    have h2' : shouldProcessBefore v2 u2 = false := h_spb_vu ▸ h2
                    by_cases h3 : u1.tiebreaker ≤ v1.tiebreaker
                    · -- u.tiebreaker ≤ v.tiebreaker
                      have h3' : u2.tiebreaker ≤ v2.tiebreaker := by omega
                      have lhs : insertSorted u1 (v1 :: rest1) (n + 1) =
                          u1 :: v1 :: rest1 := by
                          show (if shouldProcessBefore u1 v1 then u1 :: v1 :: rest1
                              else if shouldProcessBefore v1 u1 then v1 :: insertSorted u1 rest1 n
                              else if u1.tiebreaker ≤ v1.tiebreaker then u1 :: v1 :: rest1
                              else v1 :: insertSorted u1 rest1 n) = _
                          simp [h1, h2, h3]
                      have rhs : insertSorted u2 (v2 :: rest2) (n + 1) =
                          u2 :: v2 :: rest2 := by
                          show (if shouldProcessBefore u2 v2 then _
                              else if shouldProcessBefore v2 u2 then _
                              else if u2.tiebreaker ≤ v2.tiebreaker then u2 :: v2 :: rest2
                              else _) = _
                          simp [h1', h2', h3']
                      simp only [lhs, rhs]
                      constructor
                      · simp [h_len]
                      · intro i hi p
                        cases i with
                        | zero => exact hu p
                        | succ j =>
                            cases j with
                            | zero => exact h_v p
                            | succ k =>
                                simp only [List.getElem_cons_succ]
                                exact h_pw (k + 1) (by simp at hi ⊢; omega) p
                    · -- u.tiebreaker > v.tiebreaker
                      have h3' : ¬(u2.tiebreaker ≤ v2.tiebreaker) := by omega
                      have lhs : insertSorted u1 (v1 :: rest1) (n + 1) =
                          v1 :: insertSorted u1 rest1 n := by
                          show (if shouldProcessBefore u1 v1 then u1 :: v1 :: rest1
                              else if shouldProcessBefore v1 u1 then v1 :: insertSorted u1 rest1 n
                              else if u1.tiebreaker ≤ v1.tiebreaker then u1 :: v1 :: rest1
                              else v1 :: insertSorted u1 rest1 n) = _
                          simp [h1, h2, h3]
                      have rhs : insertSorted u2 (v2 :: rest2) (n + 1) =
                          v2 :: insertSorted u2 rest2 n := by
                          show (if shouldProcessBefore u2 v2 then _
                              else if shouldProcessBefore v2 u2 then _
                              else if u2.tiebreaker ≤ v2.tiebreaker then _
                              else v2 :: insertSorted u2 rest2 n) = _
                          simp [h1', h2', h3']
                      simp only [lhs, rhs]
                      have ih_result := ih h_rest_len h_rest_pw
                      constructor
                      · simp [ih_result.1]
                      · intro i hi p
                        cases i with
                        | zero => exact h_v p
                        | succ j => exact ih_result.2 j (by simp at hi; exact hi) p

/-- sortFallingUnits は pointwise .any 等価な入力に対して pointwise .any 等価な出力を生む -/
private theorem sortFallingUnits_pointwise_ext
        {l1 l2 : List FallingUnit}
        (h_len : l1.length = l2.length)
        (h_pw : ∀ (i : Nat) (hi : i < l1.length) (p : QuarterPos),
            (l1[i]'hi).positions.any (· == p) =
            (l2[i]'(h_len ▸ hi)).positions.any (· == p)) :
        (sortFallingUnits l1).length = (sortFallingUnits l2).length ∧
        ∀ (i : Nat) (hi : i < (sortFallingUnits l1).length) (p : QuarterPos),
            ((sortFallingUnits l1)[i]'hi).positions.any (· == p) =
            ((sortFallingUnits l2)[i]'(by
                rw [sortFallingUnits_length] at hi ⊢
                rw [h_len] at hi; exact hi)).positions.any (· == p) := by
    -- foldl の帰納法で pointwise 等価を保存する補助定理
    -- sortFU = foldl (fun sorted u => insertSorted u sorted (sorted.length + 1)) []
    -- l1, l2 に対する帰納法で acc1, acc2 を保持
    have key : ∀ (l1' l2' : List FallingUnit)
        (h_len' : l1'.length = l2'.length)
        (h_pw' : ∀ (i : Nat) (hi : i < l1'.length) (p : QuarterPos),
            (l1'[i]'hi).positions.any (· == p) =
            (l2'[i]'(h_len' ▸ hi)).positions.any (· == p))
        (acc1 acc2 : List FallingUnit)
        (ha_len : acc1.length = acc2.length)
        (ha_pw : ∀ (i : Nat) (hi : i < acc1.length) (p : QuarterPos),
            (acc1[i]'hi).positions.any (· == p) =
            (acc2[i]'(ha_len ▸ hi)).positions.any (· == p)),
        let res1 := l1'.foldl (fun sorted u => insertSorted u sorted (sorted.length + 1)) acc1
        let res2 := l2'.foldl (fun sorted u => insertSorted u sorted (sorted.length + 1)) acc2
        res1.length = res2.length ∧
        ∀ (i : Nat) (hi1 : i < res1.length) (hi2 : i < res2.length) (p : QuarterPos),
            (res1[i]'hi1).positions.any (· == p) =
            (res2[i]'hi2).positions.any (· == p) := by
      intro l1' l2' h_len' h_pw'
      induction l1' generalizing l2' with
      | nil =>
          have : l2' = [] := by cases l2' with | nil => rfl | cons _ _ => simp at h_len'
          subst this
          intro acc1 acc2 ha_len ha_pw
          simp only [List.foldl]
          exact ⟨ha_len, fun i hi1 _hi2 p => ha_pw i hi1 p⟩
      | cons u1 rest1 ih =>
          cases l2' with
          | nil => simp at h_len'
          | cons u2 rest2 =>
              have h_rest_len : rest1.length = rest2.length := by simp at h_len'; exact h_len'
              have h_u : ∀ p, u1.positions.any (· == p) = u2.positions.any (· == p) :=
                  fun p => h_pw' 0 (by simp) p
              have h_rest_pw : ∀ (i : Nat) (hi : i < rest1.length) (p : QuarterPos),
                      (rest1[i]'hi).positions.any (· == p) =
                      (rest2[i]'(h_rest_len ▸ hi)).positions.any (· == p) :=
                  fun i hi p => h_pw' (i + 1) (by simp; omega) p
              intro acc1 acc2 ha_len ha_pw
              simp only [List.foldl]
              have h_ins := insertSorted_pointwise_ext h_u ha_len ha_pw (acc1.length + 1)
              -- fuel の正規化: acc2.length + 1 = acc1.length + 1
              have h_rw : insertSorted u2 acc2 (acc2.length + 1) = insertSorted u2 acc2 (acc1.length + 1) :=
                  congrArg (insertSorted u2 acc2) (by omega)
              simp only [h_rw]
              exact ih rest2 h_rest_len h_rest_pw
                  (insertSorted u1 acc1 (acc1.length + 1))
                  (insertSorted u2 acc2 (acc1.length + 1))
                  h_ins.1 h_ins.2
    -- key を sortFU に適用
    simp only [sortFallingUnits]
    have result := key l1 l2 h_len h_pw [] [] rfl (fun _ hi => absurd hi (by simp))
    constructor
    · exact result.1
    · intro i hi p
      exact result.2 i hi _ p

-- ============================================================
-- settle_foldl_eq: ソート後 foldl の等価性
-- ============================================================

/-- pointwise .any 等価な入力リストはソート後 foldl で同じ結果を生む
    （入力が pointwise 等価の場合に使用可能。Perm ベースの場合は settle_foldl_eq を参照） -/
private theorem sorted_foldl_pointwise_eq (s : Shape)
        (l1 l2 : List FallingUnit) (obs : List Layer)
        (h_len : l1.length = l2.length)
        (h_pw : ∀ (i : Nat) (hi : i < l1.length) (p : QuarterPos),
            (l1[i]'hi).positions.any (· == p) =
            (l2[i]'(h_len ▸ hi)).positions.any (· == p)) :
        (sortFallingUnits l1).foldl
            (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs =
        (sortFallingUnits l2).foldl
            (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs := by
    have h_sort := sortFallingUnits_pointwise_ext h_len h_pw
    exact foldl_pointwise_ext s _ _ obs h_sort.1 h_sort.2

-- ============================================================
-- 浮遊単位の位置素性
-- ============================================================

/-- QuarterPos.allValid s は重複なし (NoDup)。
    allValid s = (range lc).flatMap (fun li => Direction.all.map (fun d => ⟨li, d⟩))
    において、各内部リストは NoDup（Direction.all が 4 要素で重複なし）、
    異なる li の内部リストは disjoint（.layer が異なる）ため。 -/
private theorem allValid_nodup (s : Shape) : (QuarterPos.allValid s).Nodup := by
    unfold QuarterPos.allValid
    rw [List.nodup_flatMap]
    refine ⟨fun li _ => ?_, ?_⟩
    · -- (Direction.all.map fun d => ⟨li, d⟩).Nodup
      -- Direction.all は 4 要素で重複なし、map は layer 固定で injective
      have h_dir : Direction.all.Nodup := by unfold Direction.all; decide
      exact h_dir.map fun {_ _} h => congr_arg QuarterPos.dir h
    · -- Pairwise (Disjoint on f) (range s.layerCount)
      -- 異なる layer index → 構築される QuarterPos の .layer が異なる → disjoint
      exact (@List.nodup_range s.layerCount).imp fun {li₁ li₂} h_ne x h₁ h₂ => by
        rw [List.mem_map] at h₁ h₂
        obtain ⟨_, _, rfl⟩ := h₁
        obtain ⟨_, _, h_eq⟩ := h₂
        exact h_ne (congr_arg QuarterPos.layer h_eq).symm

/-- allStructuralClustersList の各クラスタの全位置は bondable (canFormBond = true)。
    allStructuralClustersList_is_structuralClusterList + structuralClusterList_sound
    + structuralReachable_canFormBond から従う。 -/
private theorem allStructuralClustersList_all_bondable (s : Shape)
        (c : List QuarterPos) (hc : c ∈ allStructuralClustersList s)
        (p : QuarterPos) (hp : c.any (· == p) = true) :
        ∃ v, p.getQuarter s = some v ∧ v.canFormBond = true := by
    have ⟨pos, h_eq, _, h_bond⟩ := allStructuralClustersList_is_structuralClusterList s c hc
    rw [h_eq] at hp
    exact structuralReachable_canFormBond s pos p (structuralClusterList_sound s pos p hp) h_bond

/-- allIsolatedPins に .any で含まれる位置のシェイプ上の象限は .pin である -/
private theorem allIsolatedPins_is_pin (s : Shape) (p : QuarterPos)
        (hp : (allIsolatedPins s).any (· == p) = true) :
        p.getQuarter s = some .pin := by
    have h_mem : p ∈ allIsolatedPins s := by
        rw [List.any_eq_true] at hp
        obtain ⟨q, hq_mem, hq_beq⟩ := hp
        exact eq_of_beq hq_beq ▸ hq_mem
    unfold allIsolatedPins at h_mem
    rw [List.mem_filter] at h_mem
    have h_pred := h_mem.2
    -- h_pred : (match p.getQuarter s with | some .pin => true | _ => false) = true
    generalize h_gq : QuarterPos.getQuarter s p = gq at h_pred
    cases gq with
    | none => exact absurd h_pred (by decide)
    | some q' =>
        cases q' with
        | pin => exact h_gq ▸ rfl
        | empty => simp at h_pred
        | crystal _ => simp at h_pred
        | colored _ _ => simp at h_pred

/-- floatingUnits をコンポーネントに展開するための等式 -/
private theorem floatingUnits_eq_append (s : Shape) :
        floatingUnits s =
            ((allStructuralClustersList s).filter fun c =>
                c.all fun p => !((groundedPositionsList s).any (· == p))).map .cluster ++
            ((allIsolatedPins s).filter fun p =>
                !((groundedPositionsList s).any (· == p))).map .pin := by
    unfold floatingUnits
    simp_rw [decide_not_mem_groundedPositions]

/-- allStructuralClustersList は重複なし (Nodup)。
    各クラスタは seed 位置を含み（非空）、異なるインデックスのクラスタは
    位置素 (allStructuralClustersList_disjoint) であるため、
    等しいクラスタが2つ存在すると seed が共有され矛盾する。 -/
private theorem allStructuralClustersList_nodup (s : Shape) :
        (allStructuralClustersList s).Nodup :=
    List.pairwise_iff_getElem.mpr fun i j hi hj h_lt => by
    intro h_eq
    -- cluster_i は seed pos_i を含む
    have ⟨pos_i, h_ci_eq, h_layer_i, _⟩ :=
        allStructuralClustersList_is_structuralClusterList s _ (List.getElem_mem hi)
    have h_has_seed : ((allStructuralClustersList s)[i]).any (· == pos_i) = true := by
        rw [h_ci_eq]
        exact structuralClusterList_complete s pos_i pos_i (by omega) GenericReachable.refl
    -- i < j → i ≠ j → disjoint → cluster_j に pos_i は含まれない
    have h_disj := allStructuralClustersList_disjoint s i j hi hj (by omega) pos_i h_has_seed
    -- しかし c_j = c_i なので pos_i を含むはず → 矛盾
    rw [← h_eq] at h_disj
    rw [h_has_seed] at h_disj
    exact Bool.noConfusion h_disj

/-- floatingUnits は重複なし (Nodup)。
    fc.map .cluster ++ fp.map .pin の形式で、
    fc は allStructuralClustersList の filter（Nodup保存）、.cluster は injective、
    fp は allIsolatedPins の filter（allValid の filter → Nodup）、.pin は injective、
    .cluster ≠ .pin → disjoint。 -/
private theorem floatingUnits_nodup (s : Shape) : (floatingUnits s).Nodup := by
    rw [floatingUnits_eq_append, List.nodup_append']
    refine ⟨?_, ?_, ?_⟩
    · -- (fc.map .cluster).Nodup
      exact ((allStructuralClustersList_nodup s).filter _).map
        fun {_ _} h => FallingUnit.cluster.inj h
    · -- (fp.map .pin).Nodup
      have h_iso : (allIsolatedPins s).Nodup := by
          unfold allIsolatedPins; exact (allValid_nodup s).filter _
      exact (h_iso.filter _).map fun {_ _} h => FallingUnit.pin.inj h
    · -- Disjoint (.cluster vs .pin)
      intro x h₁ h₂
      rw [List.mem_map] at h₁ h₂
      obtain ⟨_, _, rfl⟩ := h₁
      obtain ⟨_, _, h_eq⟩ := h₂
      exact FallingUnit.noConfusion h_eq

/-- floatingUnits の要素は pairwise で positions が素（各位置は最大1つの浮遊単位に属する）
    allStructuralClustersList は foldl + dedup で構築されるため、異なるクラスタは異なる
    連結成分に属し、位置を共有しない。孤立ピンは canFormBond=false のため
    クラスタに含まれず、互いに異なる位置を持つ。 -/
private theorem floatingUnits_pairwise_disjoint (s : Shape) :
        ∀ (i j : Nat) (hi : i < (floatingUnits s).length)
            (hj : j < (floatingUnits s).length), i ≠ j →
        ∀ (p : QuarterPos),
            ((floatingUnits s)[i]'hi).positions.any (· == p) = true →
            ((floatingUnits s)[j]'hj).positions.any (· == p) = false := by
    intro i j hi hj h_ne p hp_i
    -- 矛盾法: j の unit にも p が属すると仮定して矛盾を導く
    cases hp_j : ((floatingUnits s)[j]'hj).positions.any (· == p)
    case false => rfl
    case true =>
    exfalso
    -- p は unit_i と unit_j の両方に含まれる。unit_i, unit_j の型（クラスタ/ピン）で場合分け
    cases h_ui : (floatingUnits s)[i]'hi with
    | cluster ps_i =>
        have hp_i' : ps_i.any (· == p) = true := by
            simp only [h_ui, FallingUnit.positions] at hp_i; exact hp_i
        -- ps_i ∈ allStructuralClustersList s を示す
        have h_psi_mem : ps_i ∈ allStructuralClustersList s := by
            have h_elem : FallingUnit.cluster ps_i ∈ floatingUnits s :=
                h_ui ▸ List.getElem_mem hi
            rw [floatingUnits_eq_append, List.mem_append] at h_elem
            cases h_elem with
            | inl h =>
                rw [List.mem_map] at h
                obtain ⟨c, hc, h_eq⟩ := h
                exact FallingUnit.cluster.inj h_eq ▸ (List.mem_filter.mp hc).1
            | inr h =>
                rw [List.mem_map] at h
                obtain ⟨_, _, h_eq⟩ := h
                exact absurd h_eq (by intro h; exact FallingUnit.noConfusion h)
        -- p は bondable（クラスタ由来）
        have h_bond := allStructuralClustersList_all_bondable s ps_i h_psi_mem p hp_i'
        obtain ⟨v, hv_eq, hv_bond⟩ := h_bond
        cases h_uj : (floatingUnits s)[j]'hj with
        | cluster ps_j =>
            -- CC case: 両方クラスタ
            have hp_j' : ps_j.any (· == p) = true := by
                simp only [h_uj, FallingUnit.positions] at hp_j; exact hp_j
            have h_psj_mem : ps_j ∈ allStructuralClustersList s := by
                have h_elem : FallingUnit.cluster ps_j ∈ floatingUnits s :=
                    h_uj ▸ List.getElem_mem hj
                rw [floatingUnits_eq_append, List.mem_append] at h_elem
                cases h_elem with
                | inl h =>
                    rw [List.mem_map] at h
                    obtain ⟨c, hc, h_eq⟩ := h
                    exact FallingUnit.cluster.inj h_eq ▸ (List.mem_filter.mp hc).1
                | inr h =>
                    rw [List.mem_map] at h
                    obtain ⟨_, _, h_eq⟩ := h
                    exact absurd h_eq (by intro h; exact FallingUnit.noConfusion h)
            -- ps_i と ps_j は共に p を含む allStructuralClustersList の要素
            -- allStructuralClustersList_disjoint の対偶: 異なるインデックスなら位置を共有しない
            -- → 同一インデックス → ps_i = ps_j
            have ⟨k_i, hk_i, hk_i_eq⟩ := List.mem_iff_getElem.mp h_psi_mem
            have ⟨k_j, hk_j, hk_j_eq⟩ := List.mem_iff_getElem.mp h_psj_mem
            -- k_i ≠ k_j → 矛盾（disjointness）
            have h_k_eq : k_i = k_j := by
                by_contra h_k_ne
                have h_disj := allStructuralClustersList_disjoint s k_i k_j hk_i hk_j h_k_ne p
                    (hk_i_eq ▸ hp_i')
                rw [hk_j_eq] at h_disj
                exact absurd hp_j' (by rw [h_disj]; exact Bool.noConfusion)
            -- k_i = k_j → ps_i = ps_j → floatingUnits[i] = floatingUnits[j]
            -- NoDup → i = j → h_ne に矛盾
            have h_ps_eq : ps_i = ps_j := by
                subst h_k_eq; exact hk_i_eq.symm.trans hk_j_eq
            have h_fu_eq : (floatingUnits s)[i]'hi = (floatingUnits s)[j]'hj :=
                h_ui.trans ((congr_arg FallingUnit.cluster h_ps_eq).trans h_uj.symm)
            exact absurd ((floatingUnits_nodup s).getElem_inj_iff.mp h_fu_eq) h_ne
        | pin q_j =>
            -- CP case: i はクラスタ（bondable）, j はピン（not bondable）
            have hp_j' : [q_j].any (· == p) = true := by
                simp only [h_uj, FallingUnit.positions] at hp_j; exact hp_j
            rw [List.any_cons, List.any_nil, Bool.or_false] at hp_j'
            have h_eq_j : q_j = p := eq_of_beq hp_j'
            -- q_j ∈ allIsolatedPins s
            have h_qj_mem : q_j ∈ allIsolatedPins s := by
                have h_elem : FallingUnit.pin q_j ∈ floatingUnits s :=
                    h_uj ▸ List.getElem_mem hj
                rw [floatingUnits_eq_append, List.mem_append] at h_elem
                cases h_elem with
                | inl h =>
                    rw [List.mem_map] at h
                    obtain ⟨_, _, h_eq⟩ := h
                    exact absurd h_eq (by intro h; exact FallingUnit.noConfusion h)
                | inr h =>
                    rw [List.mem_map] at h
                    obtain ⟨q, hq, h_eq⟩ := h
                    exact FallingUnit.pin.inj h_eq ▸ (List.mem_filter.mp hq).1
            -- q_j.getQuarter s = some .pin
            have h_pin := allIsolatedPins_is_pin s q_j
                (List.any_eq_true.mpr ⟨q_j, h_qj_mem, beq_self_eq_true q_j⟩)
            -- p = q_j → p.getQuarter s = some .pin → .pin.canFormBond = false
            rw [h_eq_j] at h_pin
            rw [h_pin] at hv_eq
            cases hv_eq
            -- v = .pin → v.canFormBond = false ≠ true
            exact absurd hv_bond (by decide)
    | pin q_i =>
        have hp_i' : [q_i].any (· == p) = true := by
            simp only [h_ui, FallingUnit.positions] at hp_i; exact hp_i
        rw [List.any_cons, List.any_nil, Bool.or_false] at hp_i'
        have h_eq_i : q_i = p := eq_of_beq hp_i'
        -- q_i ∈ allIsolatedPins s
        have h_qi_mem : q_i ∈ allIsolatedPins s := by
            have h_elem : FallingUnit.pin q_i ∈ floatingUnits s :=
                h_ui ▸ List.getElem_mem hi
            rw [floatingUnits_eq_append, List.mem_append] at h_elem
            cases h_elem with
            | inl h =>
                rw [List.mem_map] at h
                obtain ⟨_, _, h_eq⟩ := h
                exact absurd h_eq (by intro h; exact FallingUnit.noConfusion h)
            | inr h =>
                rw [List.mem_map] at h
                obtain ⟨q, hq, h_eq⟩ := h
                exact FallingUnit.pin.inj h_eq ▸ (List.mem_filter.mp hq).1
        have h_pin_i := allIsolatedPins_is_pin s q_i
            (List.any_eq_true.mpr ⟨q_i, h_qi_mem, beq_self_eq_true q_i⟩)
        cases h_uj : (floatingUnits s)[j]'hj with
        | cluster ps_j =>
            -- PC case: i はピン, j はクラスタ（CP の対称）
            have hp_j' : ps_j.any (· == p) = true := by
                simp only [h_uj, FallingUnit.positions] at hp_j; exact hp_j
            have h_psj_mem : ps_j ∈ allStructuralClustersList s := by
                have h_elem : FallingUnit.cluster ps_j ∈ floatingUnits s :=
                    h_uj ▸ List.getElem_mem hj
                rw [floatingUnits_eq_append, List.mem_append] at h_elem
                cases h_elem with
                | inl h =>
                    rw [List.mem_map] at h
                    obtain ⟨c, hc, h_eq⟩ := h
                    exact FallingUnit.cluster.inj h_eq ▸ (List.mem_filter.mp hc).1
                | inr h =>
                    rw [List.mem_map] at h
                    obtain ⟨_, _, h_eq⟩ := h
                    exact absurd h_eq (by intro h; exact FallingUnit.noConfusion h)
            have h_bond := allStructuralClustersList_all_bondable s ps_j h_psj_mem p hp_j'
            obtain ⟨v, hv_eq, hv_bond⟩ := h_bond
            -- q_i = p → p.getQuarter s = some .pin → contradiction with bondable
            rw [h_eq_i] at h_pin_i
            rw [h_pin_i] at hv_eq; cases hv_eq
            exact absurd hv_bond (by decide)
        | pin q_j =>
            -- PP case: 両方ピン → q_i = p = q_j
            have hp_j' : [q_j].any (· == p) = true := by
                simp only [h_uj, FallingUnit.positions] at hp_j; exact hp_j
            rw [List.any_cons, List.any_nil, Bool.or_false] at hp_j'
            have h_eq_j : q_j = p := eq_of_beq hp_j'
            -- q_i = p = q_j → floatingUnits[i] = .pin p = floatingUnits[j]
            -- NoDup → i = j → h_ne に矛盾
            have h_fu_eq : (floatingUnits s)[i]'hi = (floatingUnits s)[j]'hj :=
                h_ui.trans ((congr_arg FallingUnit.pin
                    (h_eq_i.trans h_eq_j.symm)).trans h_uj.symm)
            exact absurd ((floatingUnits_nodup s).getElem_inj_iff.mp h_fu_eq) h_ne

/-- map FU.rotate180 は位置素性を保存する -/
private theorem map_rotate180_pairwise_disjoint (l : List FallingUnit)
        (h_disj : ∀ (i j : Nat) (hi : i < l.length) (hj : j < l.length), i ≠ j →
            ∀ p, (l[i]'hi).positions.any (· == p) = true →
                (l[j]'hj).positions.any (· == p) = false) :
        ∀ (i j : Nat) (hi : i < (l.map FallingUnit.rotate180).length)
            (hj : j < (l.map FallingUnit.rotate180).length), i ≠ j →
        ∀ p, ((l.map FallingUnit.rotate180)[i]'hi).positions.any (· == p) = true →
            ((l.map FallingUnit.rotate180)[j]'hj).positions.any (· == p) = false := by
    intro i j hi hj h_ne p h_any
    simp only [List.length_map] at hi hj
    simp only [List.getElem_map] at h_any ⊢
    rw [FallingUnit.positions_rotate180] at h_any ⊢
    rw [any_map_rotate180_beq] at h_any ⊢
    exact h_disj i j hi hj h_ne p.rotate180 h_any

-- ============================================================
-- settle_foldl_eq: ソート済み foldl の等価性
-- ============================================================

/-- リスト prefix ++ [u, v] ++ suffix の foldl は、u と v が方角素なら
    prefix ++ [v, u] ++ suffix の foldl と等しい -/
private theorem foldl_settle_swap_at (s : Shape) (prefix_ : List FallingUnit)
        (u v : FallingUnit) (suffix : List FallingUnit) (obs : List Layer)
        (h_uv : ∀ p, p ∈ u.positions → v.positions.any (fun q => q.dir == p.dir) = false)
        (h_vu : ∀ p, p ∈ v.positions → u.positions.any (fun q => q.dir == p.dir) = false) :
        (prefix_ ++ u :: v :: suffix).foldl
            (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs =
        (prefix_ ++ v :: u :: suffix).foldl
            (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs := by
    rw [List.foldl_append, List.foldl_append]
    exact foldl_settle_head_swap s u v suffix _ h_uv h_vu

/-- floatingUnits s の各ユニットに対し、floatingUnits s.rotate180 に
    .any 等価なユニットが存在する -/
private theorem floatingUnit_any_in_rotate180 (s : Shape) (u : FallingUnit)
        (hu : u ∈ floatingUnits s) :
        ∃ v ∈ floatingUnits s.rotate180,
            ∀ p, u.rotate180.positions.any (· == p) = v.positions.any (· == p) := by
    rw [floatingUnits_eq_append, List.mem_append] at hu
    cases hu with
    | inl h_cluster =>
        -- u = .cluster ps, ps ∈ allStructuralClustersList s で浮遊
        rw [List.mem_map] at h_cluster
        obtain ⟨ps, hps_filtered, rfl⟩ := h_cluster
        rw [List.mem_filter] at hps_filtered
        obtain ⟨hps_mem, hps_floating⟩ := hps_filtered
        -- ps = structuralClusterList s pos for some pos
        obtain ⟨pos, hps_eq, h_layer, h_bondable⟩ :=
            allStructuralClustersList_is_structuralClusterList s ps hps_mem
        -- u.r180 = .cluster (ps.map r180), positions = ps.map r180
        -- structuralClusterList s.r180 (pos.r180) は .any 等価
        -- pos.r180 は s.r180 で bondable
        have h_bond_r180 : match pos.rotate180.getQuarter s.rotate180 with
                | some q => q.canFormBond = true | none => False := by
            rw [getQuarter_rotate180]
            obtain ⟨q, hq, hb⟩ := h_bondable; rw [hq]; exact hb
        have h_layer_r180 : pos.rotate180.layer < s.rotate180.layerCount := by
            rw [Shape.layerCount_rotate180, QuarterPos.rotate180_layer]; exact h_layer
        -- allStructuralClustersList s.r180 は pos.r180 をカバーする
        have h_covers := allStructuralClustersList_covers s.rotate180 pos.rotate180
            h_layer_r180 h_bond_r180
        rw [List.any_eq_true] at h_covers
        obtain ⟨c', hc'_mem, hc'_any⟩ := h_covers
        -- c' は pos.r180 を含む構造クラスタ
        -- c' = structuralClusterList s.r180 pos' for some pos'
        obtain ⟨pos', hc'_eq, _, _⟩ :=
            allStructuralClustersList_is_structuralClusterList s.rotate180 c' hc'_mem
        -- c' の .any と (ps.map r180) の .any は一致する
        -- mem_structuralCluster_rotate180 + 連結成分の一意性から導出
        have h_any_eq : ∀ (q : QuarterPos),
                c'.any (· == q) = (ps.map QuarterPos.rotate180).any (· == q) := by
            intro q
            -- ps = structuralClusterList s pos
            -- Finset メンバーシップ等変 → List .any 等変
            have h_sc : ps.any (· == q.rotate180) =
                    (structuralClusterList s.rotate180 pos.rotate180).any (· == q) := by
                have h := mem_structuralCluster_rotate180 s pos q.rotate180
                simp only [QuarterPos.rotate180_rotate180, structuralCluster,
                    List.mem_toFinset] at h
                rw [hps_eq]
                exact Bool.eq_iff_iff.mpr
                    ((any_beq_iff_mem _ _).trans (h.trans (any_beq_iff_mem _ _).symm))
            -- h_sc: ps.any (· == q.r180) = (structuralClusterList s.r180 pos.r180).any (· == q)
            -- c' のメンバーシップと structuralClusterList s.r180 pos.r180 のメンバーシップは一致
            -- （同じ連結成分のため）
            -- c' = structuralClusterList s.r180 pos' で pos.r180 を含む
            -- structuralClusterList s.r180 pos.r180 も pos.r180 を含む
            -- 両方が pos.r180 を含む → 同じ連結成分 → .any 一致
            -- structuralClusterList_shared_contains_seed を使う
            have h_sc_pos_r180 : (structuralClusterList s.rotate180 pos.rotate180).any (· == pos.rotate180) = true :=
                structuralClusterList_complete s.rotate180 pos.rotate180 pos.rotate180
                    (by rw [Shape.layerCount_rotate180]; omega)
                    GenericReachable.refl
            -- c' 内に pos.r180 がある（hc'_any から）
            -- c' = structuralClusterList s.r180 pos'
            -- pos.r180 は c' にも structuralClusterList s.r180 pos.r180 にも含まれる
            -- → structuralClusterList_shared_contains_seed: 同じ connected component の seed は相互到達可能
            -- → 同じクラスタ (any レベルで同一)
            -- 直接: hc'_eq を使って c' = structuralClusterList s.r180 pos'
            -- pos.r180 ∈ c' → pos.r180 ∈ structuralClusterList s.r180 pos'
            -- → pos' は structuralClusterList s.r180 pos.r180 に含まれる (shared_contains_seed)
            -- → structuralClusterList s.r180 pos' と structuralClusterList s.r180 pos.r180 は同じ .any
            rw [hc'_eq]
            -- goal: (structuralClusterList s.r180 pos').any (· == q) = (ps.map QP.r180).any (· == q)
            -- = ps.any (· == q.r180) (from any_map_rotate180_beq)
            rw [any_map_rotate180_beq]
            -- goal: (structuralClusterList s.r180 pos').any (· == q) = ps.any (· == q.r180)
            rw [h_sc]
            -- goal: (structuralClusterList s.r180 pos').any (· == q) = (structuralClusterList s.r180 pos.r180).any (· == q)
            -- pos' の クラスタと pos.r180 のクラスタは同一 (.any レベル)
            -- pos.r180 は structuralClusterList s.r180 pos' に含まれる (hc'_any, hc'_eq)
            have h_pos_r180_in_c' : (structuralClusterList s.rotate180 pos').any (· == pos.rotate180) = true := by
                rw [← hc'_eq]; exact hc'_any
            -- structuralClusterList_shared_contains_seed 的な議論
            -- pos.r180 は sc(s.r180, pos') に到達可能 → pos' は sc(s.r180, pos.r180) に到達可能
            have h_reach_pos' : GenericReachable (isStructurallyBonded s.rotate180) pos.rotate180 pos' := by
                have h_pos_reach := structuralClusterList_sound s.rotate180 pos' pos.rotate180 h_pos_r180_in_c'
                exact h_pos_reach.symm (fun a b => isStructurallyBonded_symm s.rotate180 a b)
            -- pos' は sc(s.r180, pos.r180) に到達可能 → sc(s.r180, pos') ⊆ sc(s.r180, pos.r180)
            -- and sc(s.r180, pos.r180) ⊆ sc(s.r180, pos')
            -- → .any 一致
            have h_pos'_in_sc : (structuralClusterList s.rotate180 pos.rotate180).any (· == pos') = true :=
                structuralClusterList_complete s.rotate180 pos.rotate180 pos'
                    (by rw [Shape.layerCount_rotate180]; omega)
                    h_reach_pos'
            -- q を含む側: sc(s.r180, pos').any (· == q) = sc(s.r180, pos.r180).any (· == q)
            -- これは sc の「同連結成分なら .any 一致」から
            cases hq : (structuralClusterList s.rotate180 pos').any (· == q) with
            | true =>
                -- q ∈ sc(s.r180, pos') → q は pos' から到達可能
                -- pos は pos' から到達可能（h_reach_pos' の逆方向）
                -- → q は pos.r180 から到達可能 → q ∈ sc(s.r180, pos.r180)
                have h_q_reach := structuralClusterList_sound s.rotate180 pos' q hq
                have h_q_from_pos := GenericReachable.trans
                    ((structuralClusterList_sound s.rotate180 pos' pos.rotate180 h_pos_r180_in_c').symm
                        (fun a b => isStructurallyBonded_symm s.rotate180 a b))
                    h_q_reach
                symm; exact structuralClusterList_complete s.rotate180 pos.rotate180 q
                    (by rw [Shape.layerCount_rotate180]; omega)
                    h_q_from_pos
            | false =>
                -- q ∉ sc(s.r180, pos') → q ∉ sc(s.r180, pos.r180) も示す
                symm
                cases hq2 : (structuralClusterList s.rotate180 pos.rotate180).any (· == q) with
                | false => rfl
                | true =>
                    exfalso
                    have := structuralClusterList_complete s.rotate180 pos' q
                        (by rw [Shape.layerCount_rotate180]; omega)
                        (GenericReachable.trans
                            ((structuralClusterList_sound s.rotate180 pos.rotate180 pos' h_pos'_in_sc).symm
                                (fun a b => isStructurallyBonded_symm s.rotate180 a b))
                            (structuralClusterList_sound s.rotate180 pos.rotate180 q hq2))
                    rw [hq] at this; exact Bool.noConfusion this
        -- c' が浮遊であることを示す
        have h_floating : c'.all (fun p => !((groundedPositionsList s.rotate180).any (· == p))) = true := by
            rw [List.all_eq_true]
            intro q hq_mem
            have hq_any : c'.any (· == q) = true :=
                List.any_eq_true.mpr ⟨q, hq_mem, beq_self_eq_true q⟩
            rw [h_any_eq] at hq_any
            rw [any_map_rotate180_beq] at hq_any
            -- q.r180 ∈ ps → ps 浮遊 → q.r180 は s で ungrounded
            rw [List.all_eq_true] at hps_floating
            have h_qr_in_ps : q.rotate180 ∈ ps := by
                rw [List.any_eq_true] at hq_any
                obtain ⟨x, hx_mem, hx_beq⟩ := hq_any
                exact eq_of_beq hx_beq ▸ hx_mem
            have h_ungrounded := hps_floating q.rotate180 h_qr_in_ps
            simp only [Bool.not_eq_true'] at h_ungrounded ⊢
            have h_gp : (groundedPositionsList s).any (· == q.rotate180) =
                    (groundedPositionsList s.rotate180).any (· == q) := by
                have h := mem_groundedPositions_rotate180 s q.rotate180
                simp only [QuarterPos.rotate180_rotate180, groundedPositions,
                    List.mem_toFinset] at h
                exact Bool.eq_iff_iff.mpr
                    ((any_beq_iff_mem _ _).trans (h.trans (any_beq_iff_mem _ _).symm))
            rw [← h_gp]; exact h_ungrounded
        -- .cluster c' ∈ floatingUnits s.r180
        have h_v_mem : FallingUnit.cluster c' ∈ floatingUnits s.rotate180 := by
            rw [floatingUnits_eq_append, List.mem_append]
            exact .inl (List.mem_map.mpr ⟨c', List.mem_filter.mpr ⟨hc'_mem, h_floating⟩, rfl⟩)
        -- (.cluster ps).r180 の positions = ps.map r180
        -- .cluster c' の positions = c'
        -- h_any_eq: ∀ q, c'.any (· == q) = (ps.map r180).any (· == q)
        exact ⟨.cluster c', h_v_mem, fun p => by
            simp only [FallingUnit.rotate180, FallingUnit.positions]
            exact (h_any_eq p).symm⟩
    | inr h_pin =>
        -- u = .pin p, p ∈ allIsolatedPins s で浮遊
        rw [List.mem_map] at h_pin
        obtain ⟨p, hp_filtered, rfl⟩ := h_pin
        -- hp_filtered : p ∈ (allIsolatedPins s).filter (fun p => !((gP s).any (· == p)))
        -- p.r180 は s.r180 で isolated pin
        have hp_pins : p ∈ allIsolatedPins s :=
            List.mem_of_mem_filter hp_filtered
        have hp_floating_raw := (List.mem_filter.mp hp_filtered).2
        -- grounded の .any == false を示す
        have hp_floating_bool : (groundedPositionsList s).any (· == p) = false := by
            simp only [Bool.not_eq_true', Bool.eq_false_iff] at hp_floating_raw ⊢
            exact hp_floating_raw
        have h_pin_r180 : p.rotate180 ∈ allIsolatedPins s.rotate180 := by
            unfold allIsolatedPins
            rw [CrystalBond.allValid_rotate180_eq]
            rw [List.mem_filter]
            constructor
            · -- p.r180 ∈ allValid s
              unfold allIsolatedPins at hp_pins
              have h_p_valid := (List.mem_filter.mp hp_pins).1
              have h_layer : p.layer < s.layerCount :=
                  (allValid_any_iff_layer' s p).mp
                      (List.any_eq_true.mpr ⟨p, h_p_valid, BEq.rfl⟩)
              have h_any := (allValid_any_iff_layer' s p.rotate180).mpr h_layer
              rw [List.any_eq_true] at h_any
              obtain ⟨y, hy, hye⟩ := h_any; exact eq_of_beq hye ▸ hy
            · -- p.r180 は s.r180 で .pin
              rw [getQuarter_rotate180]
              -- p.getQuarter s = some .pin（hp_pins から）
              unfold allIsolatedPins at hp_pins
              exact (List.mem_filter.mp hp_pins).2
        -- p.r180 は s.r180 で ungrounded
        have h_ungrounded_bool : (groundedPositionsList s.rotate180).any (· == p.rotate180) = false := by
            have h_gp : (groundedPositionsList s).any (· == p) =
                    (groundedPositionsList s.rotate180).any (· == p.rotate180) := by
                have h := mem_groundedPositions_rotate180 s p
                simp only [groundedPositions, List.mem_toFinset] at h
                exact Bool.eq_iff_iff.mpr
                    ((any_beq_iff_mem _ _).trans (h.trans (any_beq_iff_mem _ _).symm))
            rw [← h_gp]; exact hp_floating_bool
        -- .pin p.r180 ∈ floatingUnits s.r180
        have h_v_mem : FallingUnit.pin p.rotate180 ∈ floatingUnits s.rotate180 := by
            rw [floatingUnits_eq_append, List.mem_append]
            refine .inr (List.mem_map.mpr ⟨p.rotate180, ?_, rfl⟩)
            rw [List.mem_filter]
            refine ⟨h_pin_r180, ?_⟩
            simp only [Bool.not_eq_true']
            exact h_ungrounded_bool
        exact ⟨.pin p.rotate180, h_v_mem, fun q => rfl⟩

/-- floatingUnits の各要素は少なくとも 1 つの位置を持つ -/
private theorem floatingUnit_positions_nonempty (s : Shape) (u : FallingUnit)
        (hu : u ∈ floatingUnits s) :
        ∃ p, p ∈ u.positions := by
    rw [floatingUnits_eq_append, List.mem_append] at hu
    cases hu with
    | inl h_cluster =>
        rw [List.mem_map] at h_cluster
        obtain ⟨ps, hps_filtered, rfl⟩ := h_cluster
        -- ps ∈ allStructuralClustersList s → ps は structuralClusterList s pos
        -- structuralClusterList は seed を含む → 非空
        rw [List.mem_filter] at hps_filtered
        obtain ⟨pos, hps_eq, h_layer, _⟩ :=
            allStructuralClustersList_is_structuralClusterList s ps hps_filtered.1
        -- seed pos ∈ ps
        have h_seed : ps.any (· == pos) = true := by
            rw [hps_eq]
            exact structuralClusterList_complete s pos pos (by omega) GenericReachable.refl
        rw [List.any_eq_true] at h_seed
        obtain ⟨q, hq, _⟩ := h_seed
        exact ⟨q, hq⟩
    | inr h_pin =>
        rw [List.mem_map] at h_pin
        obtain ⟨p, _, rfl⟩ := h_pin
        -- .pin p の positions は [p]
        exact ⟨p, by simp [FallingUnit.positions]⟩

/-- rotate180 後の positions の .any は元の .any と等価 -/
private theorem any_positions_rotate180 (u : FallingUnit) (p : QuarterPos) :
        u.rotate180.positions.any (· == p.rotate180) = u.positions.any (· == p) := by
    rw [FallingUnit.positions_rotate180, any_map_rotate180_beq,
        QuarterPos.rotate180_rotate180]

/-- NoDup リスト間の注射的対応があれば長さ以下 -/
private theorem length_le_of_injection {α β : Type} [DecidableEq β]
        (l1 : List α) (l2 : List β)
        (f : α → β)
        (h_mem : ∀ a ∈ l1, f a ∈ l2)
        (h_inj : ∀ a₁ ∈ l1, ∀ a₂ ∈ l1, f a₁ = f a₂ → a₁ = a₂)
        (h_nodup1 : l1.Nodup)
        (_h_nodup2 : l2.Nodup) :
        l1.length ≤ l2.length := by
    have h_map_nodup : (l1.map f).Nodup :=
        (List.nodup_map_iff_inj_on h_nodup1).mpr h_inj
    have h_map_sub : l1.map f ⊆ l2 := by
        intro x hx; rw [List.mem_map] at hx
        obtain ⟨a, ha, rfl⟩ := hx; exact h_mem a ha
    calc l1.length = (l1.map f).length := (List.length_map ..).symm
      _ ≤ l2.length := (List.subperm_of_subset h_map_nodup h_map_sub).length_le

/-- floatingUnits の長さは rotate180 で不変 -/
private theorem floatingUnits_length_rotate180 (s : Shape) :
        (floatingUnits s).length = (floatingUnits s.rotate180).length := by
    -- 補助: s → s.r180 方向の |fU(s)| ≤ |fU(s.r180)|
    suffices h_le : ∀ (t : Shape),
            (floatingUnits t).length ≤ (floatingUnits t.rotate180).length by
        apply Nat.le_antisymm (h_le s)
        have h := h_le s.rotate180
        rw [Shape.rotate180_rotate180] at h; exact h
    intro t
    -- 各 u ∈ fU(t) に対応する v ∈ fU(t.r180) を choose で取る
    have hg_ex : ∀ u ∈ floatingUnits t,
            ∃ v ∈ floatingUnits t.rotate180,
                ∀ p, u.rotate180.positions.any (· == p) = v.positions.any (· == p) :=
        floatingUnit_any_in_rotate180 t
    -- 非依存型の写像を構築
    open Classical in
    let g : FallingUnit → FallingUnit :=
        fun u => if h : u ∈ floatingUnits t
            then (hg_ex u h).choose
            else u
    have hg_mem : ∀ u ∈ floatingUnits t, g u ∈ floatingUnits t.rotate180 := by
        intro u hu
        show (if h : u ∈ floatingUnits t then (hg_ex u h).choose else u) ∈ _
        rw [dif_pos hu]
        exact (hg_ex u hu).choose_spec.1
    have hg_any : ∀ u ∈ floatingUnits t, ∀ p : QuarterPos,
            u.rotate180.positions.any (· == p) = (g u).positions.any (· == p) := by
        intro u hu
        show ∀ p, u.rotate180.positions.any (· == p) =
            (if h : u ∈ floatingUnits t then (hg_ex u h).choose else u).positions.any (· == p)
        rw [dif_pos hu]
        exact (hg_ex u hu).choose_spec.2
    -- 注射性
    have hg_inj : ∀ u1 ∈ floatingUnits t, ∀ u2 ∈ floatingUnits t,
            g u1 = g u2 → u1 = u2 := by
        intro u1 hu1 u2 hu2 h_eq
        by_contra h_ne
        have ⟨p, hp⟩ := floatingUnit_positions_nonempty t u1 hu1
        have h1 : u1.rotate180.positions.any (· == p.rotate180) = true := by
            rw [any_positions_rotate180]; exact List.any_eq_true.mpr ⟨p, hp, BEq.rfl⟩
        have h2 : u2.rotate180.positions.any (· == p.rotate180) = true := by
            rw [hg_any u2 hu2, ← h_eq, ← hg_any u1 hu1]; exact h1
        rw [any_positions_rotate180] at h2
        obtain ⟨i, hi, h_eq_i⟩ := List.mem_iff_getElem.mp hu1
        obtain ⟨j, hj, h_eq_j⟩ := List.mem_iff_getElem.mp hu2
        subst h_eq_i; subst h_eq_j
        have h_ij : i ≠ j := fun h_eq_ij => h_ne (by subst h_eq_ij; rfl)
        exact absurd
            (by rw [List.any_eq_true] at h2 ⊢; exact h2 :
                ((floatingUnits t)[j]).positions.any (· == p) = true)
            (Bool.eq_false_iff.mp
                (floatingUnits_pairwise_disjoint t i j hi hj h_ij p
                    (List.any_eq_true.mpr ⟨p, hp, BEq.rfl⟩)))
    exact length_le_of_injection _ _ g hg_mem hg_inj (floatingUnits_nodup t) (floatingUnits_nodup t.rotate180)

/-- insertSorted は要素 u をソート済みリスト sorted の位置 k に挿入する形で分解できる:
    insertSorted u sorted fuel = sorted.take k ++ [u] ++ sorted.drop k
    （fuel ≥ sorted.length のとき）。
    結果として、sorted 内の既存要素の相対順序は保存される。 -/
private theorem insertSorted_split (u : FallingUnit) (sorted : List FallingUnit)
        (fuel : Nat) (h_fuel : fuel ≥ sorted.length) :
        ∃ k, k ≤ sorted.length ∧
            insertSorted u sorted fuel = sorted.take k ++ [u] ++ sorted.drop k := by
    induction sorted, fuel using insertSorted.induct u with
    | case1 sorted =>
        -- fuel = 0 → u :: sorted, k = 0
        exact ⟨0, by omega, by simp [insertSorted]⟩
    | case2 =>
        -- sorted = [] → k = 0
        exact ⟨0, by omega, rfl⟩
    | case3 fuel v rest h_spb =>
        -- spb(u, v) = true → u :: v :: rest, k = 0
        simp only [insertSorted, h_spb, ite_true]
        exact ⟨0, by omega, rfl⟩
    | case4 fuel v rest h_not_spb_uv h_spb_vu ih =>
        -- spb(v, u) = true → v :: insertSorted u rest fuel
        simp only [insertSorted, h_not_spb_uv, h_spb_vu, ite_true]
        have h_fuel' : fuel ≥ rest.length := by
            simp only [List.length] at h_fuel; omega
        obtain ⟨k', hk', hk'_eq⟩ := ih h_fuel'
        exact ⟨k' + 1, by simp only [List.length]; omega,
            by simp [hk'_eq, List.take_succ_cons, List.drop_succ_cons]⟩
    | case5 fuel v rest h_not_spb_uv h_not_spb_vu h_tb =>
        -- tied, u.tb ≤ v.tb → u :: v :: rest, k = 0
        simp only [insertSorted, h_not_spb_uv, h_not_spb_vu, h_tb, ite_true]
        exact ⟨0, by omega, rfl⟩
    | case6 fuel v rest h_not_spb_uv h_not_spb_vu h_not_tb ih =>
        -- tied, u.tb > v.tb → v :: insertSorted u rest fuel
        simp only [insertSorted, h_not_spb_uv, ite_false, h_not_spb_vu, ite_false, h_not_tb, ite_false]
        have h_fuel' : fuel ≥ rest.length := by
            simp only [List.length] at h_fuel; omega
        obtain ⟨k', hk', hk'_eq⟩ := ih h_fuel'
        exact ⟨k' + 1, by simp only [List.length]; omega,
            by simp [hk'_eq, List.take_succ_cons, List.drop_succ_cons]⟩

-- ============================================================
-- バブルソート帰納: NoDup 置換リストの foldl 等価性
-- ============================================================

/-- DecidableEq ベースの等値判定述語 (BEq ではなく decide を使用) -/
private def eqPred (x : FallingUnit) : FallingUnit → Bool := fun y => decide (y = x)

/-- eqPred x x = true (反射性) -/
private theorem eqPred_self (x : FallingUnit) : eqPred x x = true := decide_eq_true rfl

/-- eqPred x y = true → y = x (等値性抽出) -/
private theorem eq_of_eqPred (x y : FallingUnit) (h : eqPred x y = true) : y = x :=
    of_decide_eq_true h

/-- リスト中の要素 x の位置を返す (DecidableEq ベース) -/
private def posIn (x : FallingUnit) (l : List FallingUnit) : Nat :=
    l.findIdx (eqPred x)

/-- posIn x l < l.length ← x ∈ l -/
private theorem posIn_lt_length (x : FallingUnit) (l : List FallingUnit)
        (hx : x ∈ l) : posIn x l < l.length := by
    exact List.findIdx_lt_length_of_exists ⟨x, hx, eqPred_self x⟩

/-- posIn で取得した位置の要素は x に等しい -/
private theorem getElem_posIn (x : FallingUnit) (l : List FallingUnit)
        (hx : x ∈ l) :
        l[posIn x l]'(posIn_lt_length x l hx) = x := by
    have h := posIn_lt_length x l hx
    have h_match : eqPred x (l[posIn x l]'h) = true :=
        @List.findIdx_getElem _ (eqPred x) l h
    exact eq_of_eqPred x _ h_match

/-- リスト l1 の l2 に対する反転数: l1[i], l1[j] (i<j) で l2 内の位置が逆転するペアの数。
    全ペア (i,j) を列挙し、i<j かつ l2 内で順序が逆転しているペアの数を返す。 -/
private def invCount (l1 l2 : List FallingUnit) : Nat :=
    let pairs := do
        let i ← List.range l1.length
        let j ← List.range l1.length
        if i < j then pure (i, j) else []
    pairs.foldl (fun acc (i, j) =>
        if h₁ : i < l1.length then
            if h₂ : j < l1.length then
                if posIn l1[i] l2 > posIn l1[j] l2 then acc + 1 else acc
            else acc
        else acc
    ) 0

/-- foldl で条件付き加算した結果は非負・単調非減少:
    foldl が init から始まって各要素で条件付き +1 する場合、init 以上 -/
private theorem foldl_cond_add_ge_init {α : Type*} (l : List α) (p : α → Bool) (init : Nat) :
        l.foldl (fun acc x => if p x then acc + 1 else acc) init ≥ init := by
    induction l generalizing init with
    | nil => simp [List.foldl]
    | cons hd tl ih =>
      simp only [List.foldl]
      by_cases hp : p hd = true
      · simp only [hp, ite_true]
        have := ih (init + 1)
        omega
      · simp only [Bool.eq_false_iff.mpr (by simpa using hp)]
        exact ih init

/-- foldl 条件付き加算 = 0 → リストの全要素が条件を満たさない -/
private theorem foldl_cond_add_zero {α : Type*} (l : List α) (p : α → Bool) :
        l.foldl (fun acc x => if p x then acc + 1 else acc) 0 = 0 →
        ∀ x ∈ l, p x = false := by
    induction l with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.foldl]
      intro h_fold
      by_cases hp : p hd = true
      · simp only [hp, ite_true] at h_fold
        have h_ge := foldl_cond_add_ge_init tl p 1
        simp only [Nat.zero_add] at h_fold
        omega
      · have hp_false : p hd = false := by simpa using hp
        simp only [hp_false] at h_fold
        intro x hx
        cases hx with
        | head => exact hp_false
        | tail _ hx => exact ih h_fold x hx

/-- posIn は NoDup リスト上で単射 -/
private theorem posIn_injective (l : List FallingUnit) (_h_nodup : l.Nodup)
        (x y : FallingUnit) (hx : x ∈ l) (hy : y ∈ l)
        (h_eq : posIn x l = posIn y l) : x = y := by
    have hx_get := getElem_posIn x l hx
    have hy_get := getElem_posIn y l hy
    have h_len_x := posIn_lt_length x l hx
    have h_len_y := posIn_lt_length y l hy
    -- l[posIn x l] = x, l[posIn y l] = y, posIn x l = posIn y l → x = y
    calc x = l[posIn x l]'h_len_x := hx_get.symm
      _ = l[posIn y l]'h_len_y := by congr 1
      _ = y := hy_get

/-- 単調非減少関数の foldl は init 以上 -/
private theorem foldl_mono_ge_init {α : Type*} (l : List α) (f : Nat → α → Nat) (init : Nat)
        (h_mono : ∀ acc x, f acc x ≥ acc) :
        l.foldl f init ≥ init := by
    induction l generalizing init with
    | nil => simp [List.foldl]
    | cons hd tl ih =>
      simp only [List.foldl]
      have h1 := h_mono init hd
      have h2 := ih (f init hd)
      omega

/-- 単調非減少関数の foldl = 0 → x ∈ l で f 0 x ≥ 1 なら矛盾 -/
private theorem foldl_mono_zero_imp {α : Type*} (l : List α) (f : Nat → α → Nat)
        (h_mono : ∀ acc x, f acc x ≥ acc)
        (_h_mono_add : ∀ acc₁ acc₂ x, acc₁ ≤ acc₂ → f acc₁ x ≤ f acc₂ x)
        (h_fold : l.foldl f 0 = 0) :
        ∀ x ∈ l, f 0 x = 0 := by
    induction l with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.foldl] at h_fold
      have h_f0_hd := h_mono 0 hd
      have h_foldl_ge := foldl_mono_ge_init tl f (f 0 hd) h_mono
      have h_f0 : f 0 hd = 0 := by omega
      rw [h_f0] at h_fold
      intro x hx
      cases hx with
      | head => exact h_f0
      | tail _ hx => exact ih h_fold x hx

/-- NoDup リストにおいて posIn l[k] l = k -/
private theorem posIn_getElem_self (l : List FallingUnit) (h_nodup : l.Nodup)
        (k : Nat) (hk : k < l.length) :
        posIn l[k] l = k := by
    unfold posIn
    rw [List.findIdx_eq hk]
    constructor
    · exact eqPred_self _
    · intro j hj
      have h_ne : l[j]'(Nat.lt_trans hj hk) ≠ l[k] := by
        intro h_eq
        exact absurd (h_nodup.getElem_inj_iff.mp h_eq) (by omega)
      simp [eqPred, h_ne]

/-- foldl の init 単調性 -/
private theorem foldl_mono_le_init {β : Type*} (l : List β) (f : Nat → β → Nat)
        (a b : Nat) (h_le : a ≤ b)
        (h_mono_le : ∀ acc₁ acc₂ y, acc₁ ≤ acc₂ → f acc₁ y ≤ f acc₂ y) :
        l.foldl f a ≤ l.foldl f b := by
    induction l generalizing a b with
    | nil => simp [List.foldl]; exact h_le
    | cons hd tl ih =>
      simp only [List.foldl]
      exact ih (f a hd) (f b hd) (h_mono_le a b hd h_le)

/-- 単調 foldl で member が 1以上寄与 → foldl ≥ 1 -/
private theorem foldl_mono_ge_of_mem {β : Type*} (l : List β) (f : Nat → β → Nat) (x : β)
        (h_mono : ∀ acc y, f acc y ≥ acc)
        (h_mono_le : ∀ acc₁ acc₂ y, acc₁ ≤ acc₂ → f acc₁ y ≤ f acc₂ y)
        (h_mem : x ∈ l) (h_pos : f 0 x ≥ 1) :
        l.foldl f 0 ≥ 1 := by
    induction l with
    | nil => simp at h_mem
    | cons hd tl ih =>
      simp only [List.foldl]
      cases h_mem with
      | head =>
        have h1 := foldl_mono_ge_init tl f (f 0 x) h_mono
        omega
      | tail _ hx =>
        have ih_result := ih hx
        calc 1 ≤ tl.foldl f 0 := ih_result
          _ ≤ tl.foldl f (f 0 hd) := foldl_mono_le_init tl f 0 (f 0 hd) (by omega) h_mono_le

/-- invCount = 0 → 全ペア (i, j) (i < j) で反転なし -/
private theorem invCount_zero_no_inv (l1 l2 : List FallingUnit)
        (h_inv : invCount l1 l2 = 0)
        (i j : Nat) (h_lt : i < j) (hi : i < l1.length) (hj : j < l1.length) :
        ¬(posIn l1[i] l2 > posIn l1[j] l2) := by
    intro h_pos
    -- invCount を展開
    simp only [invCount] at h_inv
    -- step 関数を抽出
    set f : Nat → Nat × Nat → Nat := fun acc ij =>
        if h₁ : ij.1 < l1.length then
            if h₂ : ij.2 < l1.length then
                if posIn l1[ij.1] l2 > posIn l1[ij.2] l2 then acc + 1 else acc
            else acc
        else acc
    -- f 0 (i,j) ≥ 1 (条件が true)
    have h_f_pos : f 0 (i, j) ≥ 1 := by
        show (if h₁ : i < l1.length then
            if h₂ : j < l1.length then
                if posIn l1[i] l2 > posIn l1[j] l2 then 0 + 1 else 0
            else 0
         else 0) ≥ 1
        simp only [hi, dite_true, hj, h_pos, ite_true]
        omega
    -- (i,j) ∈ pairs（do-notation は flatMap に展開）
    have h_mem : (i, j) ∈ (do
        let i ← List.range l1.length
        let j ← List.range l1.length
        if i < j then pure (i, j) else [] : List (Nat × Nat)) := by
        show (i, j) ∈ (List.range l1.length).flatMap fun a =>
            (List.range l1.length).flatMap fun b =>
                if a < b then [(a, b)] else []
        rw [List.mem_flatMap]
        refine ⟨i, List.mem_range.mpr hi, ?_⟩
        rw [List.mem_flatMap]
        refine ⟨j, List.mem_range.mpr hj, ?_⟩
        rw [if_pos h_lt]
        exact List.Mem.head _
    -- f は単調
    have h_mono : ∀ acc (y : Nat × Nat), f acc y ≥ acc := by
        intro acc y
        show (if h₁ : y.1 < l1.length then _ else acc) ≥ acc
        split
        · split
          · split <;> omega
          · omega
        · omega
    have h_mono_le : ∀ acc₁ acc₂ (y : Nat × Nat), acc₁ ≤ acc₂ → f acc₁ y ≤ f acc₂ y := by
        intro a1 a2 y h_le
        show (if h₁ : y.1 < l1.length then _ else a1) ≤ (if h₁ : y.1 < l1.length then _ else a2)
        split
        · rename_i h1
          show (if h₂ : y.2 < l1.length then _ else a1) ≤ (if h₂ : y.2 < l1.length then _ else a2)
          split
          · rename_i h2
            show (if posIn l1[y.1] l2 > posIn l1[y.2] l2 then a1 + 1 else a1) ≤
                 (if posIn l1[y.1] l2 > posIn l1[y.2] l2 then a2 + 1 else a2)
            split <;> omega
          · exact h_le
        · exact h_le
    -- foldl ≥ 1 なので h_inv (= 0) と矛盾
    have h_ge := foldl_mono_ge_of_mem _ f (i, j) h_mono h_mono_le h_mem h_f_pos
    omega

/-- NoDup 置換リストで反転数 0 → リスト等号。
    l1.Perm l2 かつ l1.Nodup のとき、invCount l1 l2 = 0 ならば l1 = l2。 -/
private theorem invCount_zero_imp_eq (l1 l2 : List FallingUnit)
        (h_perm : l1.Perm l2) (h_nodup : l1.Nodup) (h_inv : invCount l1 l2 = 0) :
        l1 = l2 := by
    -- NoDup 置換のリスト帰納法で証明
    -- l1 と l2 は同じ長さ（Perm から）
    have h_len := h_perm.length_eq
    -- リストの各要素が等しいことを示す
    apply List.ext_getElem h_len
    -- 強帰納法: posIn l1[k] l2 = k を示し、getElem_posIn から l1[k] = l2[k]
    intro k hk1 hk2
    -- l2 の NoDup
    have h_nodup2 : l2.Nodup := h_perm.nodup_iff.mp h_nodup
    -- posIn l1[m] l2 = m を強帰納法で示す
    suffices h_posIn_eq : ∀ (m : Nat) (hm : m < l1.length), posIn (l1[m]'hm) l2 = m by
        have h_mem : l1[k] ∈ l2 := h_perm.mem_iff.mp (List.getElem_mem hk1)
        have h_get := getElem_posIn l1[k] l2 h_mem
        simp only [h_posIn_eq k hk1] at h_get
        exact h_get.symm
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
    intro hm
    -- Step 1: posIn l1[m] l2 ≥ m
    have h_mem_m : l1[m] ∈ l2 := h_perm.mem_iff.mp (List.getElem_mem hm)
    have h_pos_lt : posIn l1[m] l2 < l2.length := posIn_lt_length l1[m] l2 h_mem_m
    have h_pos_lt1 : posIn l1[m] l2 < l1.length := by omega
    have h_ge : posIn l1[m] l2 ≥ m := by
        by_contra h_lt_m
        simp only [Nat.not_le] at h_lt_m
        -- posIn l1[m] l2 < m → ih gives posIn l1[posIn l1[m] l2] l2 = posIn l1[m] l2
        have h_pm := ih (posIn l1[m] l2) h_lt_m h_pos_lt1
        -- l1[posIn l1[m] l2] と l1[m] は posIn が同じ → l2 の NoDup で等しい要素
        have h_same := posIn_injective l2 h_nodup2
            (l1[posIn l1[m] l2]'h_pos_lt1) (l1[m])
            (h_perm.mem_iff.mp (List.getElem_mem h_pos_lt1))
            h_mem_m
            h_pm
        -- l1 の NoDup から posIn l1[m] l2 = m → 矛盾
        have := h_nodup.getElem_inj_iff (hi := h_pos_lt1) (hj := hm) |>.mp h_same
        omega
    -- Step 2: posIn l1[m] l2 ≤ m (背理法)
    by_contra h_ne
    have h_gt : posIn l1[m] l2 > m := by omega
    -- l2[m] ∈ l1 → ∃ m', l1[m'] = l2[m]
    have h_l2m_mem : l2[m]'(by omega) ∈ l1 :=
        h_perm.mem_iff.mpr (List.getElem_mem (by omega))
    obtain ⟨m', hm'_lt, hm'_eq⟩ := List.getElem_of_mem h_l2m_mem
    -- posIn l1[m'] l2 = posIn l2[m] l2 = m
    have h_posIn_m' : posIn l1[m'] l2 = m := by
        rw [hm'_eq]; exact posIn_getElem_self l2 h_nodup2 m (by omega)
    -- m' ≥ m (ih で j < m → posIn l1[j] l2 = j ≠ m)
    have h_m'_ge_m : m' ≥ m := by
        by_contra h_m'_lt
        simp only [Nat.not_le] at h_m'_lt
        have := ih m' h_m'_lt (by omega)
        omega
    -- m' ≠ m (l1[m'] = l2[m] だが posIn l1[m] l2 ≠ m)
    have h_m'_ne_m : m' ≠ m := by
        intro h_eq; subst h_eq
        -- l1[m] = l2[m] → posIn l1[m] l2 = m → 矛盾
        exact absurd h_posIn_m' h_ne
    -- m' > m → (m, m') は反転ペア
    exact invCount_zero_no_inv l1 l2 h_inv m m' (by omega) hm (by omega) (by omega)

/-- ∀ x ∈ l, f 0 x = 0 → l.foldl f 0 = 0（単調 f） -/
private theorem foldl_mono_all_zero {α : Type*} (l : List α) (f : Nat → α → Nat)
        (h_all : ∀ x ∈ l, f 0 x = 0) :
        l.foldl f 0 = 0 := by
    induction l with
    | nil => simp [List.foldl]
    | cons hd tl ih =>
      simp only [List.foldl]
      have h_f0 : f 0 hd = 0 := h_all hd List.mem_cons_self
      rw [h_f0]
      exact ih (fun x hx => h_all x (List.mem_cons_of_mem hd hx))

/-- 単調 foldl > 0 → 寄与する要素が存在する -/
private theorem foldl_mono_pos_exists {α : Type*} (l : List α) (f : Nat → α → Nat)
        (_h_mono : ∀ acc x, f acc x ≥ acc)
        (_h_mono_add : ∀ acc₁ acc₂ x, acc₁ ≤ acc₂ → f acc₁ x ≤ f acc₂ x)
        (h_pos : l.foldl f 0 > 0) :
        ∃ x ∈ l, f 0 x > 0 := by
    by_contra h_all
    push_neg at h_all
    have h_all' : ∀ x ∈ l, f 0 x = 0 := fun x hx => by have := h_all x hx; omega
    have h_fold_zero := foldl_mono_all_zero l f h_all'
    omega

/-- invCount > 0 → 反転ペアが存在する -/
private theorem exists_inv_of_invCount_pos (l1 l2 : List FallingUnit)
        (h_inv_pos : invCount l1 l2 > 0) :
        ∃ (i j : Nat) (hi : i < l1.length) (hj : j < l1.length),
            i < j ∧ posIn (l1[i]'hi) l2 > posIn (l1[j]'hj) l2 := by
    simp only [invCount] at h_inv_pos
    set f : Nat → Nat × Nat → Nat := fun acc ij =>
        if h₁ : ij.1 < l1.length then
            if h₂ : ij.2 < l1.length then
                if posIn l1[ij.1] l2 > posIn l1[ij.2] l2 then acc + 1 else acc
            else acc
        else acc
    have h_mono : ∀ acc (y : Nat × Nat), f acc y ≥ acc := by
        intro acc y; simp only [f]
        split <;> [split <;> [split <;> omega; omega]; omega]
    have h_mono_add : ∀ acc₁ acc₂ (y : Nat × Nat), acc₁ ≤ acc₂ → f acc₁ y ≤ f acc₂ y := by
        intro a1 a2 y h_le; simp only [f]
        split <;> [split <;> [split <;> omega; omega]; omega]
    obtain ⟨⟨i, j⟩, h_mem, h_f_pos⟩ := foldl_mono_pos_exists _ f h_mono h_mono_add h_inv_pos
    -- f 0 (i, j) > 0 を分解
    have h_f_val : f 0 (i, j) > 0 := h_f_pos
    simp only [f] at h_f_val
    split at h_f_val
    · rename_i h1
      split at h_f_val
      · rename_i h2
        split at h_f_val
        · rename_i h_inv
          -- i < j : (i,j) は pairs 内なので i < j
          have h_ij_lt : i < j := by
            -- h_mem : (i,j) ∈ pairs, pairs は i < j のペアのみ
            have h_flat : (i, j) ∈ (List.range l1.length).flatMap fun a =>
                (List.range l1.length).flatMap fun b =>
                    if a < b then [(a, b)] else [] := by
              -- do-notation は flatMap に展開される
              exact h_mem
            rw [List.mem_flatMap] at h_flat
            obtain ⟨a, _, ha⟩ := h_flat
            rw [List.mem_flatMap] at ha
            obtain ⟨b, _, hb⟩ := ha
            split at hb
            · rename_i h_lt; simp at hb; omega
            · simp at hb
          exact ⟨i, j, h1, h2, h_ij_lt, h_inv⟩
        · omega
      · omega
    · omega

/-- 反転ペアが存在 → 隣接反転ペアが存在する -/
private theorem exists_adj_inv_of_exists_inv (l1 l2 : List FallingUnit)
        (i j : Nat) (h_lt : i < j) (hi : i < l1.length) (hj : j < l1.length)
        (h_inv : posIn (l1[i]'hi) l2 > posIn (l1[j]'hj) l2) :
        ∃ (k : Nat) (hk : k + 1 < l1.length),
            posIn (l1[k]'(by omega)) l2 > posIn (l1[k + 1]'hk) l2 := by
    -- j - i に関する強帰納法
    -- 補助: gap = j - i による Nat.strongRecOn
    suffices h_suff : ∀ (gap : Nat) (i j : Nat) (h_lt : i < j) (hi : i < l1.length)
        (hj : j < l1.length) (h_gap : gap = j - i)
        (h_inv : posIn (l1[i]'hi) l2 > posIn (l1[j]'hj) l2),
        ∃ (k : Nat) (hk : k + 1 < l1.length),
            posIn (l1[k]'(by omega)) l2 > posIn (l1[k + 1]'hk) l2 by
        exact h_suff (j - i) i j h_lt hi hj rfl h_inv
    intro gap
    induction gap using Nat.strongRecOn with
    | ind gap ih =>
    intro i j h_lt hi hj h_gap h_inv
    by_cases h_adj : j = i + 1
    · exact ⟨i, by omega, by subst h_adj; exact h_inv⟩
    · by_cases h_mid : posIn (l1[i]'hi) l2 > posIn (l1[i + 1]'(by omega)) l2
      · exact ⟨i, by omega, h_mid⟩
      · have h_inv' : posIn (l1[i + 1]'(by omega)) l2 > posIn (l1[j]'hj) l2 := by omega
        exact ih (j - (i + 1)) (by omega) (i + 1) j (by omega) (by omega) hj rfl h_inv'

-- ========================================================================
-- invCount_adj_swap_lt の証明のためのヘルパー群
-- ========================================================================

-- σ: 位置 k と k+1 の転置
private def σ_ic (k m : Nat) : Nat :=
    if m = k then k + 1 else if m = k + 1 then k else m

private theorem σ_ic_invol (k m : Nat) : σ_ic k (σ_ic k m) = m := by
    simp only [σ_ic]
    split
    · split
      · omega
      · split <;> omega
    · split
      · split <;> omega
      · rfl

private theorem σ_ic_lt_of_lt (k m n : Nat) (hk : k + 1 < n) (hm : m < n) : σ_ic k m < n := by
    unfold σ_ic; split
    · omega
    · split <;> omega

private theorem σ_ic_preserves_lt (k : Nat) {i j : Nat} (h_lt : i < j)
        (h_ne : (i, j) ≠ (k, k + 1)) : σ_ic k i < σ_ic k j := by
    unfold σ_ic
    by_cases hi_k : i = k <;> by_cases hi_k1 : i = k + 1 <;>
        by_cases hj_k : j = k <;> by_cases hj_k1 : j = k + 1 <;>
        simp_all <;> omega

private theorem σ_ic_pair_ne (k : Nat) {i j : Nat} (h_lt : i < j)
        (_h_ne : (i, j) ≠ (k, k + 1)) : (σ_ic k i, σ_ic k j) ≠ (k, k + 1) := by
    intro h_eq
    have h1 := congr_arg Prod.fst h_eq
    have h2 := congr_arg Prod.snd h_eq
    simp only at h1 h2
    have hi_eq : i = k + 1 := by
        have := σ_ic_invol k i; rw [h1] at this
        simp only [σ_ic, ite_true] at this; exact this.symm
    have hj_eq : j = k := by
        have := σ_ic_invol k j; rw [h2] at this
        simp only [σ_ic, show ¬(k + 1 = k) from by omega, ite_false, ite_true] at this
        exact this.symm
    omega

-- pairsList: (i,j) ペアのリスト (i < j < n)
private def pairsList_ic (n : Nat) : List (Nat × Nat) :=
    (List.range n).flatMap fun i =>
        (List.range n).flatMap fun j =>
            if i < j then [(i, j)] else []

private theorem mem_pairsList_ic {n : Nat} {p : Nat × Nat} :
        p ∈ pairsList_ic n ↔ p.1 < n ∧ p.2 < n ∧ p.1 < p.2 := by
    constructor
    · intro hp
      simp only [pairsList_ic, List.mem_flatMap, List.mem_range] at hp
      obtain ⟨a, ha, b, hb, h3⟩ := hp
      by_cases hab : a < b
      · simp only [hab, ite_true, List.mem_singleton] at h3
        obtain ⟨h_fst, h_snd⟩ := Prod.mk.inj h3
        exact ⟨h_fst ▸ ha, h_snd ▸ hb, h_fst ▸ h_snd ▸ hab⟩
      · simp only [hab, ite_false, List.not_mem_nil] at h3
    · rintro ⟨h1, h2, h_lt⟩
      show p ∈ (List.range n).flatMap _
      rw [List.mem_flatMap]
      refine ⟨p.1, List.mem_range.mpr h1, ?_⟩
      rw [List.mem_flatMap]
      refine ⟨p.2, List.mem_range.mpr h2, ?_⟩
      simp [h_lt]

private theorem pairsList_ic_nodup (n : Nat) : (pairsList_ic n).Nodup := by
    simp only [pairsList_ic]
    refine List.nodup_flatMap.mpr ⟨?_, ?_⟩
    · intro i _
      refine List.nodup_flatMap.mpr ⟨?_, ?_⟩
      · intro j _
        by_cases hij : i < j
        · simp only [hij, ite_true]; exact List.nodup_singleton _
        · simp only [hij, ite_false]; exact List.nodup_nil
      · exact List.nodup_range.pairwise_of_forall_ne (fun j1 hj1 j2 hj2 hne => by
          simp only [Function.onFun, List.disjoint_left]
          intro a ha1 ha2
          by_cases h1 : i < j1 <;> by_cases h2 : i < j2
          · simp only [h1, ite_true, List.mem_singleton] at ha1
            simp only [h2, ite_true, List.mem_singleton] at ha2
            exact absurd (by rw [ha1] at ha2; exact (Prod.mk.inj ha2).2) hne
          · simp only [h2, ite_false, List.not_mem_nil] at ha2
          · simp only [h1, ite_false, List.not_mem_nil] at ha1
          · simp only [h1, ite_false, List.not_mem_nil] at ha1)
    · exact List.nodup_range.pairwise_of_forall_ne (fun i1 hi1 i2 hi2 hne => by
        simp only [Function.onFun, List.disjoint_left]
        intro a ha1 ha2
        simp only [List.mem_flatMap, List.mem_range] at ha1 ha2
        obtain ⟨j1, _, hj1⟩ := ha1
        obtain ⟨j2, _, hj2⟩ := ha2
        by_cases h1 : i1 < j1 <;> by_cases h2 : i2 < j2
        · simp only [h1, ite_true, List.mem_singleton] at hj1
          simp only [h2, ite_true, List.mem_singleton] at hj2
          exact absurd (by rw [hj1] at hj2; exact (Prod.mk.inj hj2).1) hne
        · simp only [h2, ite_false, List.not_mem_nil] at hj2
        · simp only [h1, ite_false, List.not_mem_nil] at hj1
        · simp only [h1, ite_false, List.not_mem_nil] at hj1)

-- σ_pair: σ をペアに適用
private def σ_pair_ic (k : Nat) (p : Nat × Nat) : Nat × Nat := (σ_ic k p.1, σ_ic k p.2)

private theorem σ_pair_ic_invol (k : Nat) (p : Nat × Nat) : σ_pair_ic k (σ_pair_ic k p) = p := by
    simp only [σ_pair_ic, σ_ic_invol]

private theorem σ_pair_ic_injective (k : Nat) : Function.Injective (σ_pair_ic k) := by
    intro a b h
    have := congr_arg (σ_pair_ic k) h
    rwa [σ_pair_ic_invol, σ_pair_ic_invol] at this

-- foldl ヘルパー
private theorem rc_add_f_ic (f : Nat × Nat → Nat) :
        RightCommutative (fun (acc : Nat) (a : Nat × Nat) => acc + f a) :=
    ⟨fun a b c => by omega⟩

private theorem foldl_add_init_ic (l : List (Nat × Nat)) (f : Nat × Nat → Nat) (init : Nat) :
        l.foldl (fun acc a => acc + f a) init =
        init + l.foldl (fun acc a => acc + f a) 0 := by
    induction l generalizing init with
    | nil => simp [List.foldl]
    | cons x xs ih =>
        simp only [List.foldl]
        rw [ih (init + f x), ih (0 + f x)]
        omega

private theorem foldl_add_extract_ic (l : List (Nat × Nat)) (f : Nat × Nat → Nat)
        (x : Nat × Nat) (hx : x ∈ l) (_hnd : l.Nodup) :
        l.foldl (fun acc a => acc + f a) 0 =
        f x + (l.erase x).foldl (fun acc a => acc + f a) 0 := by
    have hperm := List.perm_cons_erase hx
    rw [hperm.foldl_eq (rcomm := rc_add_f_ic f) 0]
    simp only [List.foldl, Nat.zero_add]
    exact foldl_add_init_ic _ f (f x)

private theorem pairFoldl_split_ic (n k : Nat) (v : Nat × Nat → Nat)
        (hk : k + 1 < n) :
        (pairsList_ic n).foldl (fun acc p => acc + v p) 0 = v (k, k + 1) +
        ((pairsList_ic n).erase (k, k + 1)).foldl (fun acc p => acc + v p) 0 :=
    foldl_add_extract_ic (pairsList_ic n) v (k, k + 1)
        (mem_pairsList_ic.mpr ⟨by omega, hk, by omega⟩) (pairsList_ic_nodup n)

private theorem mem_erase_nodup_ic {l : List (Nat × Nat)} {a x : Nat × Nat}
        (hnd : l.Nodup) (h : x ∈ l.erase a) : x ∈ l ∧ x ≠ a :=
    ⟨List.mem_of_mem_erase h, fun heq => by subst heq; exact hnd.not_mem_erase h⟩

private theorem foldl_σ_reindex_ic (n k : Nat) (v : Nat × Nat → Nat) (hk : k + 1 < n) :
        ((pairsList_ic n).erase (k, k + 1)).foldl (fun acc p => acc + v (σ_pair_ic k p)) 0 =
        ((pairsList_ic n).erase (k, k + 1)).foldl (fun acc p => acc + v p) 0 := by
    have hnd := pairsList_ic_nodup n
    have h_nodup_erase := hnd.erase (k, k + 1)
    have h_map_nodup := List.Nodup.map (σ_pair_ic_injective k) h_nodup_erase
    have h_perm : ((pairsList_ic n).erase (k, k + 1)).map (σ_pair_ic k) |>.Perm
            ((pairsList_ic n).erase (k, k + 1)) := by
        rw [List.perm_ext_iff_of_nodup h_map_nodup h_nodup_erase]
        intro x
        simp only [List.mem_map]
        constructor
        · rintro ⟨a, ha_mem, ha_eq⟩
          rw [← ha_eq]
          have ⟨ha_in, ha_ne⟩ := mem_erase_nodup_ic hnd ha_mem
          rw [mem_pairsList_ic] at ha_in
          exact (List.mem_erase_of_ne (σ_ic_pair_ne k ha_in.2.2 ha_ne)).mpr
              (mem_pairsList_ic.mpr ⟨σ_ic_lt_of_lt k a.1 n hk ha_in.1,
                   σ_ic_lt_of_lt k a.2 n hk ha_in.2.1,
                   σ_ic_preserves_lt k ha_in.2.2 ha_ne⟩)
        · intro hx_mem
          have ⟨hx_in, hx_ne⟩ := mem_erase_nodup_ic hnd hx_mem
          rw [mem_pairsList_ic] at hx_in
          refine ⟨σ_pair_ic k x, ?_, σ_pair_ic_invol k x⟩
          apply (List.mem_erase_of_ne ?_).mpr
          · rw [mem_pairsList_ic]; simp only [σ_pair_ic]
            exact ⟨σ_ic_lt_of_lt k x.1 n hk hx_in.1,
                   σ_ic_lt_of_lt k x.2 n hk hx_in.2.1,
                   σ_ic_preserves_lt k hx_in.2.2 hx_ne⟩
          · intro h_eq
            have h_inv := σ_pair_ic_invol k x
            rw [h_eq] at h_inv
            simp only [σ_pair_ic, σ_ic, ite_true, show ¬(k + 1 = k) from by omega, ite_false] at h_inv
            have := hx_in.2.2
            rw [← h_inv] at this
            simp at this; omega
    set erase_list := (pairsList_ic n).erase (k, k + 1)
    have h_eq : erase_list.foldl (fun acc p => acc + v (σ_pair_ic k p)) 0 =
        (erase_list.map (σ_pair_ic k)).foldl (fun acc p => acc + v p) 0 :=
        (List.foldl_map (f := σ_pair_ic k) (g := fun acc p => acc + v p)).symm
    rw [h_eq]
    exact h_perm.foldl_eq (rcomm := rc_add_f_ic v) 0

private theorem foldl_add_congr_ic (l : List (Nat × Nat)) (f g : Nat × Nat → Nat)
        (h : ∀ x ∈ l, f x = g x) :
        l.foldl (fun acc p => acc + f p) 0 = l.foldl (fun acc p => acc + g p) 0 := by
    induction l with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.foldl]
        have h_eq := h x List.mem_cons_self
        rw [h_eq]
        rw [foldl_add_init_ic xs f (0 + g x), foldl_add_init_ic xs g (0 + g x)]
        congr 1
        exact ih (fun y hy => h y (List.mem_cons_of_mem x hy))

private theorem pairFoldl_decrease_ic (n k : Nat) (v v' : Nat × Nat → Nat)
        (hk : k + 1 < n)
        (h_old_kk : v (k, k + 1) ≥ 1)
        (h_new_kk : v' (k, k + 1) = 0)
        (h_other : ∀ p ∈ (pairsList_ic n).erase (k, k + 1),
            v' p = v (σ_pair_ic k p)) :
        (pairsList_ic n).foldl (fun acc p => acc + v' p) 0 <
        (pairsList_ic n).foldl (fun acc p => acc + v p) 0 := by
    rw [pairFoldl_split_ic n k v hk, pairFoldl_split_ic n k v' hk]
    rw [h_new_kk]; simp only [Nat.zero_add]
    have h_erase_eq : ((pairsList_ic n).erase (k, k + 1)).foldl (fun acc p => acc + v' p) 0 =
        ((pairsList_ic n).erase (k, k + 1)).foldl (fun acc p => acc + v (σ_pair_ic k p)) 0 :=
        foldl_add_congr_ic _ _ _ h_other
    rw [h_erase_eq, foldl_σ_reindex_ic n k v hk]
    omega

-- ========================================================================
-- invCount → pairsFoldl ブリッジ
-- ========================================================================

-- swap list の長さ保存
private theorem swap_length_ic (l : List FallingUnit) (k : Nat) (hk : k + 1 < l.length) :
        (l.take k ++ l[k + 1]'hk :: l[k]'(by omega) :: l.drop (k + 2)).length =
        l.length := by
    simp only [List.length_append, List.length_take, List.length_cons, List.length_drop]
    omega

-- getElem_swap: m < k
private theorem getElem_swap_lt_ic (l : List FallingUnit) (k m : Nat)
        (hk : k + 1 < l.length) (hm : m < l.length) (h : m < k) :
        (l.take k ++ l[k + 1]'hk :: l[k]'(by omega) :: l.drop (k + 2))[m]'(by
            rw [swap_length_ic]; exact hm) =
        l[m]'hm := by
    have h_take_bound : m < (l.take k).length := by
        rw [List.length_take_of_le (by omega)]; exact h
    simp only [List.getElem_append_left h_take_bound, List.getElem_take]

-- getElem_swap: m = k → l[k+1]
private theorem getElem_swap_eq_ic (l : List FallingUnit) (k : Nat)
        (hk : k + 1 < l.length) :
        (l.take k ++ l[k + 1]'hk :: l[k]'(by omega) :: l.drop (k + 2))[k]'(by
            rw [swap_length_ic]; omega) =
        l[k + 1]'hk := by
    have h_tk : (l.take k).length = k := List.length_take_of_le (by omega)
    have h_ge : (l.take k).length ≤ k := by omega
    rw [List.getElem_append_right h_ge]
    simp only [h_tk, Nat.sub_self]
    rfl

-- getElem_swap: m = k+1 → l[k]
private theorem getElem_swap_eq_succ_ic (l : List FallingUnit) (k : Nat)
        (hk : k + 1 < l.length) :
        (l.take k ++ l[k + 1]'hk :: l[k]'(by omega) :: l.drop (k + 2))[k + 1]'(by
            rw [swap_length_ic]; exact hk) =
        l[k]'(by omega) := by
    have h_tk : (l.take k).length = k := List.length_take_of_le (by omega)
    have h_ge : (l.take k).length ≤ k + 1 := by omega
    rw [List.getElem_append_right h_ge]
    simp only [h_tk, show k + 1 - k = 1 from by omega]
    rfl

-- getElem_swap: m > k+1 → l[m]
private theorem getElem_swap_gt_ic (l : List FallingUnit) (k m : Nat)
        (hk : k + 1 < l.length) (hm : m < l.length) (h : m > k + 1) :
        (l.take k ++ l[k + 1]'hk :: l[k]'(by omega) :: l.drop (k + 2))[m]'(by
            rw [swap_length_ic]; exact hm) =
        l[m]'hm := by
    rw [List.getElem_append]
    have h_not_lt : ¬(m < (List.take k l).length) := by
        rw [List.length_take_of_le (by omega)]; omega
    simp only [h_not_lt, dite_false]
    set len := (List.take k l).length
    have hlen_eq : len = k := List.length_take_of_le (by omega)
    rw [List.getElem_cons]; split; · omega
    rw [List.getElem_cons]; split; · omega
    rw [List.getElem_drop]; congr 1; omega

-- invContrib: ペア (i,j) の反転数への寄与
private def invContrib_ic (l1 l2 : List FallingUnit) (p : Nat × Nat) : Nat :=
    if h₁ : p.1 < l1.length then
        if h₂ : p.2 < l1.length then
            if posIn l1[p.1] l2 > posIn l1[p.2] l2 then 1 else 0
        else 0
    else 0

-- invCount の foldl body = acc + invContrib
private theorem invBody_eq_add_ic (l1 l2 : List FallingUnit)
        (acc : Nat) (p : Nat × Nat) :
        (fun acc (p : Nat × Nat) =>
            if h₁ : p.1 < l1.length then
                if h₂ : p.2 < l1.length then
                    if posIn l1[p.1] l2 > posIn l1[p.2] l2 then acc + 1 else acc
                else acc
            else acc) acc p =
        acc + invContrib_ic l1 l2 p := by
    simp only [invContrib_ic]
    split
    · split
      · split <;> omega
      · omega
    · omega

-- invCount = pairsList_ic(n).foldl(+invContrib)
private theorem invCount_eq_pairsFoldl_ic (l1 l2 : List FallingUnit) :
        invCount l1 l2 =
        (pairsList_ic l1.length).foldl (fun acc p => acc + invContrib_ic l1 l2 p) 0 := by
    unfold invCount
    set body := fun acc (p : Nat × Nat) =>
        if h₁ : p.1 < l1.length then
            if h₂ : p.2 < l1.length then
                if posIn l1[p.1] l2 > posIn l1[p.2] l2 then acc + 1 else acc
            else acc
        else acc
    suffices ∀ (init : Nat) (l : List (Nat × Nat)),
        l.foldl body init = l.foldl (fun acc p => acc + invContrib_ic l1 l2 p) init from
        this 0 _
    intro init l
    induction l generalizing init with
    | nil => rfl
    | cons p ps ih =>
        simp only [List.foldl]
        have h_eq : body init p = init + invContrib_ic l1 l2 p := by
            simp only [body, invContrib_ic]
            split
            · split
              · split <;> omega
              · omega
            · omega
        rw [h_eq]
        exact ih _

-- getElem_swap: σ_ic で統合
private theorem getElem_swap_σ_ic (l : List FallingUnit) (k m : Nat)
        (hk : k + 1 < l.length) (hm : m < l.length) :
        (l.take k ++ l[k + 1]'hk :: l[k]'(by omega) :: l.drop (k + 2))[m]'(by
            rw [swap_length_ic]; exact hm) =
        l[σ_ic k m]'(σ_ic_lt_of_lt k m l.length hk hm) := by
    by_cases h1 : m < k
    · have hσ : σ_ic k m = m := by
          simp [σ_ic, show m ≠ k from by omega, show m ≠ k + 1 from by omega]
      simp only [hσ]; exact getElem_swap_lt_ic l k m hk hm h1
    · by_cases h2 : m = k
      · -- σ_ic k m = k + 1, m = k → l'[m] = l'[k] = l[k+1]
        have hσ : σ_ic k m = k + 1 := by simp [σ_ic, h2]
        simp only [hσ]
        have := getElem_swap_eq_ic l k hk
        exact h2 ▸ this
      · by_cases h3 : m = k + 1
        · have hσ : σ_ic k m = k := by
              simp [σ_ic, h3]
          simp only [hσ]
          have := getElem_swap_eq_succ_ic l k hk
          exact h3 ▸ this
        · have hσ : σ_ic k m = m := by
              simp [σ_ic, show m ≠ k from h2, show m ≠ k + 1 from h3]
          simp only [hσ]; exact getElem_swap_gt_ic l k m hk hm (by omega)

/-- 核心: 隣接反転 swap で invCount が真に減少する。

    戦略: invCount は pairs 上の foldl(条件付き+1)。
    swap k↔k+1 は v(m) = posIn(l1[m], l2) に対して v∘σ に変換。
    各ペア (i,j) with i<j について:
    - (i,j) ≠ (k,k+1) → σi < σj なので同じペアへの全単射(対合)
    - (i,j) = (k,k+1) → 反転から非反転へ (寄与 -1)
    合計: invCount(l1') = invCount(l1) - 1 -/
private theorem invCount_adj_swap_lt (l1 l2 : List FallingUnit)
        (_h_perm : l1.Perm l2) (_h_nodup : l1.Nodup)
        (k : Nat) (hk : k + 1 < l1.length)
        (h_inv_k : posIn (l1[k]'(by omega)) l2 > posIn (l1[k + 1]'hk) l2) :
        invCount (l1.take k ++ l1[k + 1]'hk :: l1[k]'(by omega) :: l1.drop (k + 2)) l2 <
            invCount l1 l2 := by
    set l1' := l1.take k ++ l1[k + 1]'hk :: l1[k]'(by omega) :: l1.drop (k + 2)
    set n := l1.length
    have hl1'_len : l1'.length = n := swap_length_ic l1 k hk
    -- invCount を pairsFoldl に変換
    rw [invCount_eq_pairsFoldl_ic l1 l2, invCount_eq_pairsFoldl_ic l1' l2]
    -- l1'.length = n なので pairsList_ic l1'.length = pairsList_ic n
    rw [hl1'_len]
    -- pairFoldl_decrease_ic を適用
    apply pairFoldl_decrease_ic n k (invContrib_ic l1 l2) (invContrib_ic l1' l2) hk
    -- h_old_kk: invContrib l1 l2 (k, k+1) ≥ 1
    · simp only [invContrib_ic, show k < l1.length from by omega, dite_true,
                  show k + 1 < l1.length from hk]
      split
      · omega
      · omega
    -- h_new_kk: invContrib l1' l2 (k, k+1) = 0
    · have h_eq_k : l1'[k]'(by omega) = l1[k + 1]'hk :=
          getElem_swap_eq_ic l1 k hk
      have h_eq_k1 : l1'[k + 1]'(by omega) = l1[k]'(by omega) :=
          getElem_swap_eq_succ_ic l1 k hk
      simp only [invContrib_ic, show k < l1'.length from by omega, dite_true,
                  show k + 1 < l1'.length from by omega, h_eq_k, h_eq_k1]
      split
      · omega
      · rfl
    -- h_other: ∀ p ∈ erase, invContrib l1' l2 p = invContrib l1 l2 (σ_pair_ic k p)
    · intro p hp
      have ⟨hp_in, hp_ne⟩ := mem_erase_nodup_ic (pairsList_ic_nodup n) hp
      rw [mem_pairsList_ic] at hp_in
      -- l1'[p.i] を l1[σ_ic k p.i] に書き換え
      have h_eq1 : l1'[p.1]'(by omega) = l1[σ_ic k p.1]'(σ_ic_lt_of_lt k p.1 n hk hp_in.1) :=
          getElem_swap_σ_ic l1 k p.1 hk (by omega)
      have h_eq2 : l1'[p.2]'(by omega) = l1[σ_ic k p.2]'(σ_ic_lt_of_lt k p.2 n hk hp_in.2.1) :=
          getElem_swap_σ_ic l1 k p.2 hk (by omega)
      simp only [invContrib_ic, σ_pair_ic,
                  show p.1 < l1'.length from by omega, dite_true,
                  show p.2 < l1'.length from by omega,
                  show (σ_ic k p.1) < l1.length from σ_ic_lt_of_lt k p.1 n hk hp_in.1,
                  show (σ_ic k p.2) < l1.length from σ_ic_lt_of_lt k p.2 n hk hp_in.2.1,
                  h_eq1, h_eq2]
      -- bound proof の proof irrelevance で残るゴールを閉じる
      congr 1

/-- 反転数 > 0 → 隣接反転ペアが存在し、そのスワップで反転数が減少する -/
private theorem exists_adj_inv_swap (l1 l2 : List FallingUnit)
        (h_perm : l1.Perm l2) (h_nodup : l1.Nodup)
        (h_inv_pos : invCount l1 l2 > 0) :
        ∃ (k : Nat) (hk : k + 1 < l1.length),
            posIn (l1[k]'(by omega)) l2 > posIn (l1[k + 1]'hk) l2 ∧
            invCount (l1.take k ++ l1[k + 1]'hk :: l1[k]'(by omega) :: l1.drop (k + 2)) l2 <
                invCount l1 l2 := by
    -- 1. 反転ペアを取り出す
    obtain ⟨i, j, hi, hj, h_lt_ij, h_inv_ij⟩ := exists_inv_of_invCount_pos l1 l2 h_inv_pos
    -- 2. 隣接反転ペアを見つける
    obtain ⟨k, hk, h_inv_k⟩ := exists_adj_inv_of_exists_inv l1 l2 i j h_lt_ij hi hj h_inv_ij
    -- 3. invCount が減少する
    exact ⟨k, hk, h_inv_k, invCount_adj_swap_lt l1 l2 h_perm h_nodup k hk h_inv_k⟩

/-- 隣接 swap は Perm を保存する -/
private theorem adj_swap_perm (l : List FallingUnit) (k : Nat) (hk : k + 1 < l.length) :
        (l.take k ++ l[k + 1]'hk :: l[k]'(by omega) :: l.drop (k + 2)).Perm l := by
    set a := l[k]'(by omega) with ha_def
    set b := l[k + 1]'hk with hb_def
    set prefix_ := l.take k with hpre_def
    set suffix_ := l.drop (k + 2) with hsuf_def
    -- l = prefix_ ++ [a, b] ++ suffix_
    have h_split : l = prefix_ ++ a :: b :: suffix_ := by
        simp only [hpre_def, ha_def, hb_def, hsuf_def]
        conv_lhs => rw [← List.take_append_drop k l]
        have h_dk : l.drop k = l[k]'(by omega) :: l.drop (k + 1) :=
            (List.cons_getElem_drop_succ (h := by omega)).symm
        have h_dk1 : l.drop (k + 1) = l[k + 1]'hk :: l.drop (k + 2) :=
            (List.cons_getElem_drop_succ (h := hk)).symm
        rw [h_dk, h_dk1]
    -- Perm.trans で2段階
    have h1 : (prefix_ ++ b :: a :: suffix_).Perm (prefix_ ++ a :: b :: suffix_) := by
        apply List.Perm.append_left
        exact List.Perm.swap a b suffix_
    have h2 : (prefix_ ++ a :: b :: suffix_) = l := h_split.symm
    rw [h2] at h1
    exact h1

/-- バブルソートの核心: 反転がある隣接ペアが tied (方角素) なら
    swap しても foldl は不変。繰り返しにより l1.foldl = l2.foldl -/
private theorem foldl_eq_of_perm_tied_adj_comm (s : Shape)
        (l1 l2 : List FallingUnit) (obs : List Layer)
        (h_perm : l1.Perm l2) (h_nodup : l1.Nodup)
        (h_tied_comm : ∀ (i j : Nat) (hi : i < l1.length) (hj : j < l1.length),
            i < j →
            posIn (l1[i]'hi) l2 > posIn (l1[j]'hj) l2 →
            -- 反転ペアは方角素 (foldl 可換)
            (∀ p, p ∈ (l1[i]'hi).positions →
                (l1[j]'hj).positions.any (fun q => q.dir == p.dir) = false) ∧
            (∀ p, p ∈ (l1[j]'hj).positions →
                (l1[i]'hi).positions.any (fun q => q.dir == p.dir) = false)) :
        l1.foldl (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs =
        l2.foldl (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs := by
    -- invCount l1 l2 による強帰納法
    -- invCount = 0 → l1 = l2 → trivial
    -- invCount > 0 → 隣接反転存在 → swap で反転数減少 + foldl 不変 → IH
    suffices h : ∀ (n : Nat) (l1' : List FallingUnit),
        invCount l1' l2 = n →
        l1'.Perm l2 → l1'.Nodup →
        (∀ (i j : Nat) (hi : i < l1'.length) (hj : j < l1'.length),
            i < j →
            posIn (l1'[i]'hi) l2 > posIn (l1'[j]'hj) l2 →
            (∀ p, p ∈ (l1'[i]'hi).positions →
                (l1'[j]'hj).positions.any (fun q => q.dir == p.dir) = false) ∧
            (∀ p, p ∈ (l1'[j]'hj).positions →
                (l1'[i]'hi).positions.any (fun q => q.dir == p.dir) = false)) →
        l1'.foldl (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs =
        l2.foldl (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs by
      exact h (invCount l1 l2) l1 rfl h_perm h_nodup h_tied_comm
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro l1' h_inv h_perm' h_nodup' h_tied_comm'
      by_cases h_zero : invCount l1' l2 = 0
      · -- 反転数 0 → l1' = l2
        have h_eq := invCount_zero_imp_eq l1' l2 h_perm' h_nodup' h_zero
        rw [h_eq]
      · -- 反転数 > 0 → 隣接反転存在
        have h_pos : invCount l1' l2 > 0 := by omega
        obtain ⟨k, hk, h_inv_k, h_inv_dec⟩ := exists_adj_inv_swap l1' l2 h_perm' h_nodup' h_pos
        -- swap 後のリスト
        set l1'' := l1'.take k ++ l1'[k + 1]'hk :: l1'[k]'(by omega) :: l1'.drop (k + 2) with hl1''_def
        -- swap は foldl を保存 (l1'[k] と l1'[k+1] は方角素)
        have h_dirDisj := h_tied_comm' k (k + 1) (by omega) hk (by omega) h_inv_k
        -- l1'.foldl = l1''.foldl (隣接方角素ペアの swap)
        have h_foldl_eq : l1'.foldl (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs =
            l1''.foldl (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs := by
            -- l1' = take k ++ [l1'[k], l1'[k+1]] ++ drop (k+2)
            have h_split : l1' = l1'.take k ++ l1'[k]'(by omega) :: l1'[k + 1]'hk :: l1'.drop (k + 2) := by
                conv_lhs => rw [← List.take_append_drop k l1']
                rw [(List.cons_getElem_drop_succ (h := by omega)).symm,
                    (List.cons_getElem_drop_succ (h := hk)).symm]
            -- l1'' は swap 版
            -- foldl_settle_swap_at で等価
            conv_lhs => rw [h_split]
            exact foldl_settle_swap_at s (l1'.take k) (l1'[k]'(by omega)) (l1'[k + 1]'hk) (l1'.drop (k + 2)) obs
                h_dirDisj.1 h_dirDisj.2
        -- l1'' は l2 の Perm
        have h_perm'' : l1''.Perm l2 :=
            (adj_swap_perm l1' k hk).trans h_perm'
        -- l1'' は NoDup
        have h_nodup'' : l1''.Nodup :=
            (adj_swap_perm l1' k hk).nodup_iff.mpr h_nodup'
        -- l1'' の反転ペアも方角素 (swap 置換で l1' に帰着)
        -- l1'' と l1' は位置 k, k+1 のみ異なる。i < j かつ反転 → σ(i) < σ(j) を示し h_tied_comm' に帰着。
        have h_len_eq : l1''.length = l1'.length :=
            (adj_swap_perm l1' k hk).length_eq
        have h_tied_comm'' : ∀ (i j : Nat) (hi : i < l1''.length) (hj : j < l1''.length),
            i < j →
            posIn (l1''[i]'hi) l2 > posIn (l1''[j]'hj) l2 →
            (∀ p, p ∈ (l1''[i]'hi).positions →
                (l1''[j]'hj).positions.any (fun q => q.dir == p.dir) = false) ∧
            (∀ p, p ∈ (l1''[j]'hj).positions →
                (l1''[i]'hi).positions.any (fun q => q.dir == p.dir) = false) := by
            intro i j hi hj h_lt_ij h_inv_ij
            -- l1'' の各要素は l1' にも含まれる (Perm)
            have h_mem_i : l1''[i]'hi ∈ l1' :=
                (adj_swap_perm l1' k hk).subset (List.getElem_mem hi)
            have h_mem_j : l1''[j]'hj ∈ l1' :=
                (adj_swap_perm l1' k hk).subset (List.getElem_mem hj)
            -- l1''[i] ≠ l1''[j] (NoDup + i < j)
            have h_ne_ij : i ≠ j := Nat.ne_of_lt h_lt_ij
            have h_ne_elem : l1''[i]'hi ≠ l1''[j]'hj :=
                fun h => h_ne_ij (h_nodup''.getElem_inj_iff.mp h)
            -- σ mapping: l1''[m] = l1'[σ(m)] where σ swaps k ↔ k+1
            -- l1' のインデックスに変換
            obtain ⟨i', hi', h_eq_i⟩ := List.mem_iff_getElem.mp h_mem_i
            obtain ⟨j', hj', h_eq_j⟩ := List.mem_iff_getElem.mp h_mem_j
            -- i' ≠ j'
            have h_ne_ij' : i' ≠ j' := by
                intro h_eq; apply h_ne_elem
                exact h_eq_i.symm.trans ((h_nodup'.getElem_inj_iff.mpr h_eq).trans h_eq_j)
            -- posIn の反転条件を l1' に変換
            have h_inv' : posIn (l1'[i']'hi') l2 > posIn (l1'[j']'hj') l2 := by
                rw [congrArg (posIn · l2) h_eq_i, congrArg (posIn · l2) h_eq_j]; exact h_inv_ij
            -- i' < j' を示す
            -- i' > j' と仮定すると矛盾: swap で唯一の順序反転は (k,k+1)→(k+1,k)
            -- → i=k, j=k+1, i'=k+1, j'=k → posIn 反転が h_inv_k と矛盾
            have h_lt_ij' : i' < j' := by
                by_contra h_not_lt
                have h_ge := Nat.le_of_not_lt h_not_lt
                have h_gt : i' > j' := by omega
                -- j' < i' → l1' で j' が前、i' が後
                -- l1''[i] = l1'[i'] で l1''[j] = l1'[j']
                -- swap は k ↔ k+1 のみ順序反転 → i' > j' かつ i < j (l1'') は
                -- (i,j) = (k, k+1) かつ (i', j') = (k+1, k) のときのみ
                -- この場合: posIn(l1'[k+1], l2) > posIn(l1'[k], l2) ← h_inv'
                -- 一方 h_inv_k: posIn(l1'[k], l2) > posIn(l1'[k+1], l2) → 矛盾
                -- まず l1''[i] = l1'[i'] を使って NoDup で l1'' 内の位置を一意に特定
                -- NoDup l1' + NoDup l1'' で i' は l1''[i] の l1' 内位置
                -- swap 置換: l1''[m] = l1'[σ(m)] を使う
                -- σ(i) = i' を示す代わりに、i' > j' の矛盾は以下で導ける:
                -- l1'[j'] = l1''[j] ∈ l1' かつ l1'[i'] = l1''[i] ∈ l1'
                -- i < j かつ i' > j' → swap で (j', i') が (i, j) に移動
                -- NoDup リストの swap k↔k+1 で「入れ替わる」のは位置 k と k+1 のみ
                -- 位置 m ∉ {k, k+1} は l1''[m] = l1'[m]
                -- よって i ∈ {k, k+1} かつ j ∈ {k, k+1} でないと i' > j' で i < j にならない
                -- i < j, i ∈ {k, k+1}, j ∈ {k, k+1} → i = k, j = k+1
                -- l1''[k] = l1'[k+1], l1''[k+1] = l1'[k]
                -- → i' = k+1, j' = k (by NoDup)
                -- → h_inv' : posIn(l1'[k+1], l2) > posIn(l1'[k], l2)
                -- → h_inv_k : posIn(l1'[k], l2) > posIn(l1'[k+1], l2)
                -- → omega
                -- 背理法の核心: i ∈ {k, k+1} を示す
                -- m ∉ {k, k+1} → l1''[m] = l1'[m] (swap 不変)
                -- → i' = i (NoDup) で同様に j' = j → i' > j' は i > j → i < j に矛盾
                by_cases hi_k : i = k
                · by_cases hj_k1 : j = k + 1
                  · -- i = k, j = k+1 → l1''[k] = l1'[k+1], l1''[k+1] = l1'[k]
                    -- → posIn 矛盾 with h_inv_k
                    have h_l1''_k : l1''[k]'(by rw [h_len_eq]; omega) = l1'[k+1]'hk := by
                        simp only [hl1''_def]
                        rw [List.getElem_append_right (by simp [List.length_take])]
                        simp only [List.length_take, Nat.min_eq_left (by omega : k ≤ l1'.length),
                            Nat.sub_self, List.getElem_cons_zero]
                    have h_l1''_k1 : l1''[k+1]'(by rw [h_len_eq]; omega) = l1'[k]'(by omega) := by
                        simp only [hl1''_def]
                        rw [List.getElem_append_right (by simp [List.length_take])]
                        simp only [List.length_take, Nat.min_eq_left (by omega : k ≤ l1'.length),
                            show k + 1 - k = 1 from by omega,
                            List.getElem_cons_succ, List.getElem_cons_zero]
                    have h_l1''_i : l1''[i]'hi = l1'[k+1]'hk := by
                        have : i = k := hi_k; subst this; exact h_l1''_k
                    have h_l1''_j : l1''[j]'hj = l1'[k]'(by omega) := by
                        have : j = k + 1 := hj_k1; subst this; exact h_l1''_k1
                    rw [h_l1''_i, h_l1''_j] at h_inv_ij
                    omega
                  · -- i = k, j ≠ k+1 → j > k+1 (because i < j and i = k)
                    -- l1''[j] = l1'[j] (j ∉ {k, k+1})
                    have hj_gt : j > k + 1 := by omega
                    have h_l1''_j : l1''[j]'hj = l1'[j]'(by rw [h_len_eq] at hj; exact hj) := by
                        simp only [hl1''_def]
                        rw [List.getElem_append_right (by simp [List.length_take]; omega)]
                        simp only [List.length_take, Nat.min_eq_left (by omega : k ≤ l1'.length)]
                        have h_jk : j - k ≥ 2 := by omega
                        have : ∀ (a b : FallingUnit) (rest : List FallingUnit) (n : Nat) (hn : n ≥ 2)
                            (h1 : n < (a :: b :: rest).length) (h2 : n - 2 < rest.length),
                            (a :: b :: rest)[n]'h1 = rest[n - 2]'h2 := by
                            intro a b rest n hn h1 h2
                            match n, hn with | n + 2, _ => simp only [List.getElem_cons_succ, Nat.add_sub_cancel]
                        rw [this _ _ _ _ h_jk (by simp [List.length_drop]; omega) (by simp [List.length_drop]; omega)]
                        rw [List.getElem_drop]; congr 1; omega
                    have h_j'_eq_j : j' = j :=
                        h_nodup'.getElem_inj_iff.mp (h_eq_j.trans h_l1''_j)
                    have h_l1''_i_eq : l1''[i]'hi = l1'[k+1]'hk := by
                        simp only [hi_k, hl1''_def]
                        rw [List.getElem_append_right (by simp [List.length_take])]
                        simp only [List.length_take, Nat.min_eq_left (by omega : k ≤ l1'.length),
                            Nat.sub_self, List.getElem_cons_zero]
                    have h_i'_eq : i' = k + 1 :=
                        h_nodup'.getElem_inj_iff.mp (h_eq_i.trans h_l1''_i_eq)
                    -- i' = k+1 > j' = j > k+1 → 矛盾
                    omega
                · by_cases hj_k1 : j = k + 1
                  · -- i ≠ k, j = k+1
                    -- i < k+1, i ≠ k → i < k
                    have hi_lt : i < k := by omega
                    -- l1''[i] = l1'[i] (i < k → i ∉ {k, k+1})
                    have h_l1''_i : l1''[i]'hi = l1'[i]'(by rw [h_len_eq] at hi; exact hi) := by
                        simp only [hl1''_def]
                        have h1 : i < (l1'.take k).length := by simp [List.length_take]; omega
                        rw [List.getElem_append_left h1]
                        simp [List.getElem_take]
                    have h_i'_eq_i : i' = i := h_nodup'.getElem_inj_iff.mp (h_eq_i.trans h_l1''_i)
                    -- l1''[j] = l1''[k+1] = l1'[k] → j' = k
                    have h_l1''_j_eq : l1''[j]'hj = l1'[k]'(by omega) := by
                        have hj_k1' : j = k + 1 := hj_k1; subst hj_k1'
                        simp only [hl1''_def]
                        rw [List.getElem_append_right (by simp [List.length_take])]
                        simp only [List.length_take, Nat.min_eq_left (by omega : k ≤ l1'.length),
                            show k + 1 - k = 1 from by omega,
                            List.getElem_cons_succ, List.getElem_cons_zero]
                    have h_j'_eq_k : j' = k := h_nodup'.getElem_inj_iff.mp (h_eq_j.trans h_l1''_j_eq)
                    -- i' = i < k = j' → i' < j' → ¬(i' > j')
                    omega
                  · -- i ≠ k, j ≠ k+1
                    -- l1''[i] = l1'[i], l1''[j] = l1'[j] (both ∉ {k, k+1} since i < j)
                    -- 実は i は k+1 かもしれない。i ≠ k だが i = k+1 の可能性あり
                    -- i < j, i ≠ k, j ≠ k+1
                    -- l1''[m] = l1'[m] for m ∉ {k, k+1}
                    -- i ∈ {k+1} の場合: l1''[k+1] = l1'[k] → i' = k
                    -- j ∈ {k} は j ≠ k+1 で j > i → j > k+1 なら j ∉ {k, k+1}
                    -- Case: i = k+1 → j > k+1 (from i < j) → j ∉ {k, k+1}
                    -- l1''[j] = l1'[j] → j' = j → i' = k > j is possible only if k > j → contradiction with j > k+1
                    -- Case: i ≠ k+1 → i ∉ {k, k+1} → l1''[i] = l1'[i] → i' = i
                    --   j might be k → but we check j ≠ k+1 above, j could be k if j > i
                    --   but j ≠ k from line above? No, hj_k1 is j = k+1, not j = k
                    --   if j = k: i < k and i ≠ k → l1''[i] = l1'[i], l1''[k] = l1'[k+1]
                    --     i' = i, j' = k+1 → i > j' → i > k+1 → but i < k → contradiction
                    --   if j ≠ k, j ≠ k+1 → l1''[j] = l1'[j] → j' = j
                    --     l1''[i] = l1'[i] if i ∉ {k, k+1} → i' = i → i > j impossible since i < j
                    --     i = k+1 → i' = k (from l1''[k+1] = l1'[k]) → k > j → but j > k+1 > k → contradiction
                    -- OK this is getting too complex with nested cases. Let me use a simpler approach.
                    -- For m ∉ {k, k+1}: l1''[m] = l1'[m]
                    -- If both i, j ∉ {k, k+1}: i' = i, j' = j → i' > j' ↔ i > j → contradicts i < j
                    -- If exactly one of i, j ∈ {k, k+1}: position shift is at most 1
                    -- The key insight: the only pair (i, j) with i < j that gets reversed by the swap
                    -- to (i', j') with i' > j' is (k, k+1). All other pairs maintain relative order.
                    -- Since (i, j) ≠ (k, k+1) (because i ≠ k or j ≠ k+1), we get i' ≤ j' → i' < j'.
                    -- But we assumed i' > j' → contradiction.
                    -- Let me enumerate remaining sub-cases:
                    by_cases hi_k1 : i = k + 1
                    · -- i = k+1, j ≠ k+1, j > k+1 (from i < j)
                      subst hi_k1
                      have hj_gt : j > k + 1 := by omega
                      -- l1''[k+1] = l1'[k] → i' = k
                      have h_l1''_k1 : l1''[k+1]'(by rw [h_len_eq]; omega) = l1'[k]'(by omega) := by
                          simp only [hl1''_def]
                          rw [List.getElem_append_right (by simp [List.length_take])]
                          simp only [List.length_take, Nat.min_eq_left (by omega : k ≤ l1'.length),
                              show k + 1 - k = 1 from by omega,
                              List.getElem_cons_succ, List.getElem_cons_zero]
                      have h_i'_eq_k : i' = k := h_nodup'.getElem_inj_iff.mp (h_eq_i.trans h_l1''_k1)
                      -- l1''[j] = l1'[j] (j > k+1 → j ∉ {k, k+1})
                      have h_l1''_j : l1''[j]'hj = l1'[j]'(by rw [h_len_eq] at hj; exact hj) := by
                          simp only [hl1''_def]
                          rw [List.getElem_append_right (by simp [List.length_take]; omega)]
                          simp only [List.length_take, Nat.min_eq_left (by omega : k ≤ l1'.length)]
                          have h_jk : j - k ≥ 2 := by omega
                          have : ∀ (a b : FallingUnit) (rest : List FallingUnit) (n : Nat) (hn : n ≥ 2)
                              (h1 : n < (a :: b :: rest).length) (h2 : n - 2 < rest.length),
                              (a :: b :: rest)[n]'h1 = rest[n - 2]'h2 := by
                              intro a b rest n hn h1 h2
                              match n, hn with | n + 2, _ => simp only [List.getElem_cons_succ, Nat.add_sub_cancel]
                          rw [this _ _ _ _ h_jk (by simp [List.length_drop]; omega) (by simp [List.length_drop]; omega)]
                          rw [List.getElem_drop]; congr 1; omega
                      have h_j'_eq_j : j' = j := h_nodup'.getElem_inj_iff.mp (h_eq_j.trans h_l1''_j)
                      -- i' = k > j' = j > k+1 → k > k+1 → 矛盾
                      omega
                    · -- i ≠ k, i ≠ k+1, j ≠ k+1
                      -- l1''[i] = l1'[i] (i ∉ {k, k+1})
                      have hi_not_kk1 : i ≠ k ∧ i ≠ k + 1 := ⟨hi_k, hi_k1⟩
                      have h_l1''_i : l1''[i]'hi = l1'[i]'(by rw [h_len_eq] at hi; exact hi) := by
                          simp only [hl1''_def]
                          by_cases hi_lt_k : i < k
                          · rw [List.getElem_append_left (by simp [List.length_take]; omega)]
                            simp [List.getElem_take]
                          · -- i > k+1
                            have : i > k + 1 := by omega
                            rw [List.getElem_append_right (by simp [List.length_take]; omega)]
                            simp only [List.length_take, Nat.min_eq_left (by omega : k ≤ l1'.length)]
                            have h_ik : i - k ≥ 2 := by omega
                            have : ∀ (a b : FallingUnit) (rest : List FallingUnit) (n : Nat) (hn : n ≥ 2)
                                (h1 : n < (a :: b :: rest).length) (h2 : n - 2 < rest.length),
                                (a :: b :: rest)[n]'h1 = rest[n - 2]'h2 := by
                                intro a b rest n hn h1 h2
                                match n, hn with | n + 2, _ => simp only [List.getElem_cons_succ, Nat.add_sub_cancel]
                            rw [this _ _ _ _ h_ik (by simp [List.length_drop]; omega) (by simp [List.length_drop]; omega)]
                            rw [List.getElem_drop]; congr 1; omega
                      have h_i'_eq_i : i' = i := h_nodup'.getElem_inj_iff.mp (h_eq_i.trans h_l1''_i)
                      -- j: if j = k → l1''[k] = l1'[k+1] → j' = k+1
                      -- if j ≠ k (and j ≠ k+1) → l1''[j] = l1'[j] → j' = j
                      by_cases hj_k : j = k
                      · have h_l1''_j_eq : l1''[j]'hj = l1'[k+1]'hk := by
                            simp only [hj_k, hl1''_def]
                            rw [List.getElem_append_right (by simp [List.length_take])]
                            simp only [List.length_take, Nat.min_eq_left (by omega : k ≤ l1'.length),
                                Nat.sub_self, List.getElem_cons_zero]
                        have h_j'_eq : j' = k + 1 := h_nodup'.getElem_inj_iff.mp (h_eq_j.trans h_l1''_j_eq)
                        -- i' = i > j' = k+1, but i < k = j → i < k and k+1 < i → 矛盾
                        omega
                      · -- j ≠ k, j ≠ k+1 → l1''[j] = l1'[j]
                        have hj_not_kk1 : j ≠ k ∧ j ≠ k + 1 := ⟨hj_k, hj_k1⟩
                        have h_l1''_j : l1''[j]'hj = l1'[j]'(by rw [h_len_eq] at hj; exact hj) := by
                            simp only [hl1''_def]
                            by_cases hj_lt_k : j < k
                            · rw [List.getElem_append_left (by simp [List.length_take]; omega)]
                              simp [List.getElem_take]
                            · have : j > k + 1 := by omega
                              rw [List.getElem_append_right (by simp [List.length_take]; omega)]
                              simp only [List.length_take, Nat.min_eq_left (by omega : k ≤ l1'.length)]
                              have h_jk : j - k ≥ 2 := by omega
                              have : ∀ (a b : FallingUnit) (rest : List FallingUnit) (n : Nat) (hn : n ≥ 2)
                                  (h1 : n < (a :: b :: rest).length) (h2 : n - 2 < rest.length),
                                  (a :: b :: rest)[n]'h1 = rest[n - 2]'h2 := by
                                  intro a b rest n hn h1 h2
                                  match n, hn with | n + 2, _ => simp only [List.getElem_cons_succ, Nat.add_sub_cancel]
                              rw [this _ _ _ _ h_jk (by simp [List.length_drop]; omega) (by simp [List.length_drop]; omega)]
                              rw [List.getElem_drop]; congr 1; omega
                        have h_j'_eq_j : j' = j := h_nodup'.getElem_inj_iff.mp (h_eq_j.trans h_l1''_j)
                        -- i' = i > j' = j → i > j → i < j に矛盾
                        omega
            -- h_tied_comm' から方角素を取得
            have h_result := h_tied_comm' i' j' hi' hj' h_lt_ij' h_inv'
            -- l1'[i'] = l1''[i], l1'[j'] = l1''[j] を使って結論を書き戻す
            exact ⟨
                fun p hp => by rw [← h_eq_i] at hp; rw [← h_eq_j]; exact h_result.1 p hp,
                fun p hp => by rw [← h_eq_j] at hp; rw [← h_eq_i]; exact h_result.2 p hp
            ⟩
        -- IH 適用
        rw [h_foldl_eq]
        have h_inv_lt : invCount l1'' l2 < n := h_inv ▸ h_inv_dec
        exact ih (invCount l1'' l2) h_inv_lt l1'' rfl h_perm'' h_nodup'' h_tied_comm''

-- ============================================================
-- floatingUnits の spb DAG 性 (ランク関数の存在)
-- ============================================================

/-- floatingUnits 上で shouldProcessBefore は DAG: ランク関数が存在する。
    spb(a,b)=true → rank(a) < rank(b) を満たすランク関数の存在。
    これにより 2-cycle も N-cycle も自動的に排除される。

    幾何学的論証:
    - Pin-Pin: 同方角ならレイヤで全順序。異方角なら spb は非発火。
    - Pin-Cluster: ピンは 1 方角のみ → 局所的に half-order
    - Cluster-Cluster: 構造結合の接続パスにより、同レイヤで 2 方角を占有 →
      残り 2 方角が環状隣接で封鎖 → 他クラスタが同レイヤに位置不可能 →
      共有方角列の minLayer が strict total order を形成 → DAG -/
private theorem floatingUnits_spb_rank (s : Shape) :
        ∃ rank : FallingUnit → Nat,
            ∀ i j, (hi : i < (floatingUnits s).length) →
                (hj : j < (floatingUnits s).length) →
                shouldProcessBefore ((floatingUnits s)[i]'hi) ((floatingUnits s)[j]'hj) = true →
                rank ((floatingUnits s)[i]'hi) < rank ((floatingUnits s)[j]'hj) := by
    sorry

/-- sortFU は入力の置換に対して foldl settle が不変（floatingUnits 限定）。
    l1 ~ l2 かつ全要素が floatingUnits s に属する場合、
    sortFU 後の foldl 結果は等しい。

    注意: 一般の h_disj + h_rank 仮定だけでは偽。
    反例: x=pin(NE,7), u=cluster(NE@8,SW@1), w=pin(SW,3) で
    sortFU [w,x,u]=[u,w,x] vs sortFU [x,u,w]=[w,x,u] —
    u が w と x の両方と方角共有し、insertSorted のグリーディ停止で
    非 tied ペアの順序が入力順に依存。
    floatingUnits の幾何制約 (同レイヤ隣接方角排除・構造結合パスの方角遷移層封鎖)
    により、このパターンは floatingUnits 上では発生しない。

    証明に必要な要素:
    1. floatingUnits_spb_rank (DAG ランク関数の存在)
    2. floatingUnits の幾何制約: 方角遷移層を持つクラスタは当該レイヤの
       全方角を占有 → tied な他要素は同レイヤに位置不可 →
       tied 要素と spb 連鎖が干渉するパターンが排除
    3. foldl_eq_of_perm_tied_adj_comm (sortFU の反転ペアが全て方角素)

    h_sub 条件により floatingUnits_pairwise_disjoint、floatingUnits_nodup、
    floatingUnits_spb_rank を全て利用可能。 -/
private theorem sortFU_foldl_perm_input_eq (s : Shape)
        (l1 l2 : List FallingUnit) (obs : List Layer)
        (h_perm : l1.Perm l2)
        (h_nodup_l1 : l1.Nodup)
        (h_sub : ∀ x, x ∈ l1 → x ∈ floatingUnits s) :
        (sortFallingUnits l1).foldl
            (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs =
        (sortFallingUnits l2).foldl
            (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs := by
    sorry

/-- 2 つの .any 等価な入力リストのソート後 foldl 結果は等しい。
    l1 = (fU s).map r180 と l2 = fU s.r180 に対して、
    中間リスト l_mid (l2 の置換で l1 と pointwise .any 等価) を構築し、
    sorted_foldl_pointwise_eq と sortFU_foldl_perm_input_eq で証明する。 -/
private theorem settle_foldl_eq (s : Shape) (obs : List Layer) :
        Shape.ofLayers
          ((sortFallingUnits ((floatingUnits s).map FallingUnit.rotate180)).foldl
            (fun obs u => placeFallingUnit s.rotate180 obs u (landingDistance u obs)) obs) =
        Shape.ofLayers
          ((sortFallingUnits (floatingUnits s.rotate180)).foldl
            (fun obs u => placeFallingUnit s.rotate180 obs u (landingDistance u obs)) obs) := by
    congr 1
    -- l1 = (fU s).map r180, l2 = fU s.r180 と置く
    set l1 := (floatingUnits s).map FallingUnit.rotate180 with hl1_def
    set l2 := floatingUnits s.rotate180 with hl2_def
    -- 各 u ∈ fU(s) に対応する v ∈ fU(s.r180) (u.r180 .any-equiv v) を Classical choice で取得
    have hg_ex : ∀ u ∈ floatingUnits s,
            ∃ v ∈ floatingUnits s.rotate180,
                ∀ p, u.rotate180.positions.any (· == p) = v.positions.any (· == p) :=
        floatingUnit_any_in_rotate180 s
    open Classical in
    let g : FallingUnit → FallingUnit :=
        fun u => if h : u ∈ floatingUnits s
            then (hg_ex u h).choose
            else u
    have hg_mem : ∀ u ∈ floatingUnits s, g u ∈ l2 := by
        intro u hu
        show (if h : u ∈ floatingUnits s then (hg_ex u h).choose else u) ∈ _
        rw [dif_pos hu]; exact (hg_ex u hu).choose_spec.1
    have hg_any : ∀ u ∈ floatingUnits s, ∀ p : QuarterPos,
            u.rotate180.positions.any (· == p) = (g u).positions.any (· == p) := by
        intro u hu
        show ∀ p, u.rotate180.positions.any (· == p) =
            (if h : u ∈ floatingUnits s then (hg_ex u h).choose else u).positions.any (· == p)
        rw [dif_pos hu]; exact (hg_ex u hu).choose_spec.2
    have hg_inj : ∀ u1 ∈ floatingUnits s, ∀ u2 ∈ floatingUnits s,
            g u1 = g u2 → u1 = u2 := by
        intro u1 hu1 u2 hu2 h_eq
        by_contra h_ne
        have ⟨p, hp⟩ := floatingUnit_positions_nonempty s u1 hu1
        have h1 : u1.rotate180.positions.any (· == p.rotate180) = true := by
            rw [any_positions_rotate180]; exact List.any_eq_true.mpr ⟨p, hp, BEq.rfl⟩
        have h2 : u2.rotate180.positions.any (· == p.rotate180) = true := by
            rw [hg_any u2 hu2, ← h_eq, ← hg_any u1 hu1]; exact h1
        rw [any_positions_rotate180] at h2
        obtain ⟨i, hi, h_eq_i⟩ := List.mem_iff_getElem.mp hu1
        obtain ⟨j, hj, h_eq_j⟩ := List.mem_iff_getElem.mp hu2
        subst h_eq_i; subst h_eq_j
        have h_ij : i ≠ j := fun h_eq_ij => h_ne (by subst h_eq_ij; rfl)
        exact absurd
            (by rw [List.any_eq_true] at h2 ⊢; exact h2 :
                ((floatingUnits s)[j]).positions.any (· == p) = true)
            (Bool.eq_false_iff.mp
                (floatingUnits_pairwise_disjoint s i j hi hj h_ij p
                    (List.any_eq_true.mpr ⟨p, hp, BEq.rfl⟩)))
    -- l_mid = (fU s).map g : l2 の要素を l1 と同じ順序で並べたリスト
    set l_mid := (floatingUnits s).map g with hl_mid_def
    -- l_mid は l1 と pointwise .any 等価
    have h_pw_l1_mid : ∀ (i : Nat) (hi : i < l1.length) (p : QuarterPos),
            (l1[i]'hi).positions.any (· == p) =
            (l_mid[i]'(by rw [hl_mid_def, List.length_map]; rw [hl1_def, List.length_map] at hi; exact hi)).positions.any (· == p) := by
        intro i hi p
        rw [hl1_def, List.length_map] at hi
        simp only [hl1_def, hl_mid_def, List.getElem_map]
        exact hg_any ((floatingUnits s)[i]) (List.getElem_mem hi) p
    have h_len_l1_mid : l1.length = l_mid.length := by
        simp [hl1_def, hl_mid_def, List.length_map]
    -- Step 2: sortFU l1 foldl = sortFU l_mid foldl (pointwise .any 等価)
    have h_step2 : (sortFallingUnits l1).foldl
            (fun obs u => placeFallingUnit s.rotate180 obs u (landingDistance u obs)) obs =
        (sortFallingUnits l_mid).foldl
            (fun obs u => placeFallingUnit s.rotate180 obs u (landingDistance u obs)) obs :=
        sorted_foldl_pointwise_eq s.rotate180 l1 l_mid obs h_len_l1_mid h_pw_l1_mid
    -- l_mid は l2 の置換 (NoDup + subset + same length)
    have h_mid_nodup : l_mid.Nodup := by
        rw [hl_mid_def]
        exact (List.nodup_map_iff_inj_on (floatingUnits_nodup s)).mpr
            (fun u1 hu1 u2 hu2 h_eq => hg_inj u1 hu1 u2 hu2 h_eq)
    have h_mid_sub : l_mid ⊆ l2 := by
        intro v hv
        rw [hl_mid_def, List.mem_map] at hv
        obtain ⟨u, hu, rfl⟩ := hv
        exact hg_mem u hu
    have h_len_mid_l2 : l2.length ≤ l_mid.length := by
        rw [hl_mid_def, List.length_map, hl2_def]
        exact Nat.le_of_eq (floatingUnits_length_rotate180 s).symm
    have h_perm_mid_l2 : l_mid.Perm l2 :=
        (List.subperm_of_subset h_mid_nodup h_mid_sub).perm_of_length_le h_len_mid_l2
    -- Step 3: sortFU l_mid foldl = sortFU l2 foldl (perm invariance, floatingUnits 限定)
    have h_step3 : (sortFallingUnits l_mid).foldl
            (fun obs u => placeFallingUnit s.rotate180 obs u (landingDistance u obs)) obs =
        (sortFallingUnits l2).foldl
            (fun obs u => placeFallingUnit s.rotate180 obs u (landingDistance u obs)) obs := by
        exact sortFU_foldl_perm_input_eq s.rotate180 l_mid l2 obs h_perm_mid_l2
            h_mid_nodup h_mid_sub
    exact h_step2.trans h_step3

-- ============================================================
-- process_rotate180 の本体
-- ============================================================

/-- 落下処理と 180° 回転は可換である -/
theorem process_rotate180 (s : Shape) :
        (process s).map Shape.rotate180 = process s.rotate180 := by
    simp only [process]
    rw [← floatingUnits_isEmpty_rotate180]
    split <;> rename_i h
    · -- 落下単位なし: normalize の等変性
      exact s.normalize_map_layers Layer.rotate180 Layer.isEmpty_rotate180
    · -- 落下単位あり: パイプライン全体の等変性
      -- normalize + ofLayers の交換
      rw [option_bind_normalize_rotate180, ofLayers_rotate180]
      congr 1
      -- foldl_place_rotate180 で LHS の map Lr180 を foldl 内部に移動
      rw [foldl_place_rotate180]
      -- sorted の書き換え: sortFallingUnits_rotate180 を適用
      rw [sortFallingUnits_rotate180]
      -- obstacle の等変性: clearPositions_rotate180 + clearPositions_ext で証明
      rw [← layers_rotate180, clearPositions_rotate180]
      -- obstacle の .any メンバーシップ同値を clearPositions_ext で示す
      have h_obs_eq : s.rotate180.clearPositions
              ((sortFallingUnits (floatingUnits s)).flatMap FallingUnit.positions
                  |>.map QuarterPos.rotate180) =
            s.rotate180.clearPositions
              ((sortFallingUnits (floatingUnits s.rotate180)).flatMap
                  FallingUnit.positions) := by
          apply Shape.clearPositions_ext; intro p
          rw [any_map_rotate180_beq]
          rw [sortFallingUnits_any_positions (floatingUnits s)]
          rw [sortFallingUnits_any_positions (floatingUnits s.rotate180)]
          have := falling_positions_any_rotate180 s p.rotate180
          rw [QuarterPos.rotate180_rotate180] at this
          exact this
      rw [h_obs_eq]
      -- sorted リスト foldl の等価性: settle_foldl_eq で閉じる
      exact settle_foldl_eq s _

end Gravity

namespace Shape

/-- 落下処理を適用する。浮遊している落下単位を下方に移動させる -/
def gravity (s : Shape) : Option Shape :=
    Gravity.process s

/-- 落下処理を適用し結果がない場合（全て空）は元のシェイプを返す便利関数 -/
def gravityOrSelf (s : Shape) : Shape :=
    s.gravity.getD s

/-- 落下処理と 180° 回転は可換である -/
theorem gravity_rotate180_comm (s : Shape) :
        (s.gravity).map Shape.rotate180 = s.rotate180.gravity := by
    exact Gravity.process_rotate180 s

-- ============================================================
-- 安定状態 (Settled State) の定義
-- ============================================================

/-- シェイプが安定状態: 浮遊する落下単位が存在しない -/
def IsSettled (s : Shape) : Prop :=
    Gravity.floatingUnits s = []

/-- シェイプが安定状態かどうかを判定する -/
def isSettled (s : Shape) : Bool :=
    (Gravity.floatingUnits s).isEmpty

/-- IsSettled と isSettled の同値性 -/
theorem IsSettled_iff_isSettled (s : Shape) :
        s.IsSettled ↔ s.isSettled = true := by
    simp only [IsSettled, isSettled]
    constructor
    · intro h; rw [h]; rfl
    · intro h
      cases hf : Gravity.floatingUnits s with
      | nil => rfl
      | cons a l => rw [hf] at h; simp [List.isEmpty] at h

/-- 安定状態は rotate180 で保存される -/
theorem IsSettled_rotate180 (s : Shape) (h : s.IsSettled) :
        s.rotate180.IsSettled := by
    simp only [IsSettled] at h ⊢
    have he := Gravity.floatingUnits_isEmpty_rotate180 s
    rw [h] at he
    -- he : true = (floatingUnits s.rotate180).isEmpty
    cases hf : Gravity.floatingUnits s.rotate180 with
    | nil => rfl
    | cons a l => rw [hf] at he; simp [List.isEmpty] at he

end Shape
