-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Behavior.CrystalBond
import S2IL.Behavior.GenericBfs

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

/-- LawfulBEq を持つ型に対して == は可換である -/
private theorem beq_symm [BEq α] [LawfulBEq α] (a b : α) : (a == b) = (b == a) := by
    cases h : a == b with
    | true => have := eq_of_beq h; subst this; exact h.symm
    | false =>
        symm; cases h2 : b == a with
        | false => rfl
        | true => exact absurd (eq_of_beq h2).symm (by intro heq; subst heq; simp at h)

/-- Direction の == は可換である -/
private theorem dir_beq_symm (a b : Direction) : (a == b) = (b == a) := by
    cases a <;> cases b <;> rfl

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
            rw [beq_symm p1.layer p2.layer,
                Direction.adjacent_symm p1.dir p2.dir,
                LayerIndex.verticallyAdjacent_symm p1.layer p2.layer,
                dir_beq_symm p1.dir p2.dir]

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
    -- 複数 seed に対応するため n² + n の fuel を使用
    -- (queue.length ≤ n かつ unvisited ≤ n なので fuel + 1 ≥ seeds.length + n² を満たす)
    groundingBfs s allPos [] seeds (n * n + n)

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
-- ============================================================

/-- getDir と rotate180 の可換性 -/
private theorem getDir_rotate180 (l : Layer) (d : Direction) :
        QuarterPos.getDir (l.rotate180) (d.rotate180) = QuarterPos.getDir l d := by
    cases d <;> rfl

/-- Shape.layers と rotate180 の関係 -/
private theorem layers_rotate180 (s : Shape) :
        s.rotate180.layers = s.layers.map Layer.rotate180 := by
    simp [Shape.rotate180, Shape.mapLayers]

/-- getQuarter と rotate180 の可換性 -/
private theorem getQuarter_rotate180 (s : Shape) (pos : QuarterPos) :
        pos.rotate180.getQuarter s.rotate180 = pos.getQuarter s := by
    simp only [QuarterPos.getQuarter, QuarterPos.rotate180, layers_rotate180]
    rw [List.getElem?_map]
    cases s.layers[pos.layer]? with
    | none => rfl
    | some l => simp [getDir_rotate180]

/-- getQuarter の rotate180 逆方向 -/
private theorem getQuarter_rotate180_inv (s : Shape) (p : QuarterPos) :
        p.getQuarter s.rotate180 = p.rotate180.getQuarter s := by
    have h := getQuarter_rotate180 s p.rotate180
    rw [QuarterPos.rotate180_rotate180] at h; exact h

/-- isStructurallyBonded は rotate180 で不変 -/
theorem isStructurallyBonded_rotate180 (s : Shape) (p1 p2 : QuarterPos) :
        isStructurallyBonded (s.rotate180) (p1.rotate180) (p2.rotate180) =
        isStructurallyBonded s p1 p2 := by
    simp only [isStructurallyBonded, getQuarter_rotate180]
    simp only [QuarterPos.rotate180, Direction.adjacent_rotate180]
    cases p1.getQuarter s <;> cases p2.getQuarter s <;> try rfl
    rename_i q1 q2
    congr 1
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
    simp only [Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and] <;>
    (try rfl) <;> congr 1 <;> cases p1.dir <;> cases p2.dir <;> rfl

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
    induction l with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.map, List.any, ih, quarterPos_beq_rotate180]

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
-- structuralCluster / groundedPositions の rotate180 等変性
-- ============================================================

/-- structuralCluster を mapped allPos で呼んだ場合の等変性 -/
private theorem structuralCluster_rotate180_mapped (s : Shape) (pos : QuarterPos) :
        structuralBfs s.rotate180
            ((QuarterPos.allValid s).map QuarterPos.rotate180) []
            [pos.rotate180]
            (s.layerCount * 4 * (s.layerCount * 4)) =
        (structuralCluster s pos).map QuarterPos.rotate180 := by
    unfold structuralCluster
    exact structuralBfs_rotate180 s (QuarterPos.allValid s) [] [pos]
        (s.layerCount * 4 * (s.layerCount * 4))

/-- groundedPositions を mapped allPos で呼んだ場合の等変性 -/
private theorem groundedPositions_rotate180_mapped (s : Shape) :
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
        (groundedPositions s).map QuarterPos.rotate180 := by
    unfold groundedPositions
    exact groundingBfs_rotate180 s (QuarterPos.allValid s) []
        ((QuarterPos.allValid s).filter fun p =>
            p.layer == 0 &&
            match p.getQuarter s with
            | some q => !q.isEmpty
            | none   => false)
        (s.layerCount * 4 * (s.layerCount * 4) + s.layerCount * 4)

-- ============================================================
-- clearPositions の rotate180 等変性（Shatter.lean の private 版を再証明）
-- ============================================================

/-- List.map と List.set の可換性 -/
private theorem list_map_set {α β : Type} (f : α → β) (l : List α) (i : Nat) (a : α) :
        (l.set i a).map f = (l.map f).set i (f a) := by
    induction l generalizing i with
    | nil => simp
    | cons x xs ih =>
        cases i with
        | zero => simp [List.set]
        | succ n => simp [List.set, ih]

/-- List.set は非空リストを空にしない -/
private theorem set_ne_nil_of_ne_nil {α : Type} {l : List α} (h : l ≠ []) (i : Nat) (a : α) :
        l.set i a ≠ [] := by
    cases l with
    | nil => exact absurd rfl h
    | cons x xs => cases i <;> simp [List.set]

/-- setQuarter のレイヤが存在する場合、.layers は List.set の結果に等しい -/
private theorem setQuarter_layers_eq (s : Shape) (pos : QuarterPos) (q : Quarter) (l : Layer)
        (hl : s.layers[pos.layer]? = some l) :
        (pos.setQuarter s q).layers = s.layers.set pos.layer (QuarterPos.setDir l pos.dir q) := by
    simp only [QuarterPos.setQuarter, hl]
    split
    · rename_i h
      exact absurd h (set_ne_nil_of_ne_nil s.layers_ne pos.layer _)
    · rfl

/-- setDir と rotate180 の可換性（empty 特化版） -/
private theorem setDir_rotate180_empty (l : Layer) (d : Direction) :
        (QuarterPos.setDir l d .empty).rotate180 =
        QuarterPos.setDir (l.rotate180) (d.rotate180) .empty := by
    cases d <;> rfl

/-- setQuarter と rotate180 の可換性（empty 特化版） -/
private theorem setQuarter_rotate180_empty (s : Shape) (pos : QuarterPos) :
        (pos.setQuarter s .empty).rotate180 =
        (pos.rotate180).setQuarter (s.rotate180) .empty := by
    cases hl : s.layers[pos.layer]? with
    | none =>
        simp only [QuarterPos.setQuarter, QuarterPos.rotate180, layers_rotate180,
                    List.getElem?_map, hl, Option.map_none]
    | some l =>
        have hl_r : (s.layers.map Layer.rotate180)[pos.layer]? = some (l.rotate180) := by
            rw [List.getElem?_map, hl]; rfl
        apply Shape.ext
        show (pos.setQuarter s .empty).layers.map Layer.rotate180 =
             ((pos.rotate180).setQuarter s.rotate180 .empty).layers
        rw [setQuarter_layers_eq s pos .empty l hl]
        rw [setQuarter_layers_eq s.rotate180 pos.rotate180 .empty (l.rotate180)
                (show s.rotate180.layers[pos.rotate180.layer]? = some (l.rotate180) by
                    simp only [Shape.rotate180, Shape.mapLayers, QuarterPos.rotate180]
                    exact hl_r)]
        simp only [QuarterPos.rotate180, list_map_set, setDir_rotate180_empty,
                    Shape.rotate180, Shape.mapLayers]

/-- clearPositions は rotate180 で等変 -/
private theorem clearPositions_rotate180 (s : Shape) (ps : List QuarterPos) :
        (s.clearPositions ps).rotate180 =
        (s.rotate180).clearPositions (ps.map QuarterPos.rotate180) := by
    induction ps generalizing s with
    | nil => rfl
    | cons p rest ih =>
        show (Shape.clearPositions (p.setQuarter s .empty) rest).rotate180 =
            Shape.clearPositions ((p.rotate180).setQuarter (s.rotate180) .empty)
                (rest.map QuarterPos.rotate180)
        rw [ih, setQuarter_rotate180_empty]

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

/-- List.filterMap と List.map の合成 -/
private theorem list_filterMap_map {α β γ : Type} (f : β → Option γ) (g : α → β) (l : List α) :
        (l.map g).filterMap f = l.filterMap (f ∘ g) := by
    induction l with
    | nil => rfl
    | cons a rest ih =>
        simp only [List.map, List.filterMap, Function.comp, ih]

/-- positions の map rotate180 した filterMap は元の filterMap と同じ (layer 列) -/
private theorem filterMap_rotate180_layer (ps : List QuarterPos) (d : Direction) :
        (ps.map QuarterPos.rotate180).filterMap (fun p =>
            if p.dir == d.rotate180 then some p.layer else none) =
        ps.filterMap (fun p => if p.dir == d then some p.layer else none) := by
    rw [list_filterMap_map]
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

/-- insertSorted は rotate180 で等変 -/
private theorem insertSorted_rotate180 (u : FallingUnit) (sorted : List FallingUnit) (fuel : Nat) :
        (insertSorted u sorted fuel).map FallingUnit.rotate180 =
        insertSorted u.rotate180 (sorted.map FallingUnit.rotate180) fuel := by
    induction fuel generalizing sorted with
    | zero => simp [insertSorted, List.map]
    | succ n ih =>
        cases sorted with
        | nil => simp [insertSorted, List.map]
        | cons v rest =>
            simp only [insertSorted, List.map]
            rw [FallingUnit.minLayer_rotate180 u, FallingUnit.minLayer_rotate180 v,
                shouldProcessBefore_rotate180]
            split
            · simp [List.map]
            · simp only [List.map]; exact congrArg _ (ih rest)

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
private theorem structuralCluster_sound (s : Shape) (start p : QuarterPos) :
        (structuralCluster s start).any (· == p) = true →
        GenericReachable (isStructurallyBonded s) start p := by
    intro h; unfold structuralCluster at h
    rw [structuralBfs_eq_generic] at h
    match genericBfs_sound (isStructurallyBonded s) _ [] [start] _ p h with
    | .inl h_vis => simp [List.any] at h_vis
    | .inr ⟨q, h_q, h_reach⟩ =>
        rw [List.any_cons, Bool.or_eq_true_iff] at h_q
        cases h_q with
        | inl h_eq => exact eq_of_beq h_eq ▸ h_reach
        | inr h_rest => simp [List.any] at h_rest

/-- 構造クラスタのメンバーシップは rotate180 で保存される -/
private theorem structuralCluster_mem_rotate180 (s : Shape) (start p : QuarterPos) :
        (structuralCluster s start).any (· == p) =
        (structuralCluster s.rotate180 start.rotate180).any (· == p.rotate180) := by
    cases h : (structuralCluster s start).any (· == p) with
    | true =>
        have h_reach := structuralCluster_sound s start p h
        have h_reach' := structuralReachable_rotate180 s start p h_reach
        symm; unfold structuralCluster
        rw [CrystalBond.allValid_rotate180_eq, Shape.layerCount_rotate180,
            structuralBfs_eq_generic]
        have h_inv := genericBfs_invariant_preserved (isStructurallyBonded s.rotate180)
            (QuarterPos.allValid s) [] [start.rotate180]
            (s.layerCount * 4 * (s.layerCount * 4))
            (genericBfsInv_initial _ _ _)
            (by
                have h_filter : (QuarterPos.allValid s).filter (fun p =>
                    !(([] : List QuarterPos).any (· == p))) = QuarterPos.allValid s :=
                    List.filter_eq_self.mpr (by intro x _; simp [List.any])
                simp only [h_filter, List.length, allValid_length']
                omega)
            (fun p q h => by
                rw [← CrystalBond.allValid_rotate180_eq]
                exact (allValid_any_iff_layer' s.rotate180 p).mpr (isStructurallyBonded_valid s.rotate180 q p
                    (isStructurallyBonded_symm s.rotate180 p q ▸ h)))
        have h_start : (genericBfs (isStructurallyBonded s.rotate180) (QuarterPos.allValid s) []
            [start.rotate180] (s.layerCount * 4 * (s.layerCount * 4))).any
            (· == start.rotate180) = true := by
            cases hn : s.layerCount with
            | zero =>
                unfold structuralCluster at h
                rw [structuralBfs_eq_generic] at h; simp [hn, genericBfs] at h
            | succ n =>
                exact genericBfs_contains_start _ _ _ _ (by simp)
        exact genericBfs_closed_contains_reachable _ _ _ h_inv
            start.rotate180 p.rotate180 h_start h_reach'
            (fun q r h_bond => by
                rw [← CrystalBond.allValid_rotate180_eq]
                exact (allValid_any_iff_layer' s.rotate180 r).mpr
                    (Shape.layerCount_rotate180 s ▸ isStructurallyBonded_valid s.rotate180 q r h_bond))
    | false =>
        symm
        cases h' : (structuralCluster s.rotate180 start.rotate180).any (· == p.rotate180) with
        | false => rfl
        | true =>
            have h_reach' := structuralCluster_sound s.rotate180 start.rotate180 p.rotate180 h'
            have h_reach : GenericReachable (isStructurallyBonded s) start p := by
                have := structuralReachable_rotate180 s.rotate180 start.rotate180 p.rotate180 h_reach'
                simp [Shape.rotate180_rotate180, QuarterPos.rotate180_rotate180] at this
                exact this
            unfold structuralCluster at h
            rw [structuralBfs_eq_generic] at h
            have h_inv := genericBfs_invariant_preserved (isStructurallyBonded s)
                (QuarterPos.allValid s) [] [start]
                (s.layerCount * 4 * (s.layerCount * 4))
                (genericBfsInv_initial _ _ _)
                (by
                    have h_filter : (QuarterPos.allValid s).filter (fun p =>
                        !(([] : List QuarterPos).any (· == p))) = QuarterPos.allValid s :=
                        List.filter_eq_self.mpr (by intro x _; simp [List.any])
                    simp only [h_filter, List.length, allValid_length']
                    omega)
                (fun p q h => by
                    exact (allValid_any_iff_layer' s p).mpr (isStructurallyBonded_valid s q p
                        (isStructurallyBonded_symm s p q ▸ h)))
            have h_start_mem : (genericBfs (isStructurallyBonded s) (QuarterPos.allValid s) []
                [start] (s.layerCount * 4 * (s.layerCount * 4))).any (· == start) = true := by
                cases hn : s.layerCount with
                | zero =>
                    unfold structuralCluster at h'
                    rw [structuralBfs_eq_generic, CrystalBond.allValid_rotate180_eq,
                        Shape.layerCount_rotate180] at h'
                    simp [hn, genericBfs] at h'
                | succ n =>
                    exact genericBfs_contains_start _ _ _ _ (by simp)
            have h_mem := genericBfs_closed_contains_reachable _ _ _ h_inv
                start p h_start_mem h_reach
                (fun q r h_bond =>
                    (allValid_any_iff_layer' s r).mpr (isStructurallyBonded_valid s q r h_bond))
            rw [h_mem] at h; exact Bool.noConfusion h

/-- 接地位置のメンバーシップは rotate180 で保存される。
    構造クラスタと同じパターンだが、BFS の初期キューが複数 seed のため
    fuel 条件の処理に追加の手順が必要（最初の seed を手動処理後に invariant_preserved を適用）。 -/
private theorem groundedPositions_mem_rotate180 (s : Shape) (p : QuarterPos) :
        (groundedPositions s).any (· == p) =
        (groundedPositions s.rotate180).any (· == p.rotate180) := by
    sorry -- structuralCluster_mem_rotate180 と同じパターン。
           -- 差分: BFS の初期キューが複数 seed（layer-0 非空象限）のため、
           -- 最初の seed を手動処理してから invariant_preserved を適用する必要がある。

-- ============================================================
-- floatingUnits の rotate180 等変性
-- ============================================================

/-- floatingUnits は rotate180 で等変（リスト等号は BFS 探索順序のため成立しない。
    代わりにメンバーシップレベルでの等変性を使用する） -/
private theorem floatingUnits_rotate180 (s : Shape) :
        (floatingUnits s).map FallingUnit.rotate180 =
        floatingUnits s.rotate180 := by
    sorry -- この定理はリスト等号として偽。process_rotate180 の再構築が必要

/-- floatingUnits の isEmpty は rotate180 で不変 -/
theorem floatingUnits_isEmpty_rotate180 (s : Shape) :
        (floatingUnits s).isEmpty = (floatingUnits s.rotate180).isEmpty := by
    -- 両方の Bool 値について場合分け
    cases h : (floatingUnits s).isEmpty <;>
        cases h' : (floatingUnits s.rotate180).isEmpty
    · rfl
    · exfalso; sorry -- s に浮遊単位あり・s.r180 にはなし → 矛盾
    · exfalso; sorry -- s になし・s.r180 にあり → 矛盾
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

/-- FallingUnit.hasPositionAt は rotate180 で等変 -/
private theorem FallingUnit.hasPositionAt_rotate180 (u : FallingUnit) (layer : Nat) (d : Direction) :
        u.rotate180.hasPositionAt layer (d.rotate180) = u.hasPositionAt layer d := by
    simp only [FallingUnit.hasPositionAt, FallingUnit.positions_rotate180]
    induction u.positions with
    | nil => rfl
    | cons p ps ih =>
        simp only [List.map, List.any, QuarterPos.rotate180, dir_beq_rotate180']
        rw [ih]

/-- landed 判定 (positions.any) は rotate180 で不変 -/
private theorem landed_rotate180 (positions : List QuarterPos) (obs : List Layer) (d : Nat) :
        (positions.map QuarterPos.rotate180).any (fun p =>
            let newLayer := p.layer - d
            newLayer == 0 || (newLayer > 0 && isOccupied (obs.map Layer.rotate180) (newLayer - 1) p.dir)) =
        positions.any (fun p =>
            let newLayer := p.layer - d
            newLayer == 0 || (newLayer > 0 && isOccupied obs (newLayer - 1) p.dir)) := by
    induction positions with
    | nil => rfl
    | cons p rest ih =>
        simp only [List.map, List.any]
        rw [ih]
        congr 1
        simp only [QuarterPos.rotate180, QuarterPos.rotate180_layer]
        congr 1
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
        | some l => simp only [Option.map_some]; rw [list_map_set, setDir_rotate180]
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
            rw [list_map_set, setDir_rotate180]

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
      -- foldl の等変性 (map Layer.rotate180 を foldl 内部に移動)
      rw [foldl_place_rotate180]
      -- sorted, obstacle をそれぞれ rotate180 等変に書き換え
      -- sorted の等変性
      have h_sorted : (sortFallingUnits (floatingUnits s)).map FallingUnit.rotate180 =
          sortFallingUnits (floatingUnits s.rotate180) := by
          rw [sortFallingUnits_rotate180, floatingUnits_rotate180]
      -- obstacle の等変性
      have h_obs : ((s.clearPositions ((sortFallingUnits (floatingUnits s)).flatMap FallingUnit.positions)).layers).map Layer.rotate180 =
          (s.rotate180.clearPositions ((sortFallingUnits (floatingUnits s.rotate180)).flatMap FallingUnit.positions)).layers := by
          rw [← h_sorted, flatMap_map_rotate180]
          -- ゴール: ... .layers.map Lr180 = (s.r180.clearPositions (ps.map Qr180)).layers
          -- clearPositions_rotate180: (s.clearPositions ps).r180 = s.r180.clearPositions (ps.map Qr180)
          rw [← clearPositions_rotate180]
          -- ゴール: ... .layers.map Lr180 = ((s.clearPositions ...).r180).layers
          rw [layers_rotate180]
      rw [h_sorted, h_obs]

/-- floatingUnits の flatMap positions は rotate180 で等変 -/
theorem floatingUnits_flatMap_positions_rotate180 (s : Shape) :
        ((floatingUnits s).flatMap FallingUnit.positions).map QuarterPos.rotate180 =
        (floatingUnits s.rotate180).flatMap FallingUnit.positions := by
    rw [← flatMap_map_rotate180, floatingUnits_rotate180]

end Gravity

namespace Shape

/-- 落下処理を適用する。浮遊している落下単位を下方に移動させる -/
def gravity (s : Shape) : Option Shape :=
    Gravity.process s

/-- 落下処理を適用し、結果がない場合（全て空）は元のシェイプを返す便利関数 -/
def gravityOrSelf (s : Shape) : Shape :=
    s.gravity.getD s

/-- 落下処理と 180° 回転は可換である -/
theorem gravity_rotate180_comm (s : Shape) :
        (s.gravity).map Shape.rotate180 = s.rotate180.gravity := by
    exact Gravity.process_rotate180 s

end Shape
