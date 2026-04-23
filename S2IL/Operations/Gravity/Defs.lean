-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel.Bond.CrystalBond
import S2IL.Kernel.BFS.GenericBfs
import S2IL.Kernel.Transform.Rotate180Lemmas
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sort

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
def structuralBfs (s : Shape) (allPos : List QuarterPos)
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

/-- `isGroundingContact` は両端点が非空象限であることを要求する -/
theorem isGroundingContact_nonEmpty (s : Shape) (p1 p2 : QuarterPos)
        (h : isGroundingContact s p1 p2 = true) :
        ∃ q1 q2, p1.getQuarter s = some q1 ∧ p2.getQuarter s = some q2 ∧
        q1.isEmpty = false ∧ q2.isEmpty = false := by
    simp only [isGroundingContact] at h
    cases hq1 : p1.getQuarter s with
    | none => simp only [hq1] at h; exact absurd h (by decide)
    | some q1 =>
        cases hq2 : p2.getQuarter s with
        | none => simp only [hq1, hq2] at h; exact absurd h (by decide)
        | some q2 =>
            simp only [hq1, hq2, Bool.and_eq_true, Bool.not_eq_true'] at h
            exact ⟨q1, q2, rfl, rfl, h.1.1, h.1.2⟩

/-- `isStructurallyBonded` が成立すれば `isGroundingContact` も成立する
    （bonded 象限は colored/crystal であり、非空・非ピン） -/
theorem isStructurallyBonded_implies_isGroundingContact (s : Shape) (p1 p2 : QuarterPos)
        (h : isStructurallyBonded s p1 p2 = true) :
        isGroundingContact s p1 p2 = true := by
    simp only [isStructurallyBonded] at h
    simp only [isGroundingContact]
    cases hq1 : p1.getQuarter s with
    | none => simp only [hq1] at h; exact absurd h (by decide)
    | some q1 =>
        cases hq2 : p2.getQuarter s with
        | none => simp only [hq1, hq2] at h; exact absurd h (by decide)
        | some q2 =>
            simp only [hq1, hq2, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h ⊢
            obtain ⟨⟨hcfb1, hcfb2⟩, h_adj⟩ := h
            refine ⟨⟨?_, ?_⟩, ?_⟩
            · cases q1 <;> simp_all only [Quarter.canFormBond, Quarter.isEmpty]
            · cases q2 <;> simp_all only [Quarter.canFormBond, Quarter.isEmpty]
            · cases h_adj with
              | inl h =>
                  right
                  exact ⟨⟨h.1, h.2⟩, by cases q1 <;> cases q2 <;>
                      simp_all only [Quarter.canFormBond]⟩
              | inr h => left; exact ⟨h.2, h.1⟩

/-- `isGroundingContact` は prefix layers で保存される -/
theorem isGroundingContact_of_layers_prefix (s s' : Shape)
        (h_pfx : ∃ t, s.layers = s'.layers ++ t)
        (p1 p2 : QuarterPos)
        (h_v1 : p1.layer < s'.layerCount)
        (h_v2 : p2.layer < s'.layerCount) :
        isGroundingContact s' p1 p2 = isGroundingContact s p1 p2 := by
    simp only [isGroundingContact, QuarterPos.getQuarter, Shape.layerCount] at *
    obtain ⟨t, ht⟩ := h_pfx
    rw [ht,
        List.getElem?_append_left (by omega),
        List.getElem?_append_left (by omega)]

/-- 上方向接地接触: 同レイヤ以上への接地接触のみ許可する。
    BFS で下方向（高レイヤ→低レイヤ）への探索を防ぐために使用する -/
def isUpwardGroundingContact (s : Shape) (from_ to_ : QuarterPos) : Bool :=
    isGroundingContact s from_ to_ && decide (from_.layer ≤ to_.layer)

/-- isUpwardGroundingContact が成立すれば isGroundingContact も成立する -/
theorem isUpwardGroundingContact_base {s : Shape} {a b : QuarterPos}
        (h : isUpwardGroundingContact s a b = true) :
        isGroundingContact s a b = true := by
    simp only [isUpwardGroundingContact] at h
    revert h; cases isGroundingContact s a b <;> simp

/-- isGroundingContact かつレイヤ条件を満たせば isUpwardGroundingContact -/
theorem isGroundingContact_to_isUpwardGroundingContact {s : Shape} {a b : QuarterPos}
        (h_gc : isGroundingContact s a b = true) (h_le : a.layer ≤ b.layer) :
        isUpwardGroundingContact s a b = true := by
    simp only [isUpwardGroundingContact, h_gc, h_le, decide_true, Bool.true_and]

/-- isUpwardGroundingContact からレイヤ条件を抽出する -/
theorem isUpwardGroundingContact_layer_le {s : Shape} {a b : QuarterPos}
        (h : isUpwardGroundingContact s a b = true) : a.layer ≤ b.layer := by
    simp only [isUpwardGroundingContact, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2

/-- 接地 BFS のエッジ関数: 上方向接地接触 ∨ 構造結合。
    上方向接地接触は垂直方向の接地チェーンを構築し、
    構造結合はクラスタ内の双方向伝播を保証する -/
def groundingEdge (s : Shape) (a b : QuarterPos) : Bool :=
    isUpwardGroundingContact s a b || isStructurallyBonded s a b

/-- isUpwardGroundingContact → groundingEdge -/
theorem groundingEdge_of_isUpwardGroundingContact {s : Shape} {a b : QuarterPos}
        (h : isUpwardGroundingContact s a b = true) :
        groundingEdge s a b = true := by
    simp only [groundingEdge, h, Bool.true_or]

/-- isStructurallyBonded → groundingEdge -/
theorem groundingEdge_of_isStructurallyBonded {s : Shape} {a b : QuarterPos}
        (h : isStructurallyBonded s a b = true) :
        groundingEdge s a b = true := by
    simp only [groundingEdge, h, Bool.or_true]

/-- groundingEdge → isGroundingContact（どちらのケースでも isGroundingContact が成立する） -/
theorem groundingEdge_base {s : Shape} {a b : QuarterPos}
        (h : groundingEdge s a b = true) :
        isGroundingContact s a b = true := by
    simp only [groundingEdge, Bool.or_eq_true] at h
    rcases h with h | h
    · exact isUpwardGroundingContact_base h
    · exact isStructurallyBonded_implies_isGroundingContact s a b h

/-- Vacuous-case helper: 端点 `a` の象限が空（または `none`）であれば `groundingEdge` は偽。

    `isGroundingContact` が両端点の非空性を要求することから直ちに従う（`isGroundingContact_nonEmpty` 経由）。
    Sub-lemma #7 (`waveStep_grounding_mono`) で、着地位置のエッジ前提を vacuous に閉じるための基盤補題。 -/
theorem groundingEdge_false_of_empty_quarter {s : Shape} {a : QuarterPos}
        (b : QuarterPos)
        (h : ∀ q, a.getQuarter s = some q → q.isEmpty = true) :
        groundingEdge s a b = false := by
    cases hval : groundingEdge s a b with
    | false => rfl
    | true =>
        exfalso
        have hgc := groundingEdge_base hval
        obtain ⟨q1, _q2, hq1, _hq2, he1, _he2⟩ := isGroundingContact_nonEmpty s a b hgc
        have h_emp := h q1 hq1
        rw [h_emp] at he1
        exact absurd he1 (by decide)

/-- `groundingEdge_false_of_empty_quarter` の対称版（端点 `b` が空）。 -/
theorem groundingEdge_false_of_empty_quarter_right {s : Shape} {b : QuarterPos}
        (a : QuarterPos)
        (h : ∀ q, b.getQuarter s = some q → q.isEmpty = true) :
        groundingEdge s a b = false := by
    cases hval : groundingEdge s a b with
    | false => rfl
    | true =>
        exfalso
        have hgc := groundingEdge_base hval
        obtain ⟨_q1, q2, _hq1, hq2, _he1, he2⟩ := isGroundingContact_nonEmpty s a b hgc
        have h_emp := h q2 hq2
        rw [h_emp] at he2
        exact absurd he2 (by decide)

/-- BFS で接地接触チェーンにより到達可能な全象限を返す。
    上方向接地接触と構造結合の両方をエッジとして使用する -/
def groundingBfs (s : Shape) (allPos : List QuarterPos)
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
                    groundingEdge s pos p && !(newVisited.any (· == p))
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

/-- 非接地かつ非空な象限位置の (layer + 1) の総和。
    waveStep の終了性測度として使用する。
    各 settling 位置は layer L から L-d に降下するため、
    各位置の寄与は -(L+1)+(L-d+1) = -d ≤ -1 で厳密減少が保証される。
    着地位置は obs 上で常に空であるため（landingDistance の構造的保証）、
    既存の接地コンテンツの上書きは発生せず、接地グラフの破壊も起きない -/
def nonGroundedLayerSum (s : Shape) : Nat :=
    let allPos := QuarterPos.allValid s
    let grounded := groundedPositions s
    allPos.foldl (fun acc p =>
        match p.getQuarter s with
        | some q => if !q.isEmpty && p ∉ grounded then acc + p.layer + 1 else acc
        | none => acc
    ) 0

/-- 各位置の NGS への寄与を返す。非空かつ非接地なら layer+1、それ以外は 0 -/
def ngsWeight (s : Shape) (p : QuarterPos) : Nat :=
    match p.getQuarter s with
    | some q => if !q.isEmpty && p ∉ groundedPositions s then p.layer + 1 else 0
    | none => 0

/-- NGS の foldl を List.sum に変換する（アキュムレータシフト補題） -/
private theorem ngs_foldl_eq_sum (s : Shape) (grounded : Finset QuarterPos)
        (l : List QuarterPos) (acc : Nat) :
        l.foldl (fun acc p =>
            match p.getQuarter s with
            | some q => if !q.isEmpty && p ∉ grounded then acc + p.layer + 1 else acc
            | none => acc) acc
        = acc + (l.map (fun p =>
            match p.getQuarter s with
            | some q => if !q.isEmpty && p ∉ grounded then p.layer + 1 else 0
            | none => 0)).sum := by
    induction l generalizing acc with
    | nil => simp
    | cons x xs ih =>
        simp only [List.foldl_cons, List.map_cons, List.sum_cons]
        rw [ih]
        generalize x.getQuarter s = gq
        cases gq with
        | none => dsimp only; omega
        | some q =>
            dsimp only; split
            · simp only [Nat.add_assoc]
            · omega

/-- nonGroundedLayerSum は ngsWeight の合計に等しい -/
theorem nonGroundedLayerSum_eq_sum (s : Shape) :
        nonGroundedLayerSum s = ((QuarterPos.allValid s).map (ngsWeight s)).sum := by
    unfold nonGroundedLayerSum
    suffices ∀ (l : List QuarterPos) (acc : Nat),
        l.foldl (fun acc p =>
            match p.getQuarter s with
            | some q => if !q.isEmpty && p ∉ groundedPositions s then acc + p.layer + 1 else acc
            | none => acc) acc
        = acc + (l.map (ngsWeight s)).sum by simpa using this _ 0
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
        intro acc
        simp only [List.foldl_cons, List.map_cons, List.sum_cons]
        rw [ih]; simp only [ngsWeight]
        generalize x.getQuarter s = gq
        cases gq with
        | none => dsimp only; omega
        | some q =>
            dsimp only; split
            · simp only [Nat.add_assoc]
            · omega

/-- クリア対象位置の ngsWeight は 0 -/
private theorem ngsWeight_clearPositions_mem (s : Shape) (ps : List QuarterPos)
        (p : QuarterPos) (hp : (ps.any (· == p)) = true)
        (hp_lt : p.layer < s.layerCount) :
        ngsWeight (s.clearPositions ps) p = 0 := by
    simp only [ngsWeight]
    have h := QuarterPos.getQuarter_clearPositions s ps p hp_lt
    rw [hp] at h; simp only [ite_true] at h; rw [h]; simp [Quarter.isEmpty]

/-- 非クリア位置の ngsWeight は保存される（接地集合が同一なら） -/
private theorem ngsWeight_clearPositions_not_mem (s : Shape) (ps : List QuarterPos)
        (h_gp_eq : groundedPositions (s.clearPositions ps) = groundedPositions s)
        (p : QuarterPos) (hp : (ps.any (· == p)) = false)
        (hp_lt : p.layer < s.layerCount) :
        ngsWeight (s.clearPositions ps) p = ngsWeight s p := by
    simp only [ngsWeight, h_gp_eq]
    have h := QuarterPos.getQuarter_clearPositions s ps p hp_lt
    rw [hp] at h; simp at h; rw [h]

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
def shouldProcessBefore (a b : FallingUnit) : Bool :=
    -- 全方角について、共有列での上下関係を確認
    Direction.all.any fun dir =>
        match a.minLayerAtDir dir, b.minLayerAtDir dir with
        | some la, some lb => la < lb
        | _, _ => false

/-- 挿入ソート: u をソート済みリストの適切な位置に挿入する。
    shouldProcessBefore u v = true の場合のみ v の前に挿入する。
    tied ペア（双方 false）の場合はスキップして後方に配置する。
    これにより shouldProcessBefore 関係が常に保存される。 -/
def insertSorted (u : FallingUnit) (sorted : List FallingUnit)
        : (fuel : Nat) → List FallingUnit
    | 0 => u :: sorted
    | fuel + 1 =>
        match sorted with
        | [] => [u]
        | v :: rest =>
            -- u が v より先に処理されるべきか判定
            if shouldProcessBefore u v
            then u :: v :: rest
            else v :: insertSorted u rest fuel

/-- 落下単位を下位優先でソートする（挿入ソート。最大16象限なので十分）。
    仕様参照用。実際の gravity 処理では `sortFallingUnits'`（mergeSort 版）を使用する -/
def sortFallingUnits (units : List FallingUnit) : List FallingUnit :=
    units.foldl (fun sorted u => insertSorted u sorted (sorted.length + 1)) []

-- ============================================================
-- 決定性ソート (mergeSort + 全順序)
-- ============================================================

/-- 落下単位の全前順序比較: minLayer の ≤ で比較する。
    minLayer は rotate180 / rotateCW で不変なため、
    ソート結果は回転等変となる（List.map_mergeSort で証明可能）。
    同レイヤの落下単位は tied になるが、方角素のため foldl で可換。-/
def fallingUnitLe (a b : FallingUnit) : Bool :=
    decide (a.minLayer ≤ b.minLayer)

/-- fallingUnitLe は全前順序: 任意の a, b で fallingUnitLe a b ∨ fallingUnitLe b a -/
theorem fallingUnitLe_total (a b : FallingUnit) : fallingUnitLe a b = true ∨ fallingUnitLe b a = true := by
    simp only [fallingUnitLe, decide_eq_true_eq]
    exact Nat.le_total a.minLayer b.minLayer

/-- fallingUnitLe は推移的 -/
theorem fallingUnitLe_trans {a b c : FallingUnit} (h1 : fallingUnitLe a b = true) (h2 : fallingUnitLe b c = true) :
        fallingUnitLe a c = true := by
    simp only [fallingUnitLe, decide_eq_true_eq] at *
    exact Nat.le_trans h1 h2

-- ============================================================
-- 全順序比較 fallingUnitOrd (minLayer + canonicalKey)
-- ============================================================

/-- 象限位置を自然数にエンコードする (layer * 4 + dir.toFin) -/
def encodeQuarterPos (p : QuarterPos) : Nat :=
    p.layer * 4 + p.dir.toFin.val

/-- 落下単位の正規化ソートキー: 全位置をエンコードし重複を除いてソートした自然数リスト。
    .any 等価な落下単位は同じ canonicalKey を持つ（位置の集合が等しいため）。
    toFinset.sort を使うため、encode が同じ値を複数含む場合でも正規化される。
    rotate180 では値が変化するが、fallingUnitOrd の antisymmetry にのみ使用され、
    等変性証明には影響しない（mergeSort_perm_eq 経由） -/
def FallingUnit.canonicalKey (u : FallingUnit) : List Nat :=
    (u.positions.map encodeQuarterPos).toFinset.sort (· ≤ ·)

/-- List Nat の辞書式 ≤ 比較（Mathlib の LinearOrder (List Nat) を利用） -/
def listNatLe (l1 l2 : List Nat) : Bool := decide (l1 ≤ l2)

/-- listNatLe は反射的 -/
theorem listNatLe_refl (l : List Nat) : listNatLe l l = true :=
    decide_eq_true (le_refl l)

/-- listNatLe は全前順序 -/
theorem listNatLe_total (l1 l2 : List Nat) :
        listNatLe l1 l2 = true ∨ listNatLe l2 l1 = true := by
    rcases le_total l1 l2 with h | h <;> [left; right] <;> exact decide_eq_true h

/-- listNatLe は推移的 -/
theorem listNatLe_trans {l1 l2 l3 : List Nat}
        (h1 : listNatLe l1 l2 = true) (h2 : listNatLe l2 l3 = true) :
        listNatLe l1 l3 = true :=
    decide_eq_true (le_trans (of_decide_eq_true h1) (of_decide_eq_true h2))

/-- listNatLe は反対称的 -/
theorem listNatLe_antisymm {l1 l2 : List Nat}
        (h1 : listNatLe l1 l2 = true) (h2 : listNatLe l2 l1 = true) : l1 = l2 :=
    le_antisymm (of_decide_eq_true h1) (of_decide_eq_true h2)

/-- 落下単位の型識別子: pin = 0, cluster = 1。
    fallingUnitOrd の 2 次キーとして使用し、pin-cluster ペアの順序を確定させる。
    同 minLayer の pin と cluster は方角素のため処理順序不問だが、
    全順序性のため決定的な序数を与える。
    rotate180/rotateCW はコンストラクタを保存するため、この値は回転不変。-/
def FallingUnit.typeOrd : FallingUnit → Nat
    | .pin _ => 0
    | .cluster _ => 1

/-- typeOrd は 0 か 1 -/
theorem FallingUnit.typeOrd_le_one (u : FallingUnit) : u.typeOrd ≤ 1 := by
    cases u <;> simp only [typeOrd] <;> omega

/-- 複合ソートグループ: minLayer * 2 + typeOrd。
    foldl_perm_sorted_eq のグループキーとして使用し、
    pin-cluster ペアを異なるグループに分離する。 -/
def FallingUnit.sortGroup (u : FallingUnit) : Nat :=
    u.minLayer * 2 + u.typeOrd

/-- sortGroup 等値 → minLayer 等値 ∧ typeOrd 等値 -/
theorem FallingUnit.sortGroup_eq_iff {u v : FallingUnit} :
        u.sortGroup = v.sortGroup ↔ u.minLayer = v.minLayer ∧ u.typeOrd = v.typeOrd := by
    constructor
    · intro h
      have hu := u.typeOrd_le_one
      have hv := v.typeOrd_le_one
      simp only [sortGroup] at h
      constructor <;> omega
    · rintro ⟨hm, ht⟩; simp only [sortGroup, hm, ht]

/-- 落下単位の全順序比較（非厳密、決定性）:
    1 次キー: minLayer（昇順）
    2 次キー: typeOrd（pin < cluster）
    3 次キー: canonicalKey（辞書式 ≤）
    全順序のため mergeSort の出力が入力の置換に依存しない。-/
def fallingUnitOrd (a b : FallingUnit) : Bool :=
    if a.minLayer < b.minLayer then true
    else if b.minLayer < a.minLayer then false
    else if a.typeOrd < b.typeOrd then true
    else if b.typeOrd < a.typeOrd then false
    else listNatLe a.canonicalKey b.canonicalKey

/-- fallingUnitOrd は全順序: 任意の a, b で fallingUnitOrd a b ∨ fallingUnitOrd b a -/
theorem fallingUnitOrd_total (a b : FallingUnit) : fallingUnitOrd a b = true ∨ fallingUnitOrd b a = true := by
    simp only [fallingUnitOrd]
    by_cases h1 : a.minLayer < b.minLayer
    · simp only [h1, ↓reduceIte, true_or]
    · simp only [h1, ↓reduceIte]
      by_cases h2 : b.minLayer < a.minLayer
      · simp only [h2, ↓reduceIte, or_true]
      · have h_eq : a.minLayer = b.minLayer := Nat.le_antisymm (Nat.not_lt.mp h2) (Nat.not_lt.mp h1)
        simp only [h_eq, Nat.lt_irrefl, ↓reduceIte]
        by_cases h3 : a.typeOrd < b.typeOrd
        · simp only [h3, ↓reduceIte, true_or]
        · simp only [h3, ↓reduceIte]
          by_cases h4 : b.typeOrd < a.typeOrd
          · simp only [h4, ↓reduceIte, or_true]
          · have h_teq : a.typeOrd = b.typeOrd := Nat.le_antisymm (Nat.not_lt.mp h4) (Nat.not_lt.mp h3)
            simp only [h_teq, Nat.lt_irrefl, ↓reduceIte]
            exact listNatLe_total _ _

/-- fallingUnitOrd の全順序性を Bool の || で表現 -/
theorem fallingUnitOrd_total' (a b : FallingUnit) : (fallingUnitOrd a b || fallingUnitOrd b a) = true := by
    rcases fallingUnitOrd_total a b with h | h <;> simp only [h, Bool.true_or, Bool.or_true]

/-- fallingUnitOrd は推移的 -/
theorem fallingUnitOrd_trans {a b c : FallingUnit} (h1 : fallingUnitOrd a b = true) (h2 : fallingUnitOrd b c = true) :
        fallingUnitOrd a c = true := by
    simp only [fallingUnitOrd] at *
    split at h1 <;> rename_i h_ab1
    · -- a.minLayer < b.minLayer
      split at h2 <;> rename_i h_bc1
      · simp only [show a.minLayer < c.minLayer from Nat.lt_trans h_ab1 h_bc1, ↓reduceIte]
      · split at h2 <;> rename_i h_bc2
        · exact absurd h2 (by decide)
        · split at h2 <;> rename_i h_bc3
          · simp only [show a.minLayer < c.minLayer from by omega, ↓reduceIte]
          · split at h2 <;> rename_i h_bc4
            · exact absurd h2 (by decide)
            · simp only [show a.minLayer < c.minLayer from by omega, ↓reduceIte]
    · split at h1 <;> rename_i h_ab2
      · exact absurd h1 (by decide)
      · -- a.minLayer = b.minLayer
        split at h1 <;> rename_i h_ab3
        · -- a.typeOrd < b.typeOrd
          have h_eq_ab : a.minLayer = b.minLayer := by omega
          split at h2 <;> rename_i h_bc1
          · simp only [show a.minLayer < c.minLayer from h_eq_ab ▸ h_bc1, ↓reduceIte]
          · split at h2 <;> rename_i h_bc2
            · simp only [show ¬(a.minLayer < c.minLayer) from by omega,
                          show c.minLayer < a.minLayer from by omega, ↓reduceIte]
              exact h2
            · split at h2 <;> rename_i h_bc3
              · simp only [show ¬(a.minLayer < c.minLayer) from by omega,
                            show ¬(c.minLayer < a.minLayer) from by omega, ↓reduceIte,
                            show a.typeOrd < c.typeOrd from by omega]
              · split at h2 <;> rename_i h_bc4
                · exact absurd h2 (by decide)
                · simp only [show ¬(a.minLayer < c.minLayer) from by omega,
                              show ¬(c.minLayer < a.minLayer) from by omega, ↓reduceIte,
                              show a.typeOrd < c.typeOrd from by omega]
        · split at h1 <;> rename_i h_ab4
          · exact absurd h1 (by decide)
          · -- a.minLayer = b.minLayer, a.typeOrd = b.typeOrd
            have h_eq_ab : a.minLayer = b.minLayer := by omega
            have h_teq_ab : a.typeOrd = b.typeOrd := by omega
            split at h2 <;> rename_i h_bc1
            · simp only [show a.minLayer < c.minLayer from h_eq_ab ▸ h_bc1, ↓reduceIte]
            · split at h2 <;> rename_i h_bc2
              · simp only [show ¬(a.minLayer < c.minLayer) from by omega,
                            show c.minLayer < a.minLayer from by omega, ↓reduceIte]
                exact h2
              · split at h2 <;> rename_i h_bc3
                · simp only [show ¬(a.minLayer < c.minLayer) from by omega,
                              show ¬(c.minLayer < a.minLayer) from by omega, ↓reduceIte,
                              show a.typeOrd < c.typeOrd from h_teq_ab ▸ h_bc3]
                · split at h2 <;> rename_i h_bc4
                  · simp only [show ¬(a.minLayer < c.minLayer) from by omega,
                                show ¬(c.minLayer < a.minLayer) from by omega, ↓reduceIte,
                                show ¬(a.typeOrd < c.typeOrd) from by omega,
                                show c.typeOrd < a.typeOrd from by omega]
                    exact h2
                  · have h_eq_bc : b.minLayer = c.minLayer := by omega
                    have h_teq_bc : b.typeOrd = c.typeOrd := by omega
                    simp only [show ¬(a.minLayer < c.minLayer) from by omega,
                                show ¬(c.minLayer < a.minLayer) from by omega,
                                show ¬(a.typeOrd < c.typeOrd) from by omega,
                                show ¬(c.typeOrd < a.typeOrd) from by omega, ↓reduceIte]
                    exact listNatLe_trans h1 h2

-- ============================================================
-- fallingUnitOrd ユーティリティ: canonicalKey / Perm / antisymmetry
-- ============================================================

/-- .any (·==p) が等しいリストは、toFinset が等しい。
    これにより canonicalKey (= toFinset.sort ∘ map encode) も等しくなる。-/
theorem toFinset_eq_of_any_eq {l1 l2 : List Nat}
        (h : ∀ n, l1.any (· == n) = l2.any (· == n)) :
        l1.toFinset = l2.toFinset := by
    ext n; simp only [List.mem_toFinset]
    have h1 : l1.any (· == n) = true ↔ n ∈ l1 := by
        simp only [List.any_eq_true, beq_iff_eq]
        exact ⟨fun ⟨_, h, rfl⟩ => h, fun h => ⟨n, h, rfl⟩⟩
    have h2 : l2.any (· == n) = true ↔ n ∈ l2 := by
        simp only [List.any_eq_true, beq_iff_eq]
        exact ⟨fun ⟨_, h, rfl⟩ => h, fun h => ⟨n, h, rfl⟩⟩
    rw [← h1, ← h2]; exact Bool.eq_iff_iff.mp (h n)

/-- .any 等価な位置リストは同じ canonicalKey を持つ -/
theorem canonicalKey_eq_of_any_eq {u1 u2 : FallingUnit}
        (h : ∀ p : QuarterPos, u1.positions.any (· == p) = u2.positions.any (· == p)) :
        u1.canonicalKey = u2.canonicalKey := by
    unfold FallingUnit.canonicalKey
    congr 1
    -- ゴール: (u1.positions.map encodeQuarterPos).toFinset = (u2.positions.map encodeQuarterPos).toFinset
    ext n
    simp only [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      have h1 : u1.positions.any (· == p) = true := List.any_eq_true.mpr ⟨p, hp, BEq.rfl⟩
      rw [h p] at h1
      obtain ⟨q, hq, hqp⟩ := List.any_eq_true.mp h1
      simp only [beq_iff_eq] at hqp
      exact ⟨q, hq, by rw [hqp]⟩
    · rintro ⟨p, hp, rfl⟩
      have h2 : u2.positions.any (· == p) = true := List.any_eq_true.mpr ⟨p, hp, BEq.rfl⟩
      rw [← h p] at h2
      obtain ⟨q, hq, hqp⟩ := List.any_eq_true.mp h2
      simp only [beq_iff_eq] at hqp
      exact ⟨q, hq, by rw [hqp]⟩

/-- fallingUnitOrd が .any 等価なペアで一致する -/
theorem fallingUnitOrd_eq_of_any_eq {a1 a2 b1 b2 : FallingUnit}
        (ha : ∀ p, a1.positions.any (· == p) = a2.positions.any (· == p))
        (hb : ∀ p, b1.positions.any (· == p) = b2.positions.any (· == p))
        (h_ml_a : a1.minLayer = a2.minLayer) (h_ml_b : b1.minLayer = b2.minLayer)
        (h_type_a : a1.typeOrd = a2.typeOrd) (h_type_b : b1.typeOrd = b2.typeOrd) :
        fallingUnitOrd a1 b1 = fallingUnitOrd a2 b2 := by
    simp only [fallingUnitOrd, h_ml_a, h_ml_b, h_type_a, h_type_b,
        canonicalKey_eq_of_any_eq ha, canonicalKey_eq_of_any_eq hb]

/-- encodeQuarterPos は単射 -/
theorem encodeQuarterPos_injective : Function.Injective encodeQuarterPos := by
    intro p q h
    unfold encodeQuarterPos at h
    have h_layer : p.layer = q.layer := by omega
    have h_dir_val : p.dir.toFin.val = q.dir.toFin.val := by omega
    have h_dir : p.dir = q.dir := by
        revert h_dir_val; cases p.dir <;> cases q.dir <;> simp only [Direction.toFin] <;> decide
    cases p; cases q; subst h_layer; subst h_dir; rfl

/-- Perm + total + trans + antisymm → mergeSort が同じ結果を返す -/
theorem mergeSort_perm_eq {le : α → α → Bool}
        (h_trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
        (h_total : ∀ a b, (le a b || le b a) = true)
        {l1 l2 : List α} (h_perm : l1.Perm l2)
        (h_antisymm : ∀ a ∈ l1, ∀ b ∈ l1,
            le a b = true → le b a = true → a = b) :
        l1.mergeSort le = l2.mergeSort le := by
    have pw1 := List.pairwise_mergeSort h_trans h_total l1
    have pw2 := List.pairwise_mergeSort h_trans h_total l2
    have hp := (List.mergeSort_perm l1 le).trans
        (h_perm.trans (List.mergeSort_perm l2 le).symm)
    exact List.Perm.eq_of_pairwise
        (fun a b ha hb hab hba =>
            h_antisymm a ((List.mergeSort_perm l1 le).mem_iff.mp ha)
                       b (h_perm.symm.mem_iff.mp
                            ((List.mergeSort_perm l2 le).mem_iff.mp hb))
                       hab hba)
        pw1 pw2 hp

/-- 落下単位を全順序で決定性ソートする（Mathlib の mergeSort を使用）。
    fallingUnitOrd は全順序のため、同一要素集合に対して一意のソート結果を返す。-/
def sortFallingUnits' (units : List FallingUnit) : List FallingUnit :=
    units.mergeSort fallingUnitOrd

-- ============================================================
-- 着地位置の算出
-- ============================================================

/-- 障害物シェイプ上で、指定位置が非空かを判定する。
    レイヤ範囲外の場合は false (空扱い) -/
def isOccupied (obstacle : List Layer) (layer : Nat) (dir : Direction) : Bool :=
    match obstacle[layer]? with
    | some l => !(QuarterPos.getDir l dir).isEmpty
    | none   => false

-- ============================================================
-- isOccupied と getDir ≠ empty の同値 (bridge)
--
-- R-1 により chain 補題は `getDir ≠ empty` 形を基本単位として扱うが、
-- `isOccupied` は `placeLDGroupsLandings` 定義など既存 API との境界で
-- 使用する。両者の同値を Defs レベルで一度だけ記述しておく。
-- ============================================================

/-- `isOccupied = true` と `getDir ≠ Quarter.empty` は同値。 -/
theorem isOccupied_iff_getDir_ne_empty (obs : List Layer) (lay : Nat) (dir : Direction) :
        isOccupied obs lay dir = true ↔
        QuarterPos.getDir (obs.getD lay Layer.empty) dir ≠ Quarter.empty := by
    unfold isOccupied
    cases h_get : obs[lay]? with
    | none =>
        have h_getD : obs.getD lay Layer.empty = Layer.empty := by
            simp [List.getD_eq_getElem?_getD, h_get]
        rw [h_getD]
        refine ⟨fun h => by simp at h, fun h => ?_⟩
        exfalso; apply h; cases dir <;> rfl
    | some l =>
        have h_getD : obs.getD lay Layer.empty = l := by
            simp [List.getD_eq_getElem?_getD, h_get]
        rw [h_getD]
        simp only
        constructor
        · intro h h_eq
          rw [h_eq] at h
          simp [Quarter.isEmpty] at h
        · intro h
          cases hq : QuarterPos.getDir l dir
          · exact absurd hq h
          all_goals (simp [Quarter.isEmpty])

/-- `getDir ≠ empty` から `isOccupied = true` を取り出す方向。 -/
lemma isOccupied_of_getDir_ne_empty (obs : List Layer) (lay : Nat) (dir : Direction)
        (h : QuarterPos.getDir (obs.getD lay Layer.empty) dir ≠ Quarter.empty) :
        isOccupied obs lay dir = true :=
    (isOccupied_iff_getDir_ne_empty obs lay dir).mpr h

/-- `isOccupied = true` から `getDir ≠ empty` を取り出す方向。 -/
lemma getDir_ne_empty_of_isOccupied (obs : List Layer) (lay : Nat) (dir : Direction)
        (h : isOccupied obs lay dir = true) :
        QuarterPos.getDir (obs.getD lay Layer.empty) dir ≠ Quarter.empty :=
    (isOccupied_iff_getDir_ne_empty obs lay dir).mp h

/-- 落下単位の着地距離を算出する。
    obstacle は障害物シェイプ（レイヤのリスト）。
    注意: minLayer = 0 の場合 d = 0 を返すが、floatingUnits の出力では
    L0 は常に接地のため minLayer ≥ 1 が保証される（dead code path） -/
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
def placeQuarter (layers : List Layer) (layer : Nat) (dir : Direction)
        (q : Quarter) : List Layer :=
    -- レイヤが足りない場合は空レイヤで拡張
    let extended := if layer < layers.length then layers
        else layers ++ List.replicate (layer + 1 - layers.length) Layer.empty
    match extended[layer]? with
    | some l => extended.set layer (QuarterPos.setDir l dir q)
    | none => extended  -- ありえないが安全策

/-- 落下単位の全象限を元のシェイプから取得し、障害物シェイプに配置する -/
def placeFallingUnit (origShape : Shape) (obstacle : List Layer)
        (u : FallingUnit) (dropDist : Nat) : List Layer :=
    u.positions.foldl (fun obs p =>
        match p.getQuarter origShape with
        | some q => placeQuarter obs (p.layer - dropDist) p.dir q
        | none => obs
    ) obstacle

-- ============================================================
-- 波動モデル (Wave Model) — 落下処理
-- ============================================================

/-- LD グループ単位で settling FU を配置する。
    前提: sorted は landingDistance(_, obs) の昇順でソート済み。
    同一 LD グループ内: グループ開始時の obs で算出した LD(= d) を全 FU に固定適用。
    グループ間: 前グループの配置結果を新 obs として LD を再算出。
    これにより同一 LD の FU 配置順序が結果に影響しなくなり回転等変性が保証される。 -/
def placeLDGroups (origShape : Shape)
        (sorted : List FallingUnit) (obs : List Layer) : List Layer :=
    match sorted with
    | [] => obs
    | first :: rest =>
        let d := landingDistance first obs
        -- ソート済みなので同一 LD の FU は先頭に連続する
        let group := (first :: rest).takeWhile
            (fun u => landingDistance u obs == d)
        let remaining := (first :: rest).dropWhile
            (fun u => landingDistance u obs == d)
        -- グループ内: 固定 d でまとめて配置（配置順序に依存しない）
        let obs' := group.foldl (fun acc fu =>
            placeFallingUnit origShape acc fu d
        ) obs
        placeLDGroups origShape remaining obs'
    termination_by sorted.length
    decreasing_by
        -- remaining = (first :: rest).dropWhile p
        -- p first = true (d == d) → remaining = rest.dropWhile p
        -- dropWhile_suffix → remaining <:+ rest → remaining.length ≤ rest.length < sorted.length
        show ((first :: rest).dropWhile _).length < (first :: rest).length
        simp only [List.dropWhile_cons, beq_self_eq_true, ↓reduceIte, List.length_cons]
        exact Nat.lt_succ_of_le (List.dropWhile_suffix _).length_le

/-- 1波処理: 最小 minLayer を持つ全浮遊単位をその着地位置に配置する。
    - 残りの FU はそのまま（次波に持越し）
    - 各波で少なくとも 1 FU が settle するため、floatingUnits.length が単調減少する
    - settling FU は事前計算した着地距離（obs 基準）の昇順でソートし、
      低着地 FU を先に配置する。同一 LD 内はグループ一括配置。
    - 同一 LD のグループ内では配置順序に依存しないため回転等変性が保証される -/
def waveStep (s : Shape) : Shape :=
    let fus := floatingUnits s
    if fus.isEmpty then s
    else
        -- 最小 minLayer を持つ FU のみを今波で処理する
        -- fus は非空（isEmpty = false を確認済み）
        let minML := fus.tail.foldl (fun acc u => min acc u.minLayer)
            (fus.head?.map FallingUnit.minLayer |>.getD 0)
        let settling := fus.filter fun u => u.minLayer == minML
        let settlingPos := settling.flatMap FallingUnit.positions
        -- 障害物: 今波で着地する FU のみ除去（残りの FU は障害物に残留）
        let obs := (s.clearPositions settlingPos).layers
        -- 着地距離の昇順でソート（回転等変性の保証に必要）
        let sortedSettling := settling.mergeSort
            (fun a b => landingDistance a obs ≤ landingDistance b obs)
        -- LD グループ単位で配置（同一 LD 内は固定 LD で一括配置）
        let result := placeLDGroups s sortedSettling obs
        match Shape.ofLayers result with
        | some s' => s'
        | none    => s  -- 到達不能（FU の minLayer ≥ 1 が保証されるため非発生）

-- ============================================================
-- 終端性証明のための補助補題 (P3: S1 の前提補題群)
-- ============================================================

/-- placeQuarter の結果は obs ≠ [] を保存する -/
private theorem placeQuarter_ne_nil (layers : List Layer) (layer : Nat) (d : Direction) (q : Quarter)
        (h : layers ≠ []) : placeQuarter layers layer d q ≠ [] := by
    simp only [placeQuarter]
    have hext : (if layer < layers.length then layers
        else layers ++ List.replicate (layer + 1 - layers.length) Layer.empty) ≠ [] := by
        split
        · exact h
        · exact fun heq => h (List.append_eq_nil_iff.mp heq).1
    generalize (if layer < layers.length then layers
        else layers ++ List.replicate (layer + 1 - layers.length) Layer.empty) = ext at hext ⊢
    cases ext[layer]? with
    | some l =>
        intro hnil
        exact hext (by
            have := congr_arg List.length hnil
            simp only [List.length_nil, List.length_set] at this
            exact List.length_eq_zero_iff.mp this)
    | none => exact hext

/-- placeFallingUnit の結果は obs ≠ [] を保存する -/
private theorem placeFallingUnit_ne_nil (s : Shape) (obs : List Layer)
        (u : FallingUnit) (d : Nat) (h : obs ≠ []) :
        placeFallingUnit s obs u d ≠ [] := by
    unfold placeFallingUnit
    induction u.positions generalizing obs with
    | nil => simpa
    | cons p rest ih =>
        simp only [List.foldl_cons]
        apply ih
        cases p.getQuarter s with
        | none => exact h
        | some q => exact placeQuarter_ne_nil obs _ _ _ h

/-- 固定 d での foldl placeFallingUnit は obs ≠ [] を保存する -/
private theorem foldl_placeFU_fixed_ne_nil (s : Shape) (group : List FallingUnit) (obs : List Layer) (d : Nat)
        (h : obs ≠ []) :
        group.foldl (fun acc fu => placeFallingUnit s acc fu d) obs ≠ [] := by
    induction group generalizing obs with
    | nil => simpa
    | cons u rest ih =>
        simp only [List.foldl_cons]
        apply ih
        exact placeFallingUnit_ne_nil s obs u d h

/-- placeLDGroups の結果は obs ≠ [] を保存する -/
private theorem placeLDGroups_ne_nil (s : Shape) (sorted : List FallingUnit)
        (obs : List Layer) (h : obs ≠ []) :
        placeLDGroups s sorted obs ≠ [] := by
    suffices hh : ∀ n (sorted : List FallingUnit) (obs : List Layer),
        sorted.length ≤ n → obs ≠ [] → placeLDGroups s sorted obs ≠ [] from
        hh sorted.length sorted obs le_rfl h
    intro n
    induction n with
    | zero =>
        intro sorted obs hlen hobs
        have : sorted = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
        subst this; rw [placeLDGroups.eq_def]; exact hobs
    | succ n ih =>
        intro sorted obs hlen hobs
        match sorted with
        | [] => rw [placeLDGroups.eq_def]; exact hobs
        | first :: rest =>
            have hrest_le : rest.length ≤ n := by simp only [List.length_cons] at hlen; omega
            have hdrop_le :
                    (List.dropWhile (fun u => landingDistance u obs == landingDistance first obs)
                        (first :: rest)).length ≤ n := by
                have hdrop_eq : List.dropWhile
                        (fun u => landingDistance u obs == landingDistance first obs) (first :: rest) =
                        List.dropWhile
                            (fun u => landingDistance u obs == landingDistance first obs) rest := by
                    simp
                rw [hdrop_eq]; exact le_trans (List.dropWhile_suffix _).length_le hrest_le
            have hobs' :
                    (List.foldl (fun acc fu => placeFallingUnit s acc fu (landingDistance first obs)) obs
                        (List.takeWhile (fun u => landingDistance u obs == landingDistance first obs)
                            (first :: rest))) ≠ [] :=
                foldl_placeFU_fixed_ne_nil s _ obs _ hobs
            rw [placeLDGroups.eq_def]
            exact ih _ _ hdrop_le hobs'

/-- clearPositions の結果の layers は非空 -/
private theorem clearPositions_layers_ne_nil (s : Shape) (positions : List QuarterPos) :
        (s.clearPositions positions).layers ≠ [] := by
    unfold Shape.clearPositions
    induction positions generalizing s with
    | nil => exact s.layers_ne
    | cons p rest ih =>
        simp only [List.foldl_cons]
        apply ih

/-- placeLDGroups の結果で Shape.ofLayers が some を返す -/
private theorem placeLDGroups_ofLayers_isSome (s : Shape) (sorted : List FallingUnit) (obs : List Layer)
        (h : obs ≠ []) :
        (Shape.ofLayers (placeLDGroups s sorted obs)).isSome = true := by
    have hne := placeLDGroups_ne_nil s sorted obs h
    cases hcase : placeLDGroups s sorted obs with
    | nil => exact absurd rfl (hcase ▸ hne)
    | cons l ls => simp [Shape.ofLayers]

/-- `waveStep` の結果の layers を `placeLDGroups` で特徴付ける。
    `floatingUnits s` が非空のとき `waveStep s` 内部の `match Shape.ofLayers` の
    分岐を解消し、`(waveStep s).layers = placeLDGroups s sortedSettling obs` の
    形に直接到達する。`waveStep_ngs_strict_bound` 等の下流証明での使用を想定。 -/
theorem waveStep_layers_eq (s : Shape) (h : (floatingUnits s).isEmpty = false) :
        let fus := floatingUnits s
        let minML := fus.tail.foldl (fun acc u => min acc u.minLayer)
            (fus.head?.map FallingUnit.minLayer |>.getD 0)
        let settling := fus.filter fun u => u.minLayer == minML
        let settlingPos := settling.flatMap FallingUnit.positions
        let obs := (s.clearPositions settlingPos).layers
        let sortedSettling := settling.mergeSort
            (fun a b => landingDistance a obs ≤ landingDistance b obs)
        (waveStep s).layers = placeLDGroups s sortedSettling obs := by
    simp only [waveStep, h, Bool.false_eq_true, ↓reduceIte]
    set settlingPos :=
        ((floatingUnits s).filter (fun u => u.minLayer ==
            (floatingUnits s).tail.foldl (fun acc u => min acc u.minLayer)
                ((floatingUnits s).head?.map FallingUnit.minLayer |>.getD 0))).flatMap
                FallingUnit.positions
    set obs := (s.clearPositions settlingPos).layers
    set sortedSettling := ((floatingUnits s).filter (fun u => u.minLayer ==
        (floatingUnits s).tail.foldl (fun acc u => min acc u.minLayer)
            ((floatingUnits s).head?.map FallingUnit.minLayer |>.getD 0))).mergeSort
        (fun a b => landingDistance a obs ≤ landingDistance b obs)
    have h_obs_ne : obs ≠ [] := clearPositions_layers_ne_nil s settlingPos
    have h_isSome := placeLDGroups_ofLayers_isSome s sortedSettling obs h_obs_ne
    cases h_match : Shape.ofLayers (placeLDGroups s sortedSettling obs) with
    | none => rw [h_match] at h_isSome; simp at h_isSome
    | some s' =>
        -- `Shape.ofLayers` の定義から `s'.layers = placeLDGroups ...`
        cases h_case : placeLDGroups s sortedSettling obs with
        | nil =>
            rw [h_case] at h_match
            simp only [Shape.ofLayers] at h_match
            exact absurd h_match (by simp)
        | cons l ls =>
            rw [h_case] at h_match
            simp only [Shape.ofLayers] at h_match
            have : s' = ⟨l :: ls, List.cons_ne_nil l ls⟩ := (Option.some.inj h_match).symm
            rw [this]

-- ============================================================
-- S1 追加補題: foldl min の達成値 + settling 非空性
-- ============================================================

/-- foldl min の結果は元リストの要素と一致するか、init と一致する -/
private theorem foldl_min_mem_or_eq_init (init : Nat) (l : List FallingUnit) :
        (∃ u ∈ l, u.minLayer = l.foldl (fun acc u => min acc u.minLayer) init) ∨
        l.foldl (fun acc u => min acc u.minLayer) init = init := by
    induction l generalizing init with
    | nil => exact .inr rfl
    | cons u rest ih =>
        simp only [List.foldl_cons]
        rcases ih (min init u.minLayer) with ⟨v, hv_mem, hv_eq⟩ | heq
        · exact .inl ⟨v, List.mem_cons_of_mem u hv_mem, hv_eq⟩
        · rw [heq]
          rcases Nat.le_total init u.minLayer with hle | hle
          · simp [Nat.min_eq_left hle]
          · rw [show min init u.minLayer = u.minLayer from by rwa [Nat.min_comm, Nat.min_eq_left]]
            exact .inl ⟨u, List.Mem.head _, rfl⟩

/-- fus ≠ [] のとき、最小 minLayer を持つ FU が必ず settling に含まれる（settling ≠ []）-/
theorem settling_nonempty (fus : List FallingUnit) (h : fus.isEmpty = false) :
        let minML := fus.tail.foldl (fun acc u => min acc u.minLayer)
            (fus.head?.map FallingUnit.minLayer |>.getD 0)
        (fus.filter (fun u => u.minLayer == minML)) ≠ [] := by
    have hne : fus ≠ [] := by
        cases fus with
        | nil => simp at h
        | cons _ _ => exact List.cons_ne_nil _ _
    cases hfus : fus with
    | nil => exact absurd hfus hne
    | cons hd tl =>
        simp only [List.head?, Option.map_some, Option.getD_some, List.tail_cons]
        set minML := tl.foldl (fun acc u => min acc u.minLayer) hd.minLayer
        have hachieve : ∃ u ∈ hd :: tl, u.minLayer = minML := by
            rcases foldl_min_mem_or_eq_init hd.minLayer tl with ⟨v, hv_mem, hv_eq⟩ | heq
            · exact ⟨v, List.mem_cons_of_mem hd hv_mem, hv_eq⟩
            · exact ⟨hd, List.Mem.head _, heq.symm⟩
        obtain ⟨u, hu_mem, hu_eq⟩ := hachieve
        intro hnil
        have : u ∈ List.filter (fun u => u.minLayer == minML) (hd :: tl) :=
            List.mem_filter.mpr ⟨hu_mem, by simp [hu_eq]⟩
        rw [hnil] at this
        exact List.not_mem_nil this

-- ============================================================
-- 終端性補題
-- ============================================================

/-- filter 分割による長さ等式: |filter p| + |filter ¬p| = |l| -/
private theorem filter_length_partition (l : List FallingUnit) (p : FallingUnit → Bool) :
        (l.filter p).length + (l.filter (fun x => !p x)).length = l.length := by
    induction l with
    | nil => simp
    | cons x xs ih =>
        simp only [List.filter_cons]
        cases p x <;> simp_all <;> omega

/-- 非クリア位置に対して groundingEdge は clearPositions で保存される -/
private theorem groundingEdge_clearPositions_of_not_mem
        (s : Shape) (ps : List QuarterPos) (a b : QuarterPos)
        (ha : (ps.any (· == a)) = false)
        (hb : (ps.any (· == b)) = false)
        (ha_lt : a.layer < s.layerCount)
        (hb_lt : b.layer < s.layerCount) :
        groundingEdge (s.clearPositions ps) a b = groundingEdge s a b := by
    have hqa : a.getQuarter (s.clearPositions ps) = a.getQuarter s := by
        rw [QuarterPos.getQuarter_clearPositions s ps a ha_lt, ha]; rfl
    have hqb : b.getQuarter (s.clearPositions ps) = b.getQuarter s := by
        rw [QuarterPos.getQuarter_clearPositions s ps b hb_lt, hb]; rfl
    simp only [groundingEdge, isUpwardGroundingContact, isStructurallyBonded, isGroundingContact]
    rw [hqa, hqb]

/-- 浮遊単位の全位置は接地されていない -/
private theorem floatingUnit_positions_not_grounded
        (s : Shape) (u : FallingUnit) (hu : u ∈ floatingUnits s)
        (p : QuarterPos) (hp : p ∈ u.positions) :
        p ∉ groundedPositions s := by
    -- floatingUnits の定義: floating clusters (all ∉ grounded) ++ floating pins (∉ grounded)
    simp only [floatingUnits, List.mem_append, List.mem_map, List.mem_filter] at hu
    rcases hu with ⟨cluster, ⟨_, h_all⟩, hcl_eq⟩ | ⟨pinPos, ⟨_, h_ng⟩, hpin_eq⟩
    · -- cluster case
      subst hcl_eq
      simp only [FallingUnit.positions] at hp
      have := List.all_eq_true.mp h_all p hp
      simpa using this
    · -- pin case
      subst hpin_eq
      simp only [FallingUnit.positions, List.mem_singleton] at hp
      subst hp; simpa using h_ng

-- ============================================================
-- BFS 基盤補題 (Equivariance.lean のローカル版。終端性証明に必要)
-- ============================================================

/-- groundingBfs は genericBfs (groundingEdge s) と等価 -/
private theorem groundingBfs_eq_generic' (s : Shape)
        (allPos vis queue : List QuarterPos) (fuel : Nat) :
        groundingBfs s allPos vis queue fuel =
        genericBfs (groundingEdge s) allPos vis queue fuel := by
    induction fuel generalizing vis queue with
    | zero => rfl
    | succ n ih =>
        cases queue with
        | nil => rfl
        | cons pos rest =>
            simp only [groundingBfs, genericBfs]
            split <;> exact ih ..

/-- structuralBfs は genericBfs (isStructurallyBonded s) と等しい（ローカル版）-/
private theorem structuralBfs_eq_generic' (s : Shape)
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

/-- isGroundingContact → q.layer < s.layerCount -/
private theorem isGroundingContact_valid' (s : Shape) (p q : QuarterPos)
        (h : isGroundingContact s p q = true) : q.layer < s.layerCount := by
    simp only [isGroundingContact] at h
    cases hq : q.getQuarter s with
    | none => simp only [hq, reduceCtorEq, imp_self, implies_true, Bool.false_eq_true] at h
    | some _ =>
        simp only [Shape.layerCount]
        unfold QuarterPos.getQuarter at hq
        cases hl : s.layers[q.layer]? with
        | none => simp only [hl, reduceCtorEq] at hq
        | some _ => exact (List.getElem?_eq_some_iff.mp hl).1

/-- isGroundingContact → p.layer < s.layerCount -/
private theorem isGroundingContact_valid_fst' (s : Shape) (p q : QuarterPos)
        (h : isGroundingContact s p q = true) : p.layer < s.layerCount := by
    simp only [isGroundingContact] at h
    cases hp : p.getQuarter s with
    | none => simp only [hp, Bool.false_eq_true] at h
    | some _ =>
        simp only [Shape.layerCount]
        unfold QuarterPos.getQuarter at hp
        cases hl : s.layers[p.layer]? with
        | none => simp only [hl, reduceCtorEq] at hp
        | some _ => exact (List.getElem?_eq_some_iff.mp hl).1

/-- allValid メンバーシップ → layer 有効性 -/
theorem allValid_mem_layer_lt' {s : Shape} {p : QuarterPos}
        (h : p ∈ QuarterPos.allValid s) : p.layer < s.layerCount := by
    simp only [QuarterPos.allValid, List.mem_flatMap] at h
    obtain ⟨li, hli, hdir⟩ := h
    rw [List.mem_map] at hdir
    obtain ⟨_, _, h_mk⟩ := hdir
    rw [← h_mk]; exact List.mem_range.mp hli

/-- allValid の .any ↔ layer < layerCount -/
private theorem allValid_any_iff_layer (s : Shape) (p : QuarterPos) :
        (QuarterPos.allValid s).any (· == p) = true ↔ p.layer < s.layerCount := by
    constructor
    · intro h
      rw [List.any_eq_true] at h
      obtain ⟨x, h_mem, h_eq⟩ := h; have := eq_of_beq h_eq; subst this
      exact allValid_mem_layer_lt' h_mem
    · intro h
      exact List.any_eq_true.mpr ⟨p, by
          simp only [QuarterPos.allValid, List.mem_flatMap]
          exact ⟨p.layer, List.mem_range.mpr h,
              List.mem_map.mpr ⟨p.dir, List.mem_of_elem_eq_true (by cases p.dir <;> rfl),
                  by cases p; rfl⟩⟩,
          BEq.rfl⟩

/-- allValid の長さ = layerCount * 4 -/
private theorem allValid_length (s : Shape) :
        (QuarterPos.allValid s).length = s.layerCount * 4 := by
    simp only [QuarterPos.allValid, Shape.layerCount]
    generalize s.layers.length = n
    induction n with
    | zero => simp only [List.range_zero, List.flatMap_nil, List.length_nil, Nat.zero_mul]
    | succ k ih =>
        rw [List.range_succ, List.flatMap_append, List.length_append, ih]
        simp only [Direction.all, List.map_cons, List.map, List.flatMap_cons, List.flatMap_nil,
                    List.append_nil, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
        omega

/-- groundedPositionsList の健全性: BFS 結果 → seed から GenericReachable -/
private theorem groundedPositionsList_sound' (s : Shape) (p : QuarterPos)
        (h : (groundedPositionsList s).any (· == p) = true) :
        ∃ seed, seed ∈ (QuarterPos.allValid s).filter (fun q =>
            q.layer == 0 && match q.getQuarter s with
            | some q => !q.isEmpty | none => false) ∧
        GenericReachable (groundingEdge s) seed p := by
    unfold groundedPositionsList at h
    rw [groundingBfs_eq_generic'] at h
    match genericBfs_sound (groundingEdge s) (QuarterPos.allValid s) []
            _ _ p h with
    | .inl h_vis => simp only [List.any, Bool.false_eq_true] at h_vis
    | .inr ⟨seed, h_seed, h_reach⟩ =>
        exact ⟨seed, by
            rw [List.any_eq_true] at h_seed
            obtain ⟨y, hy, hye⟩ := h_seed; exact eq_of_beq hye ▸ hy,
            h_reach⟩

/-- groundedPositionsList の fuel 下界 -/
private theorem groundedPositionsList_fuel_adequate' (s : Shape) :
        (s.layerCount * 4 * (s.layerCount * 4) + s.layerCount * 4) + 1 ≥
            ((QuarterPos.allValid s).filter fun p =>
                p.layer == 0 && match p.getQuarter s with
                | some q => !q.isEmpty | none => false).length +
            ((QuarterPos.allValid s).filter fun p =>
                !(([] : List QuarterPos).any (· == p))).length *
            ((QuarterPos.allValid s).filter fun p =>
                !(([] : List QuarterPos).any (· == p))).length := by
    have h_filter : (QuarterPos.allValid s).filter (fun p =>
            !(([] : List QuarterPos).any (· == p))) = QuarterPos.allValid s :=
        List.filter_eq_self.mpr (by intro x _; simp only [List.any, Bool.not_false])
    simp only [h_filter, allValid_length]
    have := List.length_filter_le (fun p =>
        p.layer == 0 && match p.getQuarter s with
        | some q => !q.isEmpty | none => false) (QuarterPos.allValid s)
    rw [allValid_length s] at this
    omega

/-- groundedPositionsList の完全性: seed から GenericReachable → BFS 結果に含まれる -/
private theorem groundedPositionsList_complete' (s : Shape) (seed p : QuarterPos)
        (h_seed : seed ∈ (QuarterPos.allValid s).filter (fun q =>
            q.layer == 0 && match q.getQuarter s with
            | some q => !q.isEmpty | none => false))
        (h_reach : GenericReachable (groundingEdge s) seed p) :
        (groundedPositionsList s).any (· == p) = true := by
    unfold groundedPositionsList; rw [groundingBfs_eq_generic']
    have h_fuel := groundedPositionsList_fuel_adequate' s
    have h_seed_in := genericBfs_queue_in_result
        (groundingEdge s) (QuarterPos.allValid s) []
        ((QuarterPos.allValid s).filter fun p =>
            p.layer == 0 && match p.getQuarter s with
            | some q => !q.isEmpty | none => false)
        (s.layerCount * 4 * (s.layerCount * 4) + s.layerCount * 4)
        seed
        (.inr (List.any_eq_true.mpr ⟨seed, h_seed, BEq.rfl⟩))
        ((allValid_any_iff_layer s seed).mpr (allValid_mem_layer_lt' (List.mem_filter.mp h_seed).1))
        h_fuel
        (fun a b h =>
            (allValid_any_iff_layer s a).mpr
                (isGroundingContact_valid_fst' s a b (groundingEdge_base h)))
    have h_inv := genericBfs_invariant_preserved (groundingEdge s)
        (QuarterPos.allValid s) []
        ((QuarterPos.allValid s).filter fun p =>
            p.layer == 0 && match p.getQuarter s with
            | some q => !q.isEmpty | none => false)
        (s.layerCount * 4 * (s.layerCount * 4) + s.layerCount * 4)
        (by intro v hv; simp only [List.any, Bool.false_eq_true] at hv)
        h_fuel
        (fun p q h =>
            (allValid_any_iff_layer s p).mpr
                (isGroundingContact_valid_fst' s p q (groundingEdge_base h)))
    exact genericBfs_closed_contains_reachable _ _ _ h_inv
        seed p h_seed_in h_reach
        (fun q r h_bond =>
            (allValid_any_iff_layer s r).mpr
                (isGroundingContact_valid' s q r (groundingEdge_base h_bond)))

-- ============================================================
-- 接地保存: 浮遊位置クリアで既存の接地は壊れない
-- ============================================================

/-- groundedPositions → groundedPositionsList の .any 表現への変換 -/
private theorem mem_groundedPositionsList_of_mem_groundedPositions
        {s : Shape} {q : QuarterPos} (h : q ∈ groundedPositions s) :
        (groundedPositionsList s).any (· == q) = true := by
    rw [groundedPositions, List.mem_toFinset] at h
    exact List.any_eq_true.mpr ⟨q, h, BEq.rfl⟩

/-- groundedPositionsList の .any 表現 → groundedPositions メンバーシップへの変換 -/
private theorem mem_groundedPositions_of_any
        {s : Shape} {q : QuarterPos}
        (h : (groundedPositionsList s).any (· == q) = true) :
        q ∈ groundedPositions s := by
    rw [groundedPositions, List.mem_toFinset]
    rw [List.any_eq_true] at h
    obtain ⟨x, hx, hxq⟩ := h
    exact eq_of_beq hxq ▸ hx

/-- レイヤ 0 の非空位置は常に接地される（BFS のシード条件を直接満たすため）-/
theorem layer_zero_nonempty_grounded
        (s : Shape) (p : QuarterPos)
        (h_av : p ∈ QuarterPos.allValid s)
        (h_layer : p.layer = 0)
        (q : Quarter) (hq : p.getQuarter s = some q) (hne : q.isEmpty = false) :
        p ∈ groundedPositions s := by
    apply mem_groundedPositions_of_any
    have h_seed : p ∈ (QuarterPos.allValid s).filter (fun r =>
            r.layer == 0 && match r.getQuarter s with
            | some q => !q.isEmpty | none => false) := by
        rw [List.mem_filter]
        constructor
        · exact h_av
        · have h1 : (p.layer == 0) = true := by rw [h_layer]; rfl
          have h2 : (match p.getQuarter s with | some q => !q.isEmpty | none => false) = true := by
            simp only [hq, hne]
            decide
          rw [Bool.and_eq_true]; exact ⟨h1, h2⟩
    exact groundedPositionsList_complete' s p p h_seed .refl

/-- 接地の 1 ステップ伝播: `a` が接地かつ `groundingEdge s a b = true` なら `b` も接地。
    `groundedPositionsList` の健全性・完全性を合成した基本補題。 -/
theorem grounded_of_edge {s : Shape} {a b : QuarterPos}
        (h_a : a ∈ groundedPositions s)
        (h_edge : groundingEdge s a b = true) :
        b ∈ groundedPositions s := by
    have h_any := mem_groundedPositionsList_of_mem_groundedPositions h_a
    obtain ⟨seed, h_seed, h_reach⟩ := groundedPositionsList_sound' s a h_any
    have h_reach' : GenericReachable (groundingEdge s) seed b :=
        h_reach.trans (.step h_edge .refl)
    exact mem_groundedPositions_of_any
        (groundedPositionsList_complete' s seed b h_seed h_reach')

/-- 浮遊ピン（layer = 1, ungrounded）の直下セル `(0, dir)` は `s` で空である。
    もし非空なら layer 0 シード条件で `(0, dir)` が接地 → `isUpwardGroundingContact`
    でピン `q` に接地が伝播 → 浮遊仮定と矛盾。
    S1 #4 (pin_singleton_landing_empty) の d = 1 floor 接触ケースの核補題。 -/
theorem ungrounded_pin_layer_one_below_empty
        (s : Shape) (q : QuarterPos)
        (h_av : q ∈ QuarterPos.allValid s)
        (h_pin : q.getQuarter s = some .pin)
        (h_layer : q.layer = 1)
        (h_ung : q ∉ groundedPositions s) :
        isOccupied s.layers 0 q.dir = false := by
    by_contra h_occ
    rw [Bool.not_eq_false] at h_occ
    -- layerCount ≥ 1
    have h_lc : 0 < s.layerCount := by
        have := allValid_mem_layer_lt' h_av
        rw [h_layer] at this; omega
    -- (0, q.dir) ∈ allValid
    have h_av0 : (⟨0, q.dir⟩ : QuarterPos) ∈ QuarterPos.allValid s := by
        simp only [QuarterPos.allValid, List.mem_flatMap, List.mem_map, List.mem_range]
        exact ⟨0, h_lc, q.dir, List.mem_of_elem_eq_true (by cases q.dir <;> rfl), rfl⟩
    -- isOccupied から (0, q.dir) の非空象限 l0 を抽出
    have h_lookup : ∃ l0, s.layers[0]? = some l0 ∧
            (QuarterPos.getDir l0 q.dir).isEmpty = false := by
        simp only [isOccupied] at h_occ
        split at h_occ
        · rename_i l h_eq
          refine ⟨l, h_eq, ?_⟩
          simp only [Bool.not_eq_true'] at h_occ; exact h_occ
        · exact absurd h_occ (by decide)
    obtain ⟨l0, h_l0, h_ne⟩ := h_lookup
    -- (0, q.dir).getQuarter = some (getDir l0 q.dir)
    have h_gq : (⟨0, q.dir⟩ : QuarterPos).getQuarter s =
            some (QuarterPos.getDir l0 q.dir) := by
        simp only [QuarterPos.getQuarter]; rw [h_l0]
    -- (0, q.dir) ∈ groundedPositions (layer 0 シード)
    have h_grd : (⟨0, q.dir⟩ : QuarterPos) ∈ groundedPositions s :=
        layer_zero_nonempty_grounded s ⟨0, q.dir⟩ h_av0 rfl
            (QuarterPos.getDir l0 q.dir) h_gq h_ne
    -- isGroundingContact s (0, q.dir) q = true
    have h_gc : isGroundingContact s ⟨0, q.dir⟩ q = true := by
        simp only [isGroundingContact]
        rw [h_gq, h_pin]
        have h_pin_ne : Quarter.isEmpty Quarter.pin = false := by decide
        have h_va : LayerIndex.verticallyAdjacent 0 q.layer = true := by
            rw [h_layer]; decide
        simp only [h_ne, h_pin_ne, Bool.not_false, Bool.and_true,
            beq_self_eq_true, h_va, Bool.true_or]
    -- isUpwardGroundingContact (0 ≤ 1)
    have h_upw : isUpwardGroundingContact s ⟨0, q.dir⟩ q = true :=
        isGroundingContact_to_isUpwardGroundingContact h_gc
            (show (0 : Nat) ≤ q.layer by rw [h_layer]; omega)
    -- groundingEdge 成立 → grounded_of_edge で q 接地
    have h_edge : groundingEdge s ⟨0, q.dir⟩ q = true :=
        groundingEdge_of_isUpwardGroundingContact h_upw
    exact h_ung (grounded_of_edge h_grd h_edge)

/-- 接地位置はクリア対象に含まれない -/
private theorem not_any_ps_of_grounded
        {s : Shape} {ps : List QuarterPos} {p : QuarterPos}
        (h_floating : ∀ x ∈ ps, x ∉ groundedPositions s)
        (hp : (groundedPositionsList s).any (· == p) = true) :
        (ps.any (· == p)) = false := by
    by_contra h
    rw [Bool.not_eq_false] at h
    rw [List.any_eq_true] at h
    obtain ⟨x, hx, hxp⟩ := h
    exact h_floating x hx (eq_of_beq hxp ▸ mem_groundedPositions_of_any hp)

/-- allValid は layerCount のみに依存する -/
theorem allValid_eq_of_layerCount {s₁ s₂ : Shape}
        (h : s₁.layerCount = s₂.layerCount) :
        QuarterPos.allValid s₁ = QuarterPos.allValid s₂ := by
    unfold QuarterPos.allValid; rw [h]

/-- allValid メンバーシップ → layer 有効性（ローカル版） -/
theorem allValid_mem_layer_lt {s : Shape} {p : QuarterPos}
        (h : p ∈ QuarterPos.allValid s) : p.layer < s.layerCount := by
    simp only [QuarterPos.allValid, List.mem_flatMap] at h
    obtain ⟨li, hli, hdir⟩ := h
    rw [List.mem_map] at hdir
    obtain ⟨_, _, h_mk⟩ := hdir
    rw [← h_mk]; exact List.mem_range.mp hli

/-- 浮遊位置のクリアは接地を保存する: 全クリア位置が非接地なら、接地位置は接地のまま。

    数学的根拠:
    - 接地 = layer-0 非空シードから groundingEdge で到達可能
    - 到達パス上の全ノードは接地（BFS 閉包性）
    - クリア位置は非接地 → パスに含まれない
    - groundingEdge はクリアされないノードのペアで保存される
    - GenericReachable.edge_preserve_of_reachable で到達可能性を転送
    - シードは接地→クリアされない→clearPositions 後も有効 -/
private theorem clearPositions_preserves_grounded
        (s : Shape) (ps : List QuarterPos)
        (h_floating : ∀ p ∈ ps, p ∉ groundedPositions s)
        (q : QuarterPos) (hq : q ∈ groundedPositions s) :
        q ∈ groundedPositions (s.clearPositions ps) := by
    -- (1) Finset → BFS-list any
    have hq_any := mem_groundedPositionsList_of_mem_groundedPositions hq
    -- (2) Get seed and reachability
    obtain ⟨seed, h_seed_mem, h_reach⟩ := groundedPositionsList_sound' s q hq_any
    -- (3) Transfer reachability: groundingEdge s → groundingEdge (s.clearPositions ps)
    have h_reach' : GenericReachable (groundingEdge (s.clearPositions ps)) seed q :=
        h_reach.edge_preserve_of_reachable (fun p r hp_reach h_edge => by
            -- p is reachable from seed, hence in groundedPositionsList
            have hp_any := groundedPositionsList_complete' s seed p h_seed_mem hp_reach
            -- r = one more step from p, also in groundedPositionsList
            have hr_any := groundedPositionsList_complete' s seed r h_seed_mem
                (hp_reach.trans (.step h_edge .refl))
            -- p, r ∉ ps (grounded → not in floating ps)
            have hp_nps := not_any_ps_of_grounded h_floating hp_any
            have hr_nps := not_any_ps_of_grounded h_floating hr_any
            -- layer validity from groundingEdge → isGroundingContact
            have h_gc := groundingEdge_base h_edge
            have hp_lt := isGroundingContact_valid_fst' s p r h_gc
            have hr_lt := isGroundingContact_valid' s p r h_gc
            -- edge preservation
            rw [groundingEdge_clearPositions_of_not_mem s ps p r hp_nps hr_nps hp_lt hr_lt]
            exact h_edge)
    -- (4) Seed is still valid for s.clearPositions ps
    have h_seed_filter : seed ∈ (QuarterPos.allValid s).filter (fun q =>
            q.layer == 0 && match q.getQuarter s with
            | some q => !q.isEmpty | none => false) := h_seed_mem
    rw [List.mem_filter] at h_seed_filter
    obtain ⟨h_av, h_cond⟩ := h_seed_filter
    -- seed is grounded, hence not in ps
    have h_seed_any : (groundedPositionsList s).any (· == seed) = true :=
        groundedPositionsList_complete' s seed seed h_seed_mem .refl
    have h_seed_nps := not_any_ps_of_grounded h_floating h_seed_any
    have h_seed_lt := allValid_mem_layer_lt' h_av
    -- seed filter condition preserved
    have h_seed_mem' : seed ∈ (QuarterPos.allValid (s.clearPositions ps)).filter (fun q =>
            q.layer == 0 && match q.getQuarter (s.clearPositions ps) with
            | some q => !q.isEmpty | none => false) := by
        rw [List.mem_filter]
        constructor
        · rw [allValid_eq_of_layerCount (Shape.layerCount_clearPositions s ps)]; exact h_av
        · -- getQuarter preserved for seed
          rw [QuarterPos.getQuarter_clearPositions s ps seed h_seed_lt, h_seed_nps]
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact h_cond
    -- (5) Apply completeness for s.clearPositions ps
    exact mem_groundedPositions_of_any
        (groundedPositionsList_complete' (s.clearPositions ps) seed q h_seed_mem' h_reach')

/-- 構造結合による接地伝播: p→q の構造結合パスがあり q が接地されていれば p も接地される。
    証明: isStructurallyBonded の対称性 → 逆パス q→p → groundingEdge に変換 →
    groundedPositionsList_closed で伝播 -/
private theorem grounding_propagates_structural
        (s : Shape) (p q : QuarterPos)
        (h_bond_path : GenericReachable (fun a b => isStructurallyBonded s a b) p q)
        (h_grounded : q ∈ groundedPositions s) :
        p ∈ groundedPositions s := by
    have h_any_q := mem_groundedPositionsList_of_mem_groundedPositions h_grounded
    obtain ⟨seed, h_seed, h_seed_q⟩ := groundedPositionsList_sound' s q h_any_q
    have h_qp := h_bond_path.symm (fun a b => isStructurallyBonded_symm s a b)
    have h_ge_qp := h_qp.mono (fun a b h => groundingEdge_of_isStructurallyBonded h)
    have h_seed_p := h_seed_q.trans h_ge_qp
    exact mem_groundedPositions_of_any (groundedPositionsList_complete' s seed p h_seed h_seed_p)

/-- 浮遊位置のクリアは接地集合の逆包含を保つ:
    クリア位置が非接地ならば、クリア後に接地している位置は元のシェイプでも接地している。

    数学的根拠:
    - クリアされた位置は obs で空象限（getQuarter = some .empty）
    - groundingEdge は isGroundingContact を経由し、両端点に非空象限を要求する
    - BFS パス上の全ノードはエッジの端点として非空 → ps に含まれない
    - 非クリア位置同士の groundingEdge は s と obs で保存される
    - seed は非空(obs) → ps に含まれない → s でも同条件成立
    - 到達可能性が s に転送できるため、obs での接地位置は s でも接地 -/
private theorem clearPositions_grounded_reverse
        (s : Shape) (ps : List QuarterPos)
        (_h_floating : ∀ p ∈ ps, p ∉ groundedPositions s)
        (q : QuarterPos) (hq : q ∈ groundedPositions (s.clearPositions ps)) :
        q ∈ groundedPositions s := by
    -- (1) Finset → BFS-list any
    have hq_any := mem_groundedPositionsList_of_mem_groundedPositions hq
    -- (2) Get seed and reachability in obs
    obtain ⟨seed, h_seed_mem, h_reach⟩ :=
        groundedPositionsList_sound' (s.clearPositions ps) q hq_any
    -- (3) Transfer path: groundingEdge obs → groundingEdge s
    -- All path positions have non-empty content in obs, so they're not in ps.
    have h_reach' : GenericReachable (groundingEdge s) seed q :=
        h_reach.edge_preserve_of_reachable (fun p r _hp_reach h_edge => by
            -- Both endpoints have non-empty content in obs
            have hp_gc := groundingEdge_base h_edge
            obtain ⟨_, _, hqp, hqr, hne_p, hne_r⟩ :=
                isGroundingContact_nonEmpty _ p r hp_gc
            -- Layer validity (obs → s via layerCount preservation)
            have hp_lt : p.layer < s.layerCount := by
                rw [← Shape.layerCount_clearPositions s ps]
                exact isGroundingContact_valid_fst' _ p r hp_gc
            have hr_lt : r.layer < s.layerCount := by
                rw [← Shape.layerCount_clearPositions s ps]
                exact isGroundingContact_valid' _ p r hp_gc
            -- p ∉ ps: if p ∈ ps then p.getQuarter obs = some .empty, contradicting non-empty
            have hp_nps : (ps.any (· == p)) = false := by
                by_contra h_abs
                rw [Bool.not_eq_false] at h_abs
                have h_clear := QuarterPos.getQuarter_clearPositions s ps p hp_lt
                rw [h_abs] at h_clear; simp only [ite_true] at h_clear
                rw [h_clear] at hqp; cases hqp
                exact absurd hne_p (by decide)
            have hr_nps : (ps.any (· == r)) = false := by
                by_contra h_abs
                rw [Bool.not_eq_false] at h_abs
                have h_clear := QuarterPos.getQuarter_clearPositions s ps r hr_lt
                rw [h_abs] at h_clear; simp only [ite_true] at h_clear
                rw [h_clear] at hqr; cases hqr
                exact absurd hne_r (by decide)
            -- Edge preservation
            rw [groundingEdge_clearPositions_of_not_mem s ps p r hp_nps hr_nps hp_lt hr_lt]
                at h_edge
            exact h_edge)
    -- (4) Seed is still valid for s
    rw [List.mem_filter] at h_seed_mem
    obtain ⟨h_av, h_cond⟩ := h_seed_mem
    -- Seed layer validity
    have h_seed_lt : seed.layer < s.layerCount := by
        rw [← Shape.layerCount_clearPositions s ps]
        exact allValid_mem_layer_lt' h_av
    -- Seed ∉ ps (seed has non-empty content in obs, cleared positions are empty)
    have h_seed_nps : (ps.any (· == seed)) = false := by
        by_contra h_abs
        rw [Bool.not_eq_false] at h_abs
        have h_clear := QuarterPos.getQuarter_clearPositions s ps seed h_seed_lt
        rw [h_abs] at h_clear; simp only [ite_true] at h_clear
        -- h_cond contains match on seed.getQuarter obs; substituting h_clear gives false = true
        rw [h_clear] at h_cond
        simp only [Quarter.isEmpty, Bool.not_true, Bool.and_false, Bool.false_eq_true] at h_cond
    -- Seed filter condition for s (content preserved since seed ∉ ps)
    have h_seed_mem_s : seed ∈ (QuarterPos.allValid s).filter (fun q =>
            q.layer == 0 && match q.getQuarter s with
            | some q => !q.isEmpty | none => false) := by
        rw [List.mem_filter]
        constructor
        · rw [allValid_eq_of_layerCount (Shape.layerCount_clearPositions s ps)] at h_av; exact h_av
        · have h_gq : seed.getQuarter (s.clearPositions ps) = seed.getQuarter s := by
            rw [QuarterPos.getQuarter_clearPositions s ps seed h_seed_lt, h_seed_nps]
            simp only [Bool.false_eq_true, ↓reduceIte]
          rw [← h_gq]; exact h_cond
    -- (5) Apply completeness for s
    exact mem_groundedPositions_of_any
        (groundedPositionsList_complete' s seed q h_seed_mem_s h_reach')

/-- 浮遊位置のクリアは接地集合を保存する（双方向版）。
    clearPositions_preserves_grounded (⊆) と clearPositions_grounded_reverse (⊇) を結合。 -/
private theorem groundedPositions_clearNonGrounded_eq
        (s : Shape) (ps : List QuarterPos)
        (h_floating : ∀ p ∈ ps, p ∉ groundedPositions s) :
        groundedPositions (s.clearPositions ps) = groundedPositions s := by
    ext q
    constructor
    · exact clearPositions_grounded_reverse s ps h_floating q
    · exact clearPositions_preserves_grounded s ps h_floating q

/-- if-then-0 の合計は filter 合計に等しい -/
theorem sum_map_ite_eq_sum_filter {α : Type*} (l : List α) (P : α → Bool) (f : α → Nat) :
        (l.map (fun x => if P x then f x else 0)).sum = ((l.filter P).map f).sum := by
    induction l with
    | nil => simp
    | cons x xs ih =>
        simp only [List.map_cons, List.sum_cons, List.filter_cons]
        cases P x <;> simp [ih]

/-- map (f + g) の合計は map f の合計と map g の合計の和 -/
theorem sum_map_add {α : Type*} (l : List α) (f g : α → Nat) :
        (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
    induction l with
    | nil => simp
    | cons x xs ih =>
        simp only [List.map_cons, List.sum_cons, ih]
        omega

/-- Sub-lemma #3: 浮遊位置のクリアによる NGS の分解。
    NGS(s) = NGS(s.clearPositions ps) + Σ_{p ∈ allValid ∩ ps} ngsWeight(s, p)
    直感: clearing は非接地位置の寄与を除去するだけで、接地集合を保存するため
    残りの位置の寄与は不変。 -/
theorem nonGroundedLayerSum_clear_add (s : Shape) (ps : List QuarterPos)
        (h_floating : ∀ p ∈ ps, p ∉ groundedPositions s)
        (_h_valid : ∀ p ∈ ps, p.layer < s.layerCount) :
        nonGroundedLayerSum s = nonGroundedLayerSum (s.clearPositions ps)
          + (((QuarterPos.allValid s).filter (fun p => ps.any (· == p))).map (ngsWeight s)).sum := by
    -- (1) 接地集合の保存
    have h_gp_eq := groundedPositions_clearNonGrounded_eq s ps h_floating
    -- (2) allValid の保存
    have h_av_eq := allValid_eq_of_layerCount (Shape.layerCount_clearPositions s ps)
    -- (3) 両辺を ngsWeight の合計に変換
    rw [nonGroundedLayerSum_eq_sum s, nonGroundedLayerSum_eq_sum (s.clearPositions ps), h_av_eq]
    -- Goal: (L.map (ngsWeight s)).sum
    --     = (L.map (ngsWeight obs)).sum + ((L.filter P).map (ngsWeight s)).sum
    -- (4) 点別恒等式: ngsWeight s p = ngsWeight obs p + (if p ∈ ps then ngsWeight s p else 0)
    have h_pw : ∀ p ∈ QuarterPos.allValid s,
            ngsWeight s p = ngsWeight (s.clearPositions ps) p
              + (if ps.any (· == p) then ngsWeight s p else 0) := by
        intro p hp
        have hp_lt := allValid_mem_layer_lt hp
        cases h_mem : ps.any (· == p)
        · -- p ∉ ps: ngsWeight obs p = ngsWeight s p
          simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
          exact (ngsWeight_clearPositions_not_mem s ps h_gp_eq p h_mem hp_lt).symm
        · -- p ∈ ps: ngsWeight obs p = 0
          simp only [ite_true]
          rw [ngsWeight_clearPositions_mem s ps p h_mem hp_lt, Nat.zero_add]
    -- (5) map congr + sum_map_add で分解
    conv_lhs =>
        rw [show (QuarterPos.allValid s).map (ngsWeight s)
              = (QuarterPos.allValid s).map (fun p =>
                  ngsWeight (s.clearPositions ps) p
                    + (if ps.any (· == p) then ngsWeight s p else 0))
            from List.map_congr_left h_pw]
    rw [sum_map_add, sum_map_ite_eq_sum_filter]

-- ============================================================
-- landingDistance の下限 (Sub-lemma #9 の基盤)
-- ============================================================

/-- landingDistance.check は min d maxDrop 以上の値を返す -/
private theorem landingDistance_check_ge_min (obstacle : List Layer)
        (positions : List QuarterPos) (maxDrop d fuel : Nat) :
        landingDistance.check obstacle positions maxDrop d fuel ≥ min d maxDrop := by
    induction fuel generalizing d with
    | zero => simp [landingDistance.check]
    | succ n ih =>
        simp [landingDistance.check]
        split
        · -- d > maxDrop: returns maxDrop
          omega
        · -- d ≤ maxDrop
          split
          · -- landed: returns d
            omega
          · -- not landed: recurse with d+1
            have := ih (d + 1)
            omega

/-- 着地距離は minLayer ≥ 1 の FU に対して 1 以上。
    landingDistance は check 1 (minLayer + 1) で呼ばれ、
    check は min d maxDrop 以上を返すため、min 1 minLayer = 1 以上。 -/
private theorem landingDistance_ge_one (u : FallingUnit) (obstacle : List Layer)
        (h_ml : u.minLayer ≥ 1) :
        landingDistance u obstacle ≥ 1 := by
    unfold landingDistance
    have h := landingDistance_check_ge_min obstacle u.positions u.minLayer 1 (u.minLayer + 1)
    have hmin : min 1 u.minLayer = 1 := Nat.min_eq_left h_ml
    rw [hmin] at h
    exact h

-- ============================================================
-- floatingUnits の Nodup 性 (Sub-claim A の基盤)
-- ============================================================

/-- allValid は Nodup（各 QuarterPos は一意）-/
theorem allValid_nodup (s : Shape) : (QuarterPos.allValid s).Nodup := by
    simp only [QuarterPos.allValid]
    rw [List.nodup_flatMap]
    constructor
    · intro li _
      apply List.Nodup.map
      · intro d1 d2 h; exact QuarterPos.mk.inj h |>.2
      · simp only [Direction.all]; decide
    · apply List.Pairwise.imp _ (List.nodup_range.pairwise_of_forall_ne fun a _ b _ h => h)
      intro a b hab p hp1 hp2
      simp only [List.mem_map] at hp1 hp2
      obtain ⟨d1, _, rfl⟩ := hp1
      obtain ⟨d2, _, h⟩ := hp2
      have := QuarterPos.mk.inj h |>.1; omega

/-- allStructuralClustersList は Nodup（各クラスタは一意のリスト）。
    foldl 不変条件: 新クラスタの seed は既存クラスタに含まれない →
    新クラスタは既存クラスタと異なる → Nodup 保存 -/
theorem allStructuralClustersList_nodup (s : Shape) :
        (allStructuralClustersList s).Nodup := by
    unfold allStructuralClustersList
    suffices ∀ (remaining : List QuarterPos) (acc : List (List QuarterPos)),
        acc.Nodup →
        (∀ pos ∈ remaining, pos.layer < s.layerCount) →
        (remaining.foldl (fun clusters pos =>
            if clusters.any (fun cluster => cluster.any (· == pos)) then clusters
            else clusters ++ [structuralClusterList s pos]) acc).Nodup by
      exact this _ [] List.nodup_nil (fun pos h_mem => by
          rw [List.mem_filter] at h_mem
          exact (allValid_any_iff_layer s pos).mp
              (List.any_eq_true.mpr ⟨pos, h_mem.1, BEq.rfl⟩))
    intro remaining
    induction remaining with
    | nil => intro acc h_nd _; exact h_nd
    | cons pos rest ih =>
      intro acc h_nd h_props
      have h_pos_layer := h_props pos (.head _)
      have h_rest_props := fun p hp => h_props p (.tail _ hp)
      dsimp only [List.foldl]
      split <;> rename_i h_cov
      · exact ih acc h_nd h_rest_props
      · apply ih _ _ h_rest_props
        rw [List.nodup_append]
        refine ⟨h_nd, List.nodup_singleton _, ?_⟩
        intro c hc_in_acc c' hc'_in_new
        rw [List.mem_singleton] at hc'_in_new
        subst hc'_in_new
        -- c ∈ acc, need c ≠ structuralClusterList s pos
        -- seed pos is in structuralClusterList s pos
        have h_pos_in : (structuralClusterList s pos).any (· == pos) = true := by
            unfold structuralClusterList; rw [structuralBfs_eq_generic']
            exact genericBfs_contains_start _ _ _ _ (Nat.mul_pos (by omega) (by omega))
        -- pos is NOT in c (c ∈ acc, coverage check failed)
        have h_pos_not : c.any (· == pos) = false := by
            cases hcheck : c.any (· == pos) with
            | false => rfl
            | true =>
              have : acc.any (fun cluster => cluster.any (· == pos)) = true :=
                  List.any_eq_true.mpr ⟨c, hc_in_acc, hcheck⟩
              rw [this] at h_cov; exact absurd h_cov (by decide)
        -- c ≠ structuralClusterList s pos
        intro h_eq
        rw [h_eq] at h_pos_not
        rw [h_pos_in] at h_pos_not
        exact absurd h_pos_not (by decide)
/-- floatingUnits は Nodup: 構造クラスタの互いに素性 + ピンの一意性 + 異なるコンストラクタの分離 -/
theorem floatingUnits_nodup (s : Shape) : (floatingUnits s).Nodup := by
    unfold floatingUnits
    apply List.Nodup.append
    · -- Nodup of clusters.map .cluster
      apply List.Nodup.map
      · intro a b h; exact FallingUnit.cluster.inj h
      · exact (allStructuralClustersList_nodup s).filter _
    · -- Nodup of pins.map .pin
      apply List.Nodup.map
      · intro a b h; exact FallingUnit.pin.inj h
      · exact ((allValid_nodup s).filter _).filter _
    · -- Disjoint: .cluster ≠ .pin
      simp only [List.Disjoint, List.mem_map]
      intro x ⟨_, _, hx⟩ ⟨_, _, hy⟩
      rw [← hy] at hx
      exact FallingUnit.noConfusion hx

/-- Sub-claim B2: floatingUnits の任意の FU の全位置は非接地。
    floatingUnits の定義（非接地フィルター）から直接導出される基本補題。
    `waveStep_nonGroundedLayerSum_lt` の構成的証明で使用予定。 -/
theorem floatingUnits_positions_nongrounded (s : Shape) {u : FallingUnit}
        (hu : u ∈ floatingUnits s) {p : QuarterPos} (hp : p ∈ u.positions) :
        p ∉ groundedPositions s := by
    unfold floatingUnits at hu
    rw [List.mem_append] at hu
    rcases hu with h | h
    · -- cluster ケース
      rw [List.mem_map] at h
      obtain ⟨c, hc, hc_eq⟩ := h
      rw [List.mem_filter] at hc
      obtain ⟨_, h_all⟩ := hc
      subst hc_eq
      simp only [FallingUnit.positions] at hp
      have hdec : decide (p ∉ groundedPositions s) = true :=
          (List.all_eq_true.mp h_all) p hp
      exact of_decide_eq_true hdec
    · -- pin ケース
      rw [List.mem_map] at h
      obtain ⟨p', hp', hp_eq⟩ := h
      rw [List.mem_filter] at hp'
      obtain ⟨_, h_ug⟩ := hp'
      subst hp_eq
      simp only [FallingUnit.positions, List.mem_singleton] at hp
      subst hp
      exact of_decide_eq_true h_ug

/-- Sub-claim B2 の系: filter された settling FU の全位置も非接地。 -/
theorem settling_positions_nongrounded (s : Shape)
        {P : FallingUnit → Bool} {u : FallingUnit}
        (hu : u ∈ (floatingUnits s).filter P) {p : QuarterPos} (hp : p ∈ u.positions) :
        p ∉ groundedPositions s := by
    rw [List.mem_filter] at hu
    exact floatingUnits_positions_nongrounded s hu.1 hp

-- ============================================================
-- S1 基盤補題: FU positions 非空性と minLayer 下界
-- ============================================================

/-- structuralClusterList は BFS シード位置を必ず含む -/
private theorem structuralClusterList_contains_seed (s : Shape) (pos : QuarterPos)
        (h_lc : s.layerCount > 0) :
        (structuralClusterList s pos).any (· == pos) = true := by
    unfold structuralClusterList; rw [structuralBfs_eq_generic']
    exact genericBfs_contains_start _ _ _ _
        (Nat.mul_pos (Nat.mul_pos h_lc (by omega)) (Nat.mul_pos h_lc (by omega)))

/-- allStructuralClustersList の全クラスタは非空（BFS がシードを含むため）-/
private theorem allStructuralClustersList_ne_nil (s : Shape) :
        ∀ c ∈ allStructuralClustersList s, c ≠ [] := by
    unfold allStructuralClustersList
    suffices ∀ (remaining : List QuarterPos) (acc : List (List QuarterPos)),
        (∀ c ∈ acc, c ≠ []) →
        (∀ pos ∈ remaining, pos.layer < s.layerCount) →
        ∀ c, c ∈ remaining.foldl (fun clusters pos =>
            if clusters.any (fun cluster => cluster.any (· == pos)) then clusters
            else clusters ++ [structuralClusterList s pos]) acc → c ≠ [] by
      exact this _ [] (fun _ h => nomatch h) (fun pos h_mem => by
          rw [List.mem_filter] at h_mem
          exact (allValid_any_iff_layer s pos).mp
              (List.any_eq_true.mpr ⟨pos, h_mem.1, BEq.rfl⟩))
    intro remaining
    induction remaining with
    | nil => intro acc h_acc _ c hc; exact h_acc c hc
    | cons pos rest ih =>
      intro acc h_acc h_props c hc
      dsimp only [List.foldl] at hc
      split at hc <;> rename_i h_cov
      · exact ih acc h_acc (fun p hp => h_props p (.tail _ hp)) c hc
      · apply ih (acc ++ [structuralClusterList s pos]) _ (fun p hp => h_props p (.tail _ hp)) c hc
        intro c' hc'
        rw [List.mem_append, List.mem_singleton] at hc'
        rcases hc' with hc_in_acc | hc_eq
        · exact h_acc c' hc_in_acc
        · subst hc_eq; intro h_nil
          have h_lc : s.layerCount > 0 := by
            have := h_props pos (.head _); omega
          have := structuralClusterList_contains_seed s pos h_lc
          rw [h_nil, List.any_nil] at this
          exact absurd this (by decide)

/-- floatingUnits の全 FU は非空の positions を持つ -/
theorem floatingUnits_positions_ne_nil (s : Shape) (u : FallingUnit)
        (hu : u ∈ floatingUnits s) : u.positions ≠ [] := by
    unfold floatingUnits at hu
    rw [List.mem_append, List.mem_map, List.mem_map] at hu
    rcases hu with ⟨ps, hps, hps_eq⟩ | ⟨p, _, hp_eq⟩
    · subst hps_eq
      simp only [FallingUnit.positions]
      rw [List.mem_filter] at hps
      exact allStructuralClustersList_ne_nil s ps hps.1
    · subst hp_eq
      simp only [FallingUnit.positions]
      exact List.cons_ne_nil _ _

-- S1 strict-bound form `NGS(waveStep s) + 1 ≤ NGS(s)` および
-- `processWave` / `process` の定義・終端性証明は
-- `S2IL/Operations/Gravity/ProcessWave.lean` に移設（2026-04-21）。
-- Gravity/GroundedMono.lean の grounding 単調性補題に依存するため
-- Defs.lean より下流のファイル (ProcessWave.lean) に置く必要がある。
--
-- nonGroundedLayerSum_zero_fus_empty は Equivariance.lean で構成的に証明される
-- （floatingUnits_nonempty_implies_exists_ungrounded に依存するため）


end Gravity
