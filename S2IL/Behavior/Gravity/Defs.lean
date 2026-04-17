-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Behavior.CrystalBond
import S2IL.Behavior.GenericBfs
import S2IL.Behavior.Rotate180Lemmas
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
-- 落下処理 (Gravity)
-- ============================================================

/-- 落下処理のメインロジック -/
def process (s : Shape) : Option Shape :=
    let units := floatingUnits s
    -- 落下単位が存在しない場合はそのまま返す
    if units.isEmpty then s.normalize
    else
        -- 落下単位を minLayer 昇順でソート（決定性 mergeSort）
        let sorted := sortFallingUnits' units
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


end Gravity
