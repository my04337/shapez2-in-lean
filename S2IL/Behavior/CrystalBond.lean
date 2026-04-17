-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.QuarterPos
import S2IL.Behavior.Rotate
import S2IL.Behavior.Rotate180Lemmas
import S2IL.Behavior.GenericBfs
import Batteries
import Mathlib.Data.Finset.Image

/-!
# CrystalBond (結晶結合)

結晶の結合 (Bond) と結合クラスタ (Bonded Cluster) の算出。

## 結合条件

結晶同士は以下の条件で結合する:

### 同レイヤ内
- 隣接する方角 (NE↔SE, SE↔SW, SW↔NW, NW↔NE) にある
- 両方が結晶 (`Quarter.crystal`) である
- **色は問わない**

### 上下レイヤ間
- 同じ方角に位置する
- 両方が結晶である
- **色は問わない**

## 結合クラスタ

結合は推移的であり、結合関係で到達可能な結晶の集合が1つのクラスタを形成する。
クラスタの算出は `genericBfs` を用いたグラフ上での到達可能性探索（BFS）で行う。
頂点数はレイヤ数 × 4 方角。
-/

namespace CrystalBond

-- ============================================================
-- 結合条件の判定
-- ============================================================

/-- 同レイヤ内で2つの象限位置が結合しているかを判定する。
    同レイヤ内では隣接する結晶同士が色を問わず結合する -/
def isBondedInLayer (s : Shape) (p1 p2 : QuarterPos) : Bool :=
    p1.layer == p2.layer &&
    p1.dir.adjacent p2.dir &&
    match p1.getQuarter s, p2.getQuarter s with
    | some (.crystal _), some (.crystal _) => true
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
-- 定理
-- ============================================================

-- beq_symm / dir_beq_symm は Batteries の BEq.comm に統一

/-- クリスタル判定 match 式の引数対称性：q1, q2 どちらが先でも同じ真偽値を返す -/
private theorem crystal_agree_symm (q1 q2 : Option Quarter) :
        (match q1, q2 with | some (.crystal _), some (.crystal _) => true | _, _ => false) =
        (match q2, q1 with | some (.crystal _), some (.crystal _) => true | _, _ => false) :=
    by rcases q1 with _ | (_ | _) <;> rcases q2 with _ | (_ | _) <;> rfl

/-- 同レイヤ内結合は対称的である -/
theorem isBondedInLayer_symm (s : Shape) (p1 p2 : QuarterPos) :
        isBondedInLayer s p1 p2 = isBondedInLayer s p2 p1 := by
    simp only [isBondedInLayer]
    rw [BEq.comm (a := p1.layer), Direction.adjacent_symm p1.dir p2.dir]
    congr 1
    exact crystal_agree_symm (p1.getQuarter s) (p2.getQuarter s)

/-- 上下レイヤ間結合は対称的である -/
theorem isBondedCrossLayer_symm (s : Shape) (p1 p2 : QuarterPos) :
        isBondedCrossLayer s p1 p2 = isBondedCrossLayer s p2 p1 := by
    simp only [isBondedCrossLayer]
    rw [LayerIndex.verticallyAdjacent_symm p1.layer p2.layer,
        BEq.comm (a := p1.dir)]
    congr 1
    exact crystal_agree_symm (p1.getQuarter s) (p2.getQuarter s)

/-- isBonded は対称的である -/
theorem isBonded_symm (s : Shape) (p1 p2 : QuarterPos) :
        isBonded s p1 p2 = isBonded s p2 p1 := by
    unfold isBonded
    rw [isBondedInLayer_symm s p1 p2, isBondedCrossLayer_symm s p1 p2]

-- ============================================================
-- 結合クラスタの算出 (genericBfs 使用)
-- ============================================================

/-- 指定位置から到達可能な結合クラスタを返す（リスト版、計算用） -/
def clusterList (s : Shape) (pos : QuarterPos) : List QuarterPos :=
    let allPos := QuarterPos.allValid s
    -- fuel は最大頂点数の2乗で十分
    let n := s.layerCount * 4
    genericBfs (isBonded s) allPos [] [pos] (n * n)

/-- 指定位置から到達可能な結合クラスタを返す（Finset 版、証明用） -/
def cluster (s : Shape) (pos : QuarterPos) : Finset QuarterPos :=
    (clusterList s pos).toFinset

/-- シェイプ内の全結合クラスタを返す。各クラスタは `QuarterPos` の有限集合 -/
def allClusters (s : Shape) : List (Finset QuarterPos) :=
    let allPos := QuarterPos.allValid s
    let crystalPositions := allPos.filter fun p =>
        match p.getQuarter s with
        | some (.crystal _) => true
        | _ => false
    -- 各結晶位置についてクラスタを算出し、重複を除去する
    crystalPositions.foldl (fun clusters pos =>
        -- この位置が既存のクラスタに含まれているか確認
        if clusters.any (fun c => pos ∈ c) then
            clusters
        else
            let cluster := cluster s pos
            clusters ++ [cluster]
    ) []

-- ============================================================
-- 180° 回転等変性
-- ============================================================

/- rotate180 に関する基盤補題は Rotate180Lemmas.lean で定義済み:
   QuarterPos.getDir_rotate180, Shape.layers_rotate180,
   QuarterPos.getQuarter_rotate180 等。 -/

/-- isBondedInLayer は rotate180 で不変 -/
@[aesop norm simp] theorem isBondedInLayer_rotate180 (s : Shape) (p1 p2 : QuarterPos) :
        isBondedInLayer (s.rotate180) (p1.rotate180) (p2.rotate180) =
        isBondedInLayer s p1 p2 := by
    simp only [isBondedInLayer, QuarterPos.getQuarter_rotate180]
    simp only [QuarterPos.rotate180, Direction.adjacent_rotate180]

/-- isBondedCrossLayer は rotate180 で不変 -/
@[aesop norm simp] theorem isBondedCrossLayer_rotate180 (s : Shape) (p1 p2 : QuarterPos) :
        isBondedCrossLayer (s.rotate180) (p1.rotate180) (p2.rotate180) =
        isBondedCrossLayer s p1 p2 := by
    simp only [isBondedCrossLayer, QuarterPos.getQuarter_rotate180]
    simp only [QuarterPos.rotate180]
    congr 1
    cases p1.dir <;> cases p2.dir <;> rfl

/-- isBonded は rotate180 で不変 -/
@[aesop norm simp] theorem isBonded_rotate180 (s : Shape) (p1 p2 : QuarterPos) :
        isBonded (s.rotate180) (p1.rotate180) (p2.rotate180) =
        isBonded s p1 p2 := by
    simp only [isBonded, isBondedInLayer_rotate180, isBondedCrossLayer_rotate180]

-- ============================================================
-- genericBfs の rotate180 等変性
-- ============================================================

-- BFS ヘルパー用エイリアス（LayerPerm.rotate180 の具象化）
private abbrev σ_r180 := LayerPerm.rotate180

/-- isBonded フィルタの rotate180 マッピング等変性 -/
private theorem filter_isBonded_map_rotate180 (s : Shape)
        (pos : QuarterPos) (visited : List QuarterPos)
        (allPos : List QuarterPos) :
        (allPos.map QuarterPos.rotate180).filter (fun p =>
            isBonded s.rotate180 pos.rotate180 p &&
            !((pos.rotate180 :: visited.map QuarterPos.rotate180).any (· == p))) =
        (allPos.filter (fun p =>
            isBonded s pos p &&
            !((pos :: visited).any (· == p)))).map QuarterPos.rotate180 := by
    induction allPos with
    | nil => rfl
    | cons a as ih =>
        simp only [List.map, List.filter]
        rw [isBonded_rotate180, σ_r180.list_any_cons]
        cases isBonded s pos a && !((pos :: visited).any (· == a)) with
        | true => simp only [List.map]; exact congrArg _ ih
        | false => exact ih

/-- genericBfs (isBonded s) は rotate180 で等変である -/
private theorem genericBfs_isBonded_rotate180 (s : Shape)
        (allPos visited queue : List QuarterPos) (fuel : Nat) :
        genericBfs (isBonded s.rotate180)
            (allPos.map QuarterPos.rotate180)
            (visited.map QuarterPos.rotate180)
            (queue.map QuarterPos.rotate180) fuel =
        (genericBfs (isBonded s) allPos visited queue fuel).map QuarterPos.rotate180 := by
    induction fuel generalizing visited queue with
    | zero => rfl
    | succ n ih =>
        cases queue with
        | nil => simp only [genericBfs, List.map_nil]
        | cons pos rest =>
            show genericBfs (isBonded s.rotate180) (allPos.map QuarterPos.rotate180)
                (visited.map QuarterPos.rotate180)
                (pos.rotate180 :: rest.map QuarterPos.rotate180) (n + 1) =
                (genericBfs (isBonded s) allPos visited (pos :: rest) (n + 1)).map QuarterPos.rotate180
            simp only [genericBfs]
            rw [σ_r180.list_any_map]
            split
            · exact ih visited rest
            · rw [filter_isBonded_map_rotate180, ← List.map_append]
              exact ih (pos :: visited) (rest ++ allPos.filter fun p =>
                  isBonded s pos p && !((pos :: visited).any (· == p)))

-- ============================================================
-- allValid の rotate180 等価性
-- ============================================================

/-- allValid は rotate180 で不変（layerCount のみに依存するため） -/
theorem allValid_rotate180 (s : Shape) :
        QuarterPos.allValid s.rotate180 = QuarterPos.allValid s := by
    unfold QuarterPos.allValid
    simp only [Shape.layerCount_rotate180]

/-- clusterList の rotate180 等変性 -/
private theorem clusterList_rotate180_mapped (s : Shape) (pos : QuarterPos) :
        genericBfs (isBonded s.rotate180)
            ((QuarterPos.allValid s).map QuarterPos.rotate180) []
            [pos.rotate180]
            (s.layerCount * 4 * (s.layerCount * 4)) =
        (clusterList s pos).map QuarterPos.rotate180 := by
    unfold clusterList
    exact genericBfs_isBonded_rotate180 s (QuarterPos.allValid s) [] [pos]
        (s.layerCount * 4 * (s.layerCount * 4))

-- ============================================================
-- GenericReachable の rotate180 保存
-- ============================================================

/-- GenericReachable (isBonded s) は rotate180 で保存される -/
private theorem genReachable_isBonded_rotate180 (s : Shape) (p q : QuarterPos)
        (h : GenericReachable (isBonded s) p q) :
        GenericReachable (isBonded s.rotate180) p.rotate180 q.rotate180 := by
    induction h with
    | refl => exact .refl
    | step h_edge _ ih =>
        exact .step (isBonded_rotate180 s _ _ ▸ h_edge) ih

-- ============================================================
-- allValid のメンバーシップ特性
-- ============================================================

/-- allValid s のメンバーシップは layer < layerCount と同値 -/
private theorem allValid_any_iff_layer (s : Shape) (p : QuarterPos) :
        (QuarterPos.allValid s).any (· == p) = true ↔ p.layer < s.layerCount := by
    constructor
    · -- any = true → layer < layerCount
      intro h
      rw [List.any_eq_true] at h
      obtain ⟨x, h_mem, h_eq⟩ := h
      have := eq_of_beq h_eq; subst this
      simp only [QuarterPos.allValid] at h_mem
      rw [List.mem_flatMap] at h_mem
      obtain ⟨li, h_li, h_dir⟩ := h_mem
      rw [List.mem_map] at h_dir
      obtain ⟨d, _, h_mk⟩ := h_dir
      simp only [Shape.layerCount]
      rw [← h_mk]; simp only []
      exact List.mem_range.mp h_li
    · -- layer < layerCount → any = true
      intro h
      rw [List.any_eq_true]
      exact ⟨p, by
          simp only [QuarterPos.allValid]
          rw [List.mem_flatMap]
          exact ⟨p.layer, List.mem_range.mpr h,
              List.mem_map.mpr ⟨p.dir, List.mem_of_elem_eq_true (by cases p.dir <;> rfl),
                  by cases p; rfl⟩⟩,
          BEq.rfl⟩

/-- allValid の any メンバーシップは rotate180 で不変 -/
theorem allValid_any_rotate180 (s : Shape) (p : QuarterPos) :
        (QuarterPos.allValid s).any (· == p.rotate180) =
        (QuarterPos.allValid s).any (· == p) := by
    cases h : (QuarterPos.allValid s).any (· == p) with
    | true =>
        have h_lt := (allValid_any_iff_layer s p).mp h
        exact (allValid_any_iff_layer s p.rotate180).mpr
            (by simp only [QuarterPos.rotate180]; exact h_lt)
    | false =>
        cases h' : (QuarterPos.allValid s).any (· == p.rotate180) with
        | false => rfl
        | true =>
            have h_lt := (allValid_any_iff_layer s p.rotate180).mp h'
            simp only [QuarterPos.rotate180] at h_lt
            exact absurd ((allValid_any_iff_layer s p).mpr h_lt) (by simp only [h, Bool.false_eq_true, not_false_eq_true])

/-- (allValid s).map r180 のメンバーシップは allValid s と同じ -/
private theorem allValid_map_rotate180_any (s : Shape) (p : QuarterPos) :
        ((QuarterPos.allValid s).map QuarterPos.rotate180).any (· == p) =
        (QuarterPos.allValid s).any (· == p) := by
    -- 両辺を ↔ p.layer < layerCount に帰着
    cases h : (QuarterPos.allValid s).any (· == p) with
    | true =>
        have h_lt : p.layer < s.layerCount := (allValid_any_iff_layer s p).mp h
        rw [List.any_eq_true]
        -- p.r180 ∈ allValid s を示し、p.r180.r180 = p を使う
        have h_r180_mem := (allValid_any_iff_layer s p.rotate180).mpr
            (by simp only [QuarterPos.rotate180]; exact h_lt)
        rw [List.any_eq_true] at h_r180_mem
        obtain ⟨x, h_x_mem, h_x_eq⟩ := h_r180_mem
        exact ⟨x.rotate180, List.mem_map.mpr ⟨x, h_x_mem, rfl⟩, by
            have := eq_of_beq h_x_eq; subst this
            simp only [QuarterPos.rotate180_rotate180, BEq.rfl]⟩
    | false =>
        have h_ge : ¬(p.layer < s.layerCount) := by
            intro h_lt; exact absurd ((allValid_any_iff_layer s p).mpr h_lt) (by simp only [h, Bool.false_eq_true, not_false_eq_true])
        -- p ∉ allValid s → p ∉ (allValid s).map r180
        cases h' : ((QuarterPos.allValid s).map QuarterPos.rotate180).any (· == p) with
        | false => rfl
        | true =>
            rw [List.any_eq_true] at h'
            obtain ⟨x, h_x_mem, h_x_eq⟩ := h'
            rw [List.mem_map] at h_x_mem
            obtain ⟨a, h_a_mem, h_a_eq⟩ := h_x_mem
            subst h_a_eq
            have := eq_of_beq h_x_eq; subst this
            have h_a_valid := (allValid_any_iff_layer s a).mp
                (List.any_eq_true.mpr ⟨a, h_a_mem, BEq.rfl⟩)
            simp only at h_a_valid
            exact absurd h_a_valid h_ge

-- ============================================================
-- isBonded → layer 有効性
-- ============================================================

/-- isBonded s p q = true ならば q.layer < s.layerCount -/
private theorem isBonded_valid (s : Shape) (p q : QuarterPos)
        (h : isBonded s p q = true) :
        q.layer < s.layerCount := by
    simp only [isBonded, Bool.or_eq_true_iff] at h
    cases h with
    | inl h_l =>
        simp only [isBondedInLayer, Bool.and_eq_true] at h_l
        obtain ⟨⟨_, _⟩, h_m⟩ := h_l
        simp only [Shape.layerCount]
        unfold QuarterPos.getQuarter at h_m
        cases hl : s.layers[q.layer]? with
        | none => simp only [hl, reduceCtorEq, imp_self, implies_true, Bool.false_eq_true] at h_m
        | some _ =>
            exact (List.getElem?_eq_some_iff.mp hl).1
    | inr h_c =>
        simp only [isBondedCrossLayer, Bool.and_eq_true] at h_c
        obtain ⟨⟨_, _⟩, h_m⟩ := h_c
        simp only [Shape.layerCount]
        unfold QuarterPos.getQuarter at h_m
        cases hl : s.layers[q.layer]? with
        | none => simp only [hl, reduceCtorEq, imp_self, implies_true, Bool.false_eq_true] at h_m
        | some _ =>
            exact (List.getElem?_eq_some_iff.mp hl).1

/-- isBonded s p q = true ならば p.layer < s.layerCount -/
private theorem isBonded_valid_fst (s : Shape) (p q : QuarterPos)
        (h : isBonded s p q = true) :
        p.layer < s.layerCount := by
    simp only [isBonded, Bool.or_eq_true_iff] at h
    cases h with
    | inl h_l =>
        simp only [isBondedInLayer, Bool.and_eq_true] at h_l
        obtain ⟨⟨_, _⟩, h_m⟩ := h_l
        simp only [Shape.layerCount]
        unfold QuarterPos.getQuarter at h_m
        cases hl : s.layers[p.layer]? with
        | none => simp only [hl, Bool.false_eq_true] at h_m
        | some _ =>
            exact (List.getElem?_eq_some_iff.mp hl).1
    | inr h_c =>
        simp only [isBondedCrossLayer, Bool.and_eq_true] at h_c
        obtain ⟨⟨_, _⟩, h_m⟩ := h_c
        simp only [Shape.layerCount]
        unfold QuarterPos.getQuarter at h_m
        cases hl : s.layers[p.layer]? with
        | none => simp only [hl, Bool.false_eq_true] at h_m
        | some _ =>
            exact (List.getElem?_eq_some_iff.mp hl).1

/-- allValid s は isBonded の第1引数を含む -/
private theorem allValid_contains_isBonded_fst (s : Shape) (p q : QuarterPos)
        (h : isBonded s p q = true) :
        (QuarterPos.allValid s).any (· == p) = true :=
    (allValid_any_iff_layer s p).mpr (isBonded_valid_fst s p q h)

-- ============================================================
-- allValid の長さ
-- ============================================================

/-- allValid の長さは layerCount * 4 -/
private theorem allValid_length (s : Shape) :
        (QuarterPos.allValid s).length = s.layerCount * 4 := by
    simp only [QuarterPos.allValid, Shape.layerCount]
    generalize s.layers.length = n
    induction n with
    | zero => simp only [List.range_zero, List.flatMap_nil, List.length_nil, Nat.zero_mul]
    | succ k ih =>
        rw [List.range_succ, List.flatMap_append, List.length_append, ih]
        simp only [Direction.all, List.map_cons, List.map, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
        omega

/-- allValid s は isBonded の結果を全て含む -/
private theorem allValid_contains_isBonded (s : Shape) (p q : QuarterPos)
        (h : isBonded s p q = true) :
        (QuarterPos.allValid s).any (· == q) = true :=
    (allValid_any_iff_layer s q).mpr (isBonded_valid s p q h)

-- ============================================================
-- cluster の健全性
-- ============================================================

/-- .any (· == p) と List.mem の等価性（LawfulBEq 前提） -/
private theorem any_beq_iff_mem (l : List QuarterPos) (p : QuarterPos) :
        l.any (· == p) = true ↔ p ∈ l := by
    simp only [List.any_eq_true, beq_iff_eq]
    exact ⟨fun ⟨x, hx, he⟩ => he ▸ hx, fun h => ⟨p, h, rfl⟩⟩

/-- cluster の健全性:
    結果に含まれる要素は start から GenericReachable -/
theorem cluster_sound (s : Shape) (start p : QuarterPos) :
        p ∈ cluster s start →
        GenericReachable (isBonded s) start p := by
    unfold cluster; rw [List.mem_toFinset, ← any_beq_iff_mem]
    intro h
    unfold clusterList at h
    match genericBfs_sound (isBonded s) _ [] [start] _ p h with
    | .inl h_vis => simp only [List.any, Bool.false_eq_true] at h_vis
    | .inr ⟨q, h_q, h_reach⟩ =>
        rw [List.any_cons, Bool.or_eq_true_iff] at h_q
        cases h_q with
        | inl h_eq =>
            have := eq_of_beq h_eq; subst this; exact h_reach
        | inr h_rest =>
            simp only [List.any, Bool.false_eq_true] at h_rest

-- ============================================================
-- cluster の完全性
-- ============================================================

/-- cluster の完全性:
    start から GenericReachable な要素が結果に含まれる
    （s.layerCount > 0 が必要: layerCount = 0 では BFS のキューが空） -/
theorem cluster_complete (s : Shape) (start p : QuarterPos)
        (h_lc : s.layerCount > 0)
        (h_reach : GenericReachable (isBonded s) start p) :
        p ∈ cluster s start := by
    unfold cluster; rw [List.mem_toFinset, ← any_beq_iff_mem]
    unfold clusterList
    -- BFS 不変条件保存
    have h_inv := genericBfs_invariant_preserved (isBonded s) (QuarterPos.allValid s) []
        [start] (s.layerCount * 4 * (s.layerCount * 4))
        (GenericBfsInv_initial (isBonded s) (QuarterPos.allValid s) start)
        (by
            have h_filter : (QuarterPos.allValid s).filter (fun p =>
                !(([] : List QuarterPos).any (· == p))) = QuarterPos.allValid s :=
                List.filter_eq_self.mpr (by intro x _; simp only [List.any, Bool.not_false])
            simp only [h_filter, List.length, allValid_length]; omega)
        (fun p q h => allValid_contains_isBonded_fst s p q h)
    -- start が BFS 結果に含まれることを確認
    have h_start : (genericBfs (isBonded s) (QuarterPos.allValid s) [] [start]
        (s.layerCount * 4 * (s.layerCount * 4))).any (· == start) = true :=
        genericBfs_contains_start (isBonded s) (QuarterPos.allValid s) start
            (s.layerCount * 4 * (s.layerCount * 4))
            (Nat.mul_pos (by omega) (by omega))
    -- 閉包で p の所属を導出
    exact genericBfs_closed_contains_reachable (isBonded s) (QuarterPos.allValid s) _ h_inv
        start p h_start h_reach
        (fun q r h_bond => allValid_contains_isBonded s q r h_bond)

-- ============================================================
-- cluster の rotate180 等変性
-- ============================================================

/-- cluster の rotate180 等変性（Finset.image 形式）。
    rotate180 してからクラスタ算出 = クラスタ算出してから Finset.image。
    BFS の健全性・完全性・到達可能性の等変性から直接導出。 -/
theorem cluster_rotate180 (s : Shape) (start : QuarterPos) :
        cluster s.rotate180 start.rotate180 =
        (cluster s start).image QuarterPos.rotate180 := by
    ext p
    simp only [Finset.mem_image]
    constructor
    · intro hp
      -- 健全性: p は start.r180 から s.r180 で GenericReachable
      have h_reach := cluster_sound s.rotate180 start.rotate180 p hp
      -- 等変性の逆方向: s での start → p.r180 の到達可能性
      have h_back : GenericReachable (isBonded s) start p.rotate180 := by
          have := genReachable_isBonded_rotate180 s.rotate180 start.rotate180 p h_reach
          simp only [Shape.rotate180_rotate180, QuarterPos.rotate180_rotate180] at this
          exact this
      refine ⟨p.rotate180, ?_, by simp only [QuarterPos.rotate180_rotate180]⟩
      -- 完全性: layerCount = 0 では BFS 結果は空 → hp に矛盾
      cases h_lc : s.layerCount with
      | zero =>
          exfalso
          unfold cluster at hp; rw [List.mem_toFinset, ← any_beq_iff_mem] at hp
          unfold clusterList at hp
          simp only [allValid_rotate180, Shape.layerCount_rotate180, h_lc, Nat.zero_mul, Nat.mul_zero, genericBfs, List.any_nil, Bool.false_eq_true] at hp
      | succ n =>
          exact cluster_complete s start p.rotate180 (by omega) h_back
    · rintro ⟨q, hq, rfl⟩
      -- 健全性 + 等変性: q.r180 は start.r180 から s.r180 で GenericReachable
      have h_reach := cluster_sound s start q hq
      have h_r180 := genReachable_isBonded_rotate180 s start q h_reach
      -- 完全性
      cases h_lc : s.layerCount with
      | zero =>
          exfalso
          unfold cluster at hq; rw [List.mem_toFinset, ← any_beq_iff_mem] at hq
          unfold clusterList at hq; simp only [h_lc, Nat.zero_mul, Nat.mul_zero, genericBfs, List.any_nil, Bool.false_eq_true] at hq
      | succ n =>
          exact cluster_complete s.rotate180 start.rotate180 q.rotate180
              (by rw [Shape.layerCount_rotate180]; omega) h_r180

/-- cluster メンバーシップの rotate180 等変性。
    cluster_rotate180 (Finset.image) から導出。 -/
theorem cluster_mem_rotate180 (s : Shape) (start p : QuarterPos) :
        p ∈ cluster s start ↔
        p.rotate180 ∈ cluster s.rotate180 start.rotate180 := by
    rw [cluster_rotate180, Finset.mem_image]
    constructor
    · exact fun h => ⟨p, h, rfl⟩
    · rintro ⟨q, hq, hqe⟩
      have := congr_arg QuarterPos.rotate180 hqe
      simp only [QuarterPos.rotate180_rotate180] at this
      exact this ▸ hq

-- ============================================================
-- rotateCW 等変性
-- ============================================================

-- BFS ヘルパー用エイリアス
private abbrev σ_rCW := LayerPerm.rotateCW

/-- isBondedInLayer は rotateCW で不変 -/
@[aesop norm simp] theorem isBondedInLayer_rotateCW (s : Shape) (p1 p2 : QuarterPos) :
        isBondedInLayer (s.rotateCW) (p1.rotateCW) (p2.rotateCW) =
        isBondedInLayer s p1 p2 := by
    simp only [isBondedInLayer, QuarterPos.getQuarter_rotateCW]
    simp only [QuarterPos.rotateCW, Direction.adjacent_rotateCW]

/-- isBondedCrossLayer は rotateCW で不変 -/
@[aesop norm simp] theorem isBondedCrossLayer_rotateCW (s : Shape) (p1 p2 : QuarterPos) :
        isBondedCrossLayer (s.rotateCW) (p1.rotateCW) (p2.rotateCW) =
        isBondedCrossLayer s p1 p2 := by
    simp only [isBondedCrossLayer, QuarterPos.getQuarter_rotateCW]
    simp only [QuarterPos.rotateCW, σ_rCW.dir_beq]

/-- isBonded は rotateCW で不変 -/
@[aesop norm simp] theorem isBonded_rotateCW (s : Shape) (p1 p2 : QuarterPos) :
        isBonded (s.rotateCW) (p1.rotateCW) (p2.rotateCW) =
        isBonded s p1 p2 := by
    simp only [isBonded, isBondedInLayer_rotateCW, isBondedCrossLayer_rotateCW]

/-- allValid は rotateCW で不変（layerCount のみに依存するため） -/
theorem allValid_rotateCW (s : Shape) :
        QuarterPos.allValid s.rotateCW = QuarterPos.allValid s := by
    unfold QuarterPos.allValid
    simp only [Shape.layerCount_rotateCW]

/-- GenericReachable (isBonded s) は rotateCW で保存される -/
private theorem genReachable_isBonded_rotateCW (s : Shape) (p q : QuarterPos)
        (h : GenericReachable (isBonded s) p q) :
        GenericReachable (isBonded s.rotateCW) p.rotateCW q.rotateCW := by
    induction h with
    | refl => exact .refl
    | step h_edge _ ih =>
        exact .step (isBonded_rotateCW s _ _ ▸ h_edge) ih

/-- GenericReachable (isBonded s.rotateCW) の逆マッピング -/
private theorem genReachable_isBonded_rotateCW_inv (s : Shape) (p q : QuarterPos)
        (h : GenericReachable (isBonded s.rotateCW) p q) :
        GenericReachable (isBonded s) p.rotateCCW q.rotateCCW := by
    induction h with
    | refl => exact .refl
    | step h_edge _ ih =>
        exact .step (by rwa [← isBonded_rotateCW, QuarterPos.rotateCCW_rotateCW,
            QuarterPos.rotateCCW_rotateCW]) ih

/-- cluster の rotateCW 等変性（Finset.image 形式）。
    rotateCW してからクラスタ算出 = クラスタ算出してから Finset.image -/
theorem cluster_rotateCW (s : Shape) (start : QuarterPos) :
        cluster s.rotateCW start.rotateCW =
        (cluster s start).image QuarterPos.rotateCW := by
    ext p
    simp only [Finset.mem_image]
    constructor
    · intro hp
      have h_reach := cluster_sound s.rotateCW start.rotateCW p hp
      have h_back := genReachable_isBonded_rotateCW_inv s start.rotateCW p h_reach
      simp only [QuarterPos.rotateCW_rotateCCW] at h_back
      refine ⟨p.rotateCCW, ?_, by simp only [QuarterPos.rotateCCW_rotateCW]⟩
      cases h_lc : s.layerCount with
      | zero =>
          exfalso
          unfold cluster at hp; rw [List.mem_toFinset, ← any_beq_iff_mem] at hp
          unfold clusterList at hp
          simp only [allValid_rotateCW, Shape.layerCount_rotateCW, h_lc,
              Nat.zero_mul, Nat.mul_zero, genericBfs, List.any_nil, Bool.false_eq_true] at hp
      | succ n =>
          exact cluster_complete s start p.rotateCCW (by omega) h_back
    · rintro ⟨q, hq, rfl⟩
      have h_reach := cluster_sound s start q hq
      have h_rCW := genReachable_isBonded_rotateCW s start q h_reach
      cases h_lc : s.layerCount with
      | zero =>
          exfalso
          unfold cluster at hq; rw [List.mem_toFinset, ← any_beq_iff_mem] at hq
          unfold clusterList at hq; simp only [h_lc, Nat.zero_mul, Nat.mul_zero, genericBfs, List.any_nil, Bool.false_eq_true] at hq
      | succ n =>
          exact cluster_complete s.rotateCW start.rotateCW q.rotateCW
              (by rw [Shape.layerCount_rotateCW]; omega) h_rCW

/-- allValid の any メンバーシップは rotateCW で不変 -/
theorem allValid_any_rotateCW (s : Shape) (p : QuarterPos) :
        (QuarterPos.allValid s).any (· == p.rotateCW) =
        (QuarterPos.allValid s).any (· == p) := by
    cases h : (QuarterPos.allValid s).any (· == p) with
    | true =>
        have h_lt := (allValid_any_iff_layer s p).mp h
        exact (allValid_any_iff_layer s p.rotateCW).mpr
            (by simp only [QuarterPos.rotateCW]; exact h_lt)
    | false =>
        cases h' : (QuarterPos.allValid s).any (· == p.rotateCW) with
        | false => rfl
        | true =>
            have h_lt := (allValid_any_iff_layer s p.rotateCW).mp h'
            simp only [QuarterPos.rotateCW] at h_lt
            exact absurd ((allValid_any_iff_layer s p).mpr h_lt)
                (by simp only [h, Bool.false_eq_true, not_false_eq_true])

/-- allValid の any メンバーシップは rotateCCW で不変 -/
theorem allValid_any_rotateCCW (s : Shape) (p : QuarterPos) :
        (QuarterPos.allValid s).any (· == p.rotateCCW) =
        (QuarterPos.allValid s).any (· == p) := by
    cases h : (QuarterPos.allValid s).any (· == p) with
    | true =>
        have h_lt := (allValid_any_iff_layer s p).mp h
        exact (allValid_any_iff_layer s p.rotateCCW).mpr
            (by simp only [QuarterPos.rotateCCW]; exact h_lt)
    | false =>
        cases h' : (QuarterPos.allValid s).any (· == p.rotateCCW) with
        | false => rfl
        | true =>
            have h_lt := (allValid_any_iff_layer s p.rotateCCW).mp h'
            simp only [QuarterPos.rotateCCW] at h_lt
            exact absurd ((allValid_any_iff_layer s p).mpr h_lt)
                (by simp only [h, Bool.false_eq_true, not_false_eq_true])

end CrystalBond
