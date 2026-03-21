-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.QuarterPos
import S2IL.Behavior.Rotate

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
-- 定理
-- ============================================================

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

/-- 同レイヤ内結合は対称的である -/
theorem isBondedInLayer_symm (s : Shape) (p1 p2 : QuarterPos) :
        isBondedInLayer s p1 p2 = isBondedInLayer s p2 p1 := by
    simp only [isBondedInLayer]
    rw [beq_symm p1.layer p2.layer, Direction.adjacent_symm p1.dir p2.dir]
    congr 1
    generalize p1.getQuarter s = q1
    generalize p2.getQuarter s = q2
    cases q1 with
    | none =>
        cases q2 with
        | none => rfl
        | some v => cases v <;> rfl
    | some v1 =>
        cases q2 with
        | none => cases v1 <;> rfl
        | some v2 =>
            cases v1 <;> cases v2 <;> try rfl
            -- crystal c1, crystal c2 の場合のみ残る: c1 == c2 = c2 == c1
            rename_i c1 c2; cases c1 <;> cases c2 <;> rfl

/-- 上下レイヤ間結合は対称的である -/
theorem isBondedCrossLayer_symm (s : Shape) (p1 p2 : QuarterPos) :
        isBondedCrossLayer s p1 p2 = isBondedCrossLayer s p2 p1 := by
    simp only [isBondedCrossLayer]
    rw [LayerIndex.verticallyAdjacent_symm p1.layer p2.layer,
        dir_beq_symm p1.dir p2.dir]
    congr 1
    generalize p1.getQuarter s = q1
    generalize p2.getQuarter s = q2
    cases q1 with
    | none =>
        cases q2 with
        | none => rfl
        | some v => cases v <;> rfl
    | some v1 =>
        cases q2 with
        | none => cases v1 <;> rfl
        | some v2 => cases v1 <;> cases v2 <;> rfl

/-- isBonded は対称的である -/
theorem isBonded_symm (s : Shape) (p1 p2 : QuarterPos) :
        isBonded s p1 p2 = isBonded s p2 p1 := by
    unfold isBonded
    rw [isBondedInLayer_symm s p1 p2, isBondedCrossLayer_symm s p1 p2]

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

-- ============================================================
-- 180° 回転等変性
-- ============================================================

/- rotate180 に関するヘルパー補題。
   CrystalBond 内部で BFS 等変性を証明するために必要。 -/

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

/-- isBondedInLayer は rotate180 で不変 -/
theorem isBondedInLayer_rotate180 (s : Shape) (p1 p2 : QuarterPos) :
        isBondedInLayer (s.rotate180) (p1.rotate180) (p2.rotate180) =
        isBondedInLayer s p1 p2 := by
    simp only [isBondedInLayer, getQuarter_rotate180]
    simp only [QuarterPos.rotate180, Direction.adjacent_rotate180]

/-- isBondedCrossLayer は rotate180 で不変 -/
theorem isBondedCrossLayer_rotate180 (s : Shape) (p1 p2 : QuarterPos) :
        isBondedCrossLayer (s.rotate180) (p1.rotate180) (p2.rotate180) =
        isBondedCrossLayer s p1 p2 := by
    simp only [isBondedCrossLayer, getQuarter_rotate180]
    simp only [QuarterPos.rotate180]
    congr 1
    cases p1.dir <;> cases p2.dir <;> rfl

/-- isBonded は rotate180 で不変 -/
theorem isBonded_rotate180 (s : Shape) (p1 p2 : QuarterPos) :
        isBonded (s.rotate180) (p1.rotate180) (p2.rotate180) =
        isBonded s p1 p2 := by
    simp only [isBonded, isBondedInLayer_rotate180, isBondedCrossLayer_rotate180]

-- ============================================================
-- BFS の rotate180 等変性
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

/-- List.filter と map rotate180 の関係 -/
private theorem list_filter_map_rotate180 (l : List QuarterPos) (pred : QuarterPos → Bool) :
        (l.map QuarterPos.rotate180).filter pred =
        (l.filter (pred ∘ QuarterPos.rotate180)).map QuarterPos.rotate180 := by
    induction l with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.map, List.filter, Function.comp, ih]
        cases pred (x.rotate180) <;> rfl

/-- List.any の cons と rotate180 の関係 -/
private theorem list_any_cons_rotate180 (x : QuarterPos) (l : List QuarterPos)
        (p : QuarterPos) :
        ((x.rotate180 :: l.map QuarterPos.rotate180).any (· == p.rotate180)) =
        ((x :: l).any (· == p)) := by
    simp only [List.any, quarterPos_beq_rotate180, list_any_map_rotate180]

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
        rw [isBonded_rotate180, list_any_cons_rotate180]
        cases isBonded s pos a && !((pos :: visited).any (· == a)) with
        | true => simp only [List.map]; exact congrArg _ ih
        | false => exact ih

/-- BFS は rotate180 で等変である（allPos を map した場合）。
    帰納法を fuel に対して適用する。 -/
private theorem bfs_rotate180 (s : Shape)
        (allPos visited queue : List QuarterPos) (fuel : Nat) :
        bfs s.rotate180
            (allPos.map QuarterPos.rotate180)
            (visited.map QuarterPos.rotate180)
            (queue.map QuarterPos.rotate180) fuel =
        (bfs s allPos visited queue fuel).map QuarterPos.rotate180 := by
    induction fuel generalizing visited queue with
    | zero => rfl
    | succ n ih =>
        cases queue with
        | nil => simp [bfs]
        | cons pos rest =>
            -- queue.map を明示的に cons 形式にしてから bfs を展開
            show bfs s.rotate180 (allPos.map QuarterPos.rotate180)
                (visited.map QuarterPos.rotate180)
                (pos.rotate180 :: rest.map QuarterPos.rotate180) (n + 1) =
                (bfs s allPos visited (pos :: rest) (n + 1)).map QuarterPos.rotate180
            simp only [bfs]
            rw [list_any_map_rotate180]
            split
            · -- visited.any (· == pos) = true のケース
                exact ih visited rest
            · -- visited.any (· == pos) = false のケース
                rw [filter_isBonded_map_rotate180, ← List.map_append]
                exact ih (pos :: visited) (rest ++ allPos.filter fun p =>
                    isBonded s pos p && !((pos :: visited).any (· == p)))

-- ============================================================
-- allValid の rotate180 等価性
-- ============================================================

/-- allValid は rotate180 で不変（layerCount のみに依存するため） -/
theorem allValid_rotate180_eq (s : Shape) :
        QuarterPos.allValid s.rotate180 = QuarterPos.allValid s := by
    unfold QuarterPos.allValid
    simp [Shape.layerCount_rotate180]

-- ============================================================
-- crystalCluster の rotate180 等変性（mapped allPos 版）
-- ============================================================

/-- crystalCluster を mapped allPos で呼んだ場合の等変性。
    bfs_rotate180 から直接導出される。 -/
theorem crystalCluster_rotate180_mapped (s : Shape) (pos : QuarterPos) :
        bfs s.rotate180
            ((QuarterPos.allValid s).map QuarterPos.rotate180) []
            [pos.rotate180]
            (s.layerCount * 4 * (s.layerCount * 4)) =
        (crystalCluster s pos).map QuarterPos.rotate180 := by
    unfold crystalCluster
    exact bfs_rotate180 s (QuarterPos.allValid s) [] [pos]
        (s.layerCount * 4 * (s.layerCount * 4))

-- ============================================================
-- BFS メンバーシップの rotate180 等価性
-- ============================================================

/-- BFS による結合の到達可能性（帰納的定義） -/
inductive BondReachable (s : Shape) : QuarterPos → QuarterPos → Prop where
    | refl : BondReachable s p p
    | step : isBonded s p q = true → BondReachable s q r → BondReachable s p r

/-- BondReachable は rotate180 で保存される -/
theorem bondReachable_rotate180 (s : Shape) (p q : QuarterPos) :
        BondReachable s p q → BondReachable s.rotate180 p.rotate180 q.rotate180 := by
    intro h
    induction h with
    | refl => exact .refl
    | step h_bond _ ih =>
        exact .step (isBonded_rotate180 s _ _ ▸ h_bond) ih

-- ============================================================
-- BFS 基本補題
-- ============================================================

/-- BFS 結果は初期訪問済み集合を含む -/
private theorem bfs_vis_subset (s : Shape) (allPos vis queue : List QuarterPos)
        (fuel : Nat) (p : QuarterPos) :
        vis.any (· == p) = true →
        (bfs s allPos vis queue fuel).any (· == p) = true := by
    intro h_vis
    induction fuel generalizing vis queue with
    | zero => exact h_vis
    | succ n ih =>
        cases queue with
        | nil => exact h_vis
        | cons pos rest =>
            simp only [bfs]
            split
            · exact ih vis rest h_vis
            · exact ih (pos :: vis) (rest ++ _)
                    (by rw [List.any_cons]; simp [h_vis])

/-- BFS は fuel > 0 なら start を結果に含む -/
private theorem bfs_contains_start (s : Shape) (allPos : List QuarterPos)
        (start : QuarterPos) (fuel : Nat) (h_fuel : fuel > 0) :
        (bfs s allPos [] [start] fuel).any (· == start) = true := by
    cases fuel with
    | zero => omega
    | succ n =>
        simp only [bfs, List.any, Bool.false_or]
        -- start ∉ [] なので処理される
        exact bfs_vis_subset s allPos [start] _ n start
            (by rw [List.any_cons]; simp [BEq.rfl])

/-- BFS 結果の各要素は、初期 vis に含まれるか、
    初期 queue のある要素から BondReachable である -/
private theorem bfs_sound (s : Shape) (allPos vis queue : List QuarterPos)
        (fuel : Nat) (p : QuarterPos) :
        (bfs s allPos vis queue fuel).any (· == p) = true →
        vis.any (· == p) = true ∨
        ∃ q, queue.any (· == q) = true ∧ BondReachable s q p := by
    induction fuel generalizing vis queue with
    | zero => intro h; exact .inl h
    | succ n ih =>
        cases queue with
        | nil => intro h; exact .inl h
        | cons pos rest =>
            simp only [bfs]
            split
            · -- pos ∈ vis: スキップ
              intro h
              match ih vis rest h with
              | .inl h_vis => exact .inl h_vis
              | .inr ⟨q, h_q, h_reach⟩ =>
                  exact .inr ⟨q, by rw [List.any_cons]; simp [h_q], h_reach⟩
            · -- pos ∉ vis: 処理
              intro h
              match ih (pos :: vis) (rest ++ _) h with
              | .inl h' =>
                  rw [List.any_cons] at h'
                  cases h_eq : (pos == p) with
                  | true =>
                      have h_pos_eq_p := eq_of_beq h_eq
                      exact .inr ⟨pos, by rw [List.any_cons]; simp [BEq.rfl],
                                  h_pos_eq_p ▸ BondReachable.refl⟩
                  | false =>
                      rw [h_eq, Bool.false_or] at h'
                      exact .inl h'
              | .inr ⟨q, h_q_mem, h_reach⟩ =>
                  rw [List.any_append] at h_q_mem
                  cases Bool.or_eq_true_iff.mp h_q_mem with
                  | inl h_rest =>
                      exact .inr ⟨q, by rw [List.any_cons]; simp [h_rest], h_reach⟩
                  | inr h_neigh =>
                      rw [List.any_filter, List.any_eq_true] at h_neigh
                      obtain ⟨a, _, h_pred⟩ := h_neigh
                      simp only [Bool.and_eq_true] at h_pred
                      obtain ⟨⟨h_bonded, _⟩, h_aeq⟩ := h_pred
                      have := eq_of_beq h_aeq; subst this
                      exact .inr ⟨pos, by rw [List.any_cons]; simp [BEq.rfl],
                                  .step h_bonded h_reach⟩

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
      rw [← h_mk]; simp only [QuarterPos.layer]
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
            (by simp [QuarterPos.rotate180]; exact h_lt)
    | false =>
        cases h' : (QuarterPos.allValid s).any (· == p.rotate180) with
        | false => rfl
        | true =>
            have h_lt := (allValid_any_iff_layer s p.rotate180).mp h'
            simp [QuarterPos.rotate180] at h_lt
            exact absurd ((allValid_any_iff_layer s p).mpr h_lt) (by simp [h])

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
            (by simp [QuarterPos.rotate180]; exact h_lt)
        rw [List.any_eq_true] at h_r180_mem
        obtain ⟨x, h_x_mem, h_x_eq⟩ := h_r180_mem
        exact ⟨x.rotate180, List.mem_map.mpr ⟨x, h_x_mem, rfl⟩, by
            have := eq_of_beq h_x_eq; subst this
            simp [quarterPos_beq_rotate180, QuarterPos.rotate180_rotate180, BEq.rfl]⟩
    | false =>
        have h_ge : ¬(p.layer < s.layerCount) := by
            intro h_lt; exact absurd ((allValid_any_iff_layer s p).mpr h_lt) (by simp [h])
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
            simp [QuarterPos.rotate180] at h_a_valid
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
        | none => simp [hl] at h_m
        | some _ =>
            exact (List.getElem?_eq_some_iff.mp hl).1
    | inr h_c =>
        simp only [isBondedCrossLayer, Bool.and_eq_true] at h_c
        obtain ⟨⟨_, _⟩, h_m⟩ := h_c
        simp only [Shape.layerCount]
        unfold QuarterPos.getQuarter at h_m
        cases hl : s.layers[q.layer]? with
        | none => simp [hl] at h_m
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
        | none => simp [hl] at h_m
        | some _ =>
            exact (List.getElem?_eq_some_iff.mp hl).1
    | inr h_c =>
        simp only [isBondedCrossLayer, Bool.and_eq_true] at h_c
        obtain ⟨⟨_, _⟩, h_m⟩ := h_c
        simp only [Shape.layerCount]
        unfold QuarterPos.getQuarter at h_m
        cases hl : s.layers[p.layer]? with
        | none => simp [hl] at h_m
        | some _ =>
            exact (List.getElem?_eq_some_iff.mp hl).1

/-- allValid s は isBonded の第1引数を含む -/
private theorem allValid_contains_isBonded_fst (s : Shape) (p q : QuarterPos)
        (h : isBonded s p q = true) :
        (QuarterPos.allValid s).any (· == p) = true :=
    (allValid_any_iff_layer s p).mpr (isBonded_valid_fst s p q h)

/-- BondReachable で到達可能なノードは start と同じか isBonded 経由。
    p ≠ start の場合、p.layer < s.layerCount -/
private theorem bondReachable_valid_or_start (s : Shape) (start p : QuarterPos)
        (h : BondReachable s start p) :
        p = start ∨ p.layer < s.layerCount := by
    induction h with
    | refl => exact .inl rfl
    | step h_bond _ ih =>
        match ih with
        | .inl h_eq => subst h_eq; exact .inr (isBonded_valid s _ _ h_bond)
        | .inr h_lt => exact .inr h_lt

-- ============================================================
-- BFS 不変条件
-- ============================================================

/-- BFS の不変条件:
    vis 内の全ノードの allPos 内結合隣接は vis ∪ queue に含まれる -/
private def BFSInv (s : Shape) (allPos vis queue : List QuarterPos) : Prop :=
    ∀ v, vis.any (· == v) = true →
      ∀ n, allPos.any (· == n) = true →
        isBonded s v n = true →
        vis.any (· == n) = true ∨ queue.any (· == n) = true

/-- BFS 初期不変条件: vis=[], queue=[start] -/
private theorem bfsInv_initial (s : Shape) (allPos : List QuarterPos)
        (start : QuarterPos) :
        BFSInv s allPos [] [start] := by
    intro v hv; simp [List.any] at hv

/-- 重複スキップで不変条件が保存される -/
private theorem bfsInv_skip (s : Shape) (allPos vis : List QuarterPos)
        (pos : QuarterPos) (rest : List QuarterPos)
        (h_inv : BFSInv s allPos vis (pos :: rest))
        (h_vis : vis.any (· == pos) = true) :
        BFSInv s allPos vis rest := by
    intro v hv n hn hb
    match h_inv v hv n hn hb with
    | .inl h => exact .inl h
    | .inr h =>
        rw [List.any_cons] at h
        cases h_eq : (pos == n) with
        | true =>
            exact .inl (by rw [show pos = n from eq_of_beq h_eq] at h_vis; exact h_vis)
        | false => rw [h_eq, Bool.false_or] at h; exact .inr h

/-- 新ノード処理で不変条件が保存される -/
private theorem bfsInv_process (s : Shape) (allPos vis : List QuarterPos)
        (pos : QuarterPos) (rest : List QuarterPos)
        (h_inv : BFSInv s allPos vis (pos :: rest))
        (h_not_vis : ¬(vis.any (· == pos) = true)) :
        BFSInv s allPos (pos :: vis)
            (rest ++ allPos.filter fun p =>
                isBonded s pos p && !((pos :: vis).any (· == p))) := by
    intro v hv n hn hb
    rw [List.any_cons] at hv
    cases h_vp : (pos == v) with
    | true =>
        have := eq_of_beq h_vp; subst this
        by_cases h_nv : ((pos :: vis).any (· == n)) = true
        · exact .inl h_nv
        · right; rw [List.any_append, Bool.or_eq_true_iff]
          right; rw [List.any_eq_true]
          have h_n_mem : n ∈ allPos := by
              rw [List.any_eq_true] at hn
              obtain ⟨x, h_x_mem, h_x_eq⟩ := hn
              exact eq_of_beq h_x_eq ▸ h_x_mem
          exact ⟨n, List.mem_filter.mpr ⟨h_n_mem, by
            simp [hb, h_nv]⟩, BEq.rfl⟩
    | false =>
        rw [h_vp, Bool.false_or] at hv
        match h_inv v hv n hn hb with
        | .inl h =>
            exact .inl (by rw [List.any_cons]; simp [h])
        | .inr h =>
            rw [List.any_cons] at h
            cases h_pn : (pos == n) with
            | true => exact .inl (by rw [List.any_cons]; simp [h_pn])
            | false =>
                rw [h_pn, Bool.false_or] at h
                exact .inr (by rw [List.any_append, Bool.or_eq_true_iff]; left; exact h)

-- ============================================================
-- BFS 燃料充足性のヘルパー補題
-- ============================================================

/-- フィルタ結果から要素が存在すれば長さ > 0 -/
private theorem filter_length_lt_of_mem_of_not (l : List QuarterPos)
        (pred : QuarterPos → Bool) (x : QuarterPos)
        (h_mem : x ∈ l) (h_not : pred x = false) :
        (l.filter pred).length < l.length := by
    induction l with
    | nil => nomatch h_mem
    | cons a as ih =>
        simp only [List.filter, List.length]
        cases h_mem with
        | head =>
            simp only [h_not, ite_false]
            have := List.length_filter_le (p := pred) as
            omega
        | tail _ h_as =>
            cases h_pa : pred a with
            | false =>
                simp only [h_pa, ite_false]
                have := ih h_as
                omega
            | true =>
                simp only [h_pa, ite_true, List.length]
                have := ih h_as
                omega

/-- AND 条件のフィルタは単独条件のフィルタ以下の長さ -/
private theorem filter_and_length_le (l : List QuarterPos)
        (p q : QuarterPos → Bool) :
        (l.filter fun x => p x && q x).length ≤ (l.filter q).length := by
    induction l with
    | nil => simp [List.filter]
    | cons a as ih =>
        simp only [List.filter]
        cases h_q : q a with
        | false =>
            simp only [h_q, Bool.and_false, ite_false]
            have := ih; omega
        | true =>
            simp only [h_q, Bool.and_true]
            cases h_p : p a with
            | true =>
                simp only [h_p, ite_true, ite_true, List.length]
                have := ih; omega
            | false =>
                simp only [h_p, ite_false, ite_true, List.length]
                have := ih; omega

/-- nb + u'² ≤ u² を示すための算術補題。
    nb ≤ u' かつ u' < u のとき成立。 -/
private theorem add_sq_le_sq_of_lt (nb u' u : Nat)
        (h_nb : nb ≤ u') (h_lt : u' < u) :
        nb + u' * u' ≤ u * u := by
    have h1 : u' ≤ u := Nat.le_of_lt h_lt
    have h3 : u' * (u' + 1) ≤ u * u := Nat.mul_le_mul h1 h_lt
    have h4 : u' + u' * u' = u' * (u' + 1) := by rw [Nat.mul_succ]; omega
    omega

/-- BFS が不変条件を保存する。fuel に関する帰納法。
    燃料条件: fuel + 1 ≥ |queue| + (未訪問 allPos 数)² -/
private theorem bfs_invariant_preserved (s : Shape) (allPos vis queue : List QuarterPos)
        (fuel : Nat) (h_inv : BFSInv s allPos vis queue)
        (h_fuel : fuel + 1 ≥ queue.length +
            (allPos.filter fun p => !(vis.any (· == p))).length *
            (allPos.filter fun p => !(vis.any (· == p))).length)
        (h_bond_in_allPos : ∀ p q, isBonded s p q = true → allPos.any (· == p) = true) :
        BFSInv s allPos (bfs s allPos vis queue fuel) [] := by
    induction fuel generalizing vis queue with
    | zero =>
        -- fuel=0: bfs は vis を返す
        simp only [bfs]
        -- Goal: BFSInv s allPos vis []
        -- つまり ∀ v ∈ vis, ∀ n ∈ allPos, bonded → n ∈ vis ∨ n ∈ []
        intro v hv n hn hb
        -- 目標: vis.any (· == n) = true ∨ ([].any (· == n)) = true
        -- 左側のみで十分
        left
        -- 目標: vis.any (· == n) = true
        -- h_inv から: vis.any (· == n) ∨ queue.any (· == n)
        cases h_inv v hv n hn hb with
        | inl h => exact h
        | inr h_q =>
            -- n は queue に含まれる → queue 非空 → u² ≤ 0 → u = 0
            have h_qlen : queue.length ≥ 1 := by
                cases queue with
                | nil => simp [List.any] at h_q
                | cons _ _ => simp [List.length]
            -- filter 長 = 0 を示す (非線形算術: n*n ≤ 0 → n = 0)
            have h_u_zero : (allPos.filter fun p => !(vis.any (· == p))).length = 0 := by
                cases hu : (allPos.filter fun p => !(vis.any (· == p))).length with
                | zero => rfl
                | succ m =>
                    rw [hu] at h_fuel
                    have : (m + 1) * (m + 1) ≥ 1 :=
                        Nat.mul_le_mul (Nat.succ_le_succ (Nat.zero_le m))
                            (Nat.succ_le_succ (Nat.zero_le m))
                    omega
            -- フィルタ長 0 → フィルタ結果は空リスト
            have h_filter_nil : allPos.filter (fun p => !(vis.any (· == p))) = [] := by
                match h_f : allPos.filter (fun p => !(vis.any (· == p))) with
                | [] => rfl
                | _ :: _ =>
                    rw [h_f] at h_u_zero
                    simp [List.length] at h_u_zero
            -- n ∈ allPos なので vis.any (· == n) = true を導く
            rw [List.any_eq_true] at hn
            obtain ⟨x, hx_mem, hx_eq⟩ := hn
            have hx_is_n := eq_of_beq hx_eq; subst hx_is_n
            -- x ∈ allPos かつフィルタ空 → vis.any (· == x) = true
            cases h_vis_x : vis.any (· == x) with
            | true => rfl
            | false =>
                exfalso
                have h_x_in : x ∈ allPos.filter (fun p => !(vis.any (· == p))) :=
                    List.mem_filter.mpr ⟨hx_mem, by simp [h_vis_x]⟩
                rw [h_filter_nil] at h_x_in
                nomatch h_x_in
    | succ n ih =>
        cases queue with
        | nil => exact h_inv
        | cons pos rest =>
            simp only [bfs]
            split
            · -- スキップ: pos は既に訪問済み
              rename_i h_vis
              apply ih vis rest (bfsInv_skip s allPos vis pos rest h_inv h_vis)
              · have h_len : (pos :: rest).length = rest.length + 1 := rfl
                rw [h_len] at h_fuel; omega
            · -- 処理: pos は未訪問
              rename_i h_not_vis
              have h_not_vis' : ¬(vis.any (· == pos) = true) := by
                  intro h; rw [h] at h_not_vis; exact h_not_vis rfl
              apply ih (pos :: vis) (rest ++ _)
                  (bfsInv_process s allPos vis pos rest h_inv h_not_vis')
              · -- 燃料条件の伝播: nb + u'² ≤ u²
                simp only [List.length_append]
                have h_len : (pos :: rest).length = rest.length + 1 := rfl
                rw [h_len] at h_fuel
                -- h_fuel: n + 1 + 1 ≥ rest.length + 1 + u * u
                -- 目標: n + 1 ≥ rest.length + nb + u' * u'
                -- key: nb + u' * u' ≤ u * u
                have h_key : (allPos.filter fun p =>
                        isBonded s pos p && !((pos :: vis).any (· == p))).length +
                    (allPos.filter fun p => !((pos :: vis).any (· == p))).length *
                    (allPos.filter fun p => !((pos :: vis).any (· == p))).length ≤
                    (allPos.filter fun p => !(vis.any (· == p))).length *
                    (allPos.filter fun p => !(vis.any (· == p))).length := by
                  -- nb ≤ u'
                  have h_nb_le : (allPos.filter fun p =>
                          isBonded s pos p && !((pos :: vis).any (· == p))).length ≤
                      (allPos.filter fun p => !((pos :: vis).any (· == p))).length :=
                      filter_and_length_le allPos
                          (fun p => isBonded s pos p)
                          (fun p => !((pos :: vis).any (· == p)))
                  cases h_pos : allPos.any (· == pos) with
                  | false =>
                      -- pos ∉ allPos → bonds false → nb = 0
                      have h_no_bond : ∀ x, isBonded s pos x = false := by
                          intro x
                          cases h_bond : isBonded s pos x with
                          | false => rfl
                          | true =>
                              exact absurd (h_bond_in_allPos pos x h_bond) (by simp [h_pos])
                      have h_nb_zero : (allPos.filter fun p =>
                              isBonded s pos p && !((pos :: vis).any (· == p))).length = 0 := by
                          have h_pred_false : ∀ x, (isBonded s pos x &&
                              !((pos :: vis).any (· == x))) = false := by
                              intro x; simp [h_no_bond x]
                          suffices h_gen : ∀ l : List QuarterPos,
                              (l.filter fun p => isBonded s pos p &&
                                  !((pos :: vis).any (· == p))).length = 0 from h_gen allPos
                          intro l
                          induction l with
                          | nil => rfl
                          | cons a as ih_l =>
                              simp only [List.filter, h_pred_false a, ite_false]; exact ih_l
                      -- u' = u (pos ∉ allPos → フィルタ不変)
                      have h_u_eq :
                          (allPos.filter fun p => !((pos :: vis).any (· == p))).length =
                          (allPos.filter fun p => !(vis.any (· == p))).length := by
                          congr 1
                          apply List.filter_congr
                          intro x hx
                          simp only [List.any_cons]
                          have : (pos == x) = false := by
                              cases h_eq : (pos == x) with
                              | false => rfl
                              | true =>
                                  exfalso
                                  have h_eq' := eq_of_beq h_eq
                                  have h_mem_pos : pos ∈ allPos := h_eq' ▸ hx
                                  have h_pred_pos :
                                      (fun y : QuarterPos => y == pos) pos = true := BEq.rfl
                                  have h_any_true :
                                      (allPos.any (· == pos)) = true :=
                                      List.any_eq_true.mpr ⟨pos, h_mem_pos, h_pred_pos⟩
                                  rw [h_pos] at h_any_true
                                  exact absurd h_any_true Bool.false_ne_true
                          simp [this]
                      rw [h_nb_zero, h_u_eq]; omega
                  | true =>
                      -- pos ∈ allPos ∧ pos ∉ vis → u' < u
                      have h_pos_mem : pos ∈ allPos := by
                          rw [List.any_eq_true] at h_pos
                          obtain ⟨x, hx_mem, hx_eq⟩ := h_pos
                          exact eq_of_beq hx_eq ▸ hx_mem
                      have h_vis_false : vis.any (· == pos) = false := by
                          cases hh : vis.any (· == pos) with
                          | false => rfl
                          | true => exact absurd hh h_not_vis'
                      have h_pos_in_u :
                          pos ∈ allPos.filter (fun p => !(vis.any (· == p))) :=
                          List.mem_filter.mpr ⟨h_pos_mem, by simp [h_vis_false]⟩
                      have h_u'_lt_u :
                          (allPos.filter fun p => !((pos :: vis).any (· == p))).length <
                          (allPos.filter fun p => !(vis.any (· == p))).length := by
                          have h_eq :
                              (allPos.filter fun p => !((pos :: vis).any (· == p))) =
                              (allPos.filter (fun p => !(vis.any (· == p)))).filter
                                  (fun p => !(pos == p)) := by
                              rw [List.filter_filter]
                              apply List.filter_congr
                              intro x _
                              simp only [List.any_cons, Bool.not_or, Bool.and_comm]
                          rw [h_eq]
                          exact filter_length_lt_of_mem_of_not
                              (allPos.filter (fun p => !(vis.any (· == p))))
                              (fun p => !(pos == p)) pos
                              h_pos_in_u
                              (by simp [BEq.rfl])
                      exact add_sq_le_sq_of_lt _ _ _ h_nb_le h_u'_lt_u
                omega

/-- allValid の長さは layerCount * 4 -/
private theorem allValid_length (s : Shape) :
        (QuarterPos.allValid s).length = s.layerCount * 4 := by
    simp only [QuarterPos.allValid, Shape.layerCount]
    generalize s.layers.length = n
    induction n with
    | zero => simp
    | succ k ih =>
        rw [List.range_succ, List.flatMap_append, List.length_append, ih]
        simp [List.flatMap_cons, List.flatMap_nil, List.map, Direction.all]
        omega

-- ============================================================
-- BFS 閉包→BondReachable
-- ============================================================

/-- 閉じた集合は BondReachable を含む。
    isBonded の結果が allPos に含まれるという条件で十分。 -/
private theorem closed_contains_reachable (s : Shape) (allPos vis : List QuarterPos)
        (h_closed : BFSInv s allPos vis [])
        (start p : QuarterPos)
        (h_start : vis.any (· == start) = true)
        (h_reach : BondReachable s start p)
        (h_isBonded_valid : ∀ q r, isBonded s q r = true → allPos.any (· == r) = true) :
        vis.any (· == p) = true := by
    induction h_reach with
    | refl => exact h_start
    | step h_bond _ ih =>
        match h_closed _ h_start _ (h_isBonded_valid _ _ h_bond) h_bond with
        | .inl h => exact ih h
        | .inr h => simp [List.any] at h

/-- allValid s は isBonded の結果を全て含む -/
private theorem allValid_contains_isBonded (s : Shape) (p q : QuarterPos)
        (h : isBonded s p q = true) :
        (QuarterPos.allValid s).any (· == q) = true :=
    (allValid_any_iff_layer s q).mpr (isBonded_valid s p q h)

-- ============================================================
-- crystalCluster の健全性
-- ============================================================

/-- crystalCluster の健全性:
    結果に含まれる要素は start から BondReachable -/
theorem crystalCluster_sound (s : Shape) (start p : QuarterPos) :
        (crystalCluster s start).any (· == p) = true →
        BondReachable s start p := by
    intro h
    unfold crystalCluster at h
    match bfs_sound s _ [] [start] _ p h with
    | .inl h_vis => simp [List.any] at h_vis
    | .inr ⟨q, h_q, h_reach⟩ =>
        rw [List.any_cons, Bool.or_eq_true_iff] at h_q
        cases h_q with
        | inl h_eq =>
            have := eq_of_beq h_eq; subst this; exact h_reach
        | inr h_rest =>
            simp [List.any] at h_rest

-- ============================================================
-- crystalCluster の rotate180 等変性
-- ============================================================

/-- crystalCluster メンバーシップの rotate180 等変性。
    BFS の健全性と BFS 不変条件の保存性を経由して証明する。
    燃料充足性は queue.length + (未訪問数)² のポテンシャル引数で保証。 -/
theorem crystalCluster_mem_rotate180 (s : Shape) (start p : QuarterPos) :
        (crystalCluster s start).any (· == p) =
        (crystalCluster s.rotate180 start.rotate180).any (· == p.rotate180) := by
    cases h : (crystalCluster s start).any (· == p) with
    | true =>
        -- p は start から BondReachable
        have h_reach := crystalCluster_sound s start p h
        have h_reach' := bondReachable_rotate180 s start p h_reach
        symm
        -- crystalCluster s.r180 start.r180 を展開
        unfold crystalCluster
        rw [allValid_rotate180_eq, Shape.layerCount_rotate180]
        -- BFS 不変条件の閉包性
        have h_inv := bfs_invariant_preserved s.rotate180 (QuarterPos.allValid s) []
            [start.rotate180] (s.layerCount * 4 * (s.layerCount * 4))
            (bfsInv_initial s.rotate180 (QuarterPos.allValid s) start.rotate180)
            (by
                -- 空 vis でのフィルタは元リストと同じ長さ
                have h_filter : (QuarterPos.allValid s).filter (fun p =>
                    !(([] : List QuarterPos).any (· == p))) = QuarterPos.allValid s :=
                    List.filter_eq_self.mpr (by intro x _; simp [List.any])
                simp only [h_filter, List.length, allValid_length]
                omega)
            (fun p q h => by
                rw [← allValid_rotate180_eq]
                exact allValid_contains_isBonded_fst s.rotate180 p q h)
        -- start.r180 は結果に含まれる
        have h_start : (bfs s.rotate180 (QuarterPos.allValid s) [] [start.rotate180]
            (s.layerCount * 4 * (s.layerCount * 4))).any (· == start.rotate180) = true := by
            cases hn : s.layerCount with
            | zero =>
                -- layerCount = 0 → fuel = 0 → bfs = []
                -- しかし h : (crystalCluster s start).any ... = true
                -- crystalCluster s start = bfs s (allValid s) [] [start] 0 = []
                -- any [] = false ≠ true → 矛盾
                simp [hn] at h ⊢
                unfold crystalCluster at h; simp [hn, bfs] at h
            | succ n =>
                exact bfs_contains_start s.rotate180 (QuarterPos.allValid s) start.rotate180
                    (Nat.succ n * 4 * (Nat.succ n * 4)) (by simp)
        -- 閉包性から p.r180 も結果に含まれる
        exact closed_contains_reachable s.rotate180 (QuarterPos.allValid s) _ h_inv
            start.rotate180 p.rotate180 h_start h_reach'
            (fun q r h_bond => by
                rw [← allValid_rotate180_eq]
                exact allValid_contains_isBonded s.rotate180 q r h_bond)
    | false =>
        symm
        cases h' : (crystalCluster s.rotate180 start.rotate180).any (· == p.rotate180) with
        | false => rfl
        | true =>
            -- p.r180 は start.r180 から到達可能
            have h_reach' := crystalCluster_sound s.rotate180 start.rotate180 p.rotate180 h'
            -- r180 を戻す
            have h_reach : BondReachable s start p := by
                have := bondReachable_rotate180 s.rotate180 start.rotate180 p.rotate180 h_reach'
                simp [Shape.rotate180_rotate180, QuarterPos.rotate180_rotate180] at this
                exact this
            -- BFS 不変条件の閉包性（s 側）
            unfold crystalCluster at h
            have h_inv := bfs_invariant_preserved s (QuarterPos.allValid s) []
                [start] (s.layerCount * 4 * (s.layerCount * 4))
                (bfsInv_initial s (QuarterPos.allValid s) start)
                (by
                    have h_filter : (QuarterPos.allValid s).filter (fun p =>
                        !(([] : List QuarterPos).any (· == p))) = QuarterPos.allValid s :=
                        List.filter_eq_self.mpr (by intro x _; simp [List.any])
                    simp only [h_filter, List.length, allValid_length]
                    omega)
                (fun p q h => allValid_contains_isBonded_fst s p q h)
            have h_start_mem : (bfs s (QuarterPos.allValid s) [] [start]
                (s.layerCount * 4 * (s.layerCount * 4))).any (· == start) = true := by
                cases hn : s.layerCount with
                | zero =>
                    -- 同様に矛盾
                    unfold crystalCluster at h'
                    simp [hn, bfs, allValid_rotate180_eq] at h'
                | succ n =>
                    exact bfs_contains_start s (QuarterPos.allValid s) start
                        (Nat.succ n * 4 * (Nat.succ n * 4)) (by simp)
            -- 閉包性から p も結果に含まれる
            have h_mem := closed_contains_reachable s (QuarterPos.allValid s) _ h_inv
                start p h_start_mem h_reach
                (fun q r h_bond => allValid_contains_isBonded s q r h_bond)
            rw [h_mem] at h; exact Bool.noConfusion h

end CrystalBond
