-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Behavior.Gravity.Defs

namespace Gravity

-- ============================================================
-- 180° 回転等変性の基盤補題
-- Rotate180Lemmas.lean に共通補題を集約済み
-- ============================================================

open QuarterPos (getDir_rotate180 getQuarter_rotate180 getQuarter_rotate180_inv)
open Shape (layers_rotate180 clearPositions_rotate180)

-- BFS ヘルパー用エイリアス（LayerPerm の具象化）
abbrev σ_r180 := LayerPerm.rotate180
abbrev σ_rCW := LayerPerm.rotateCW

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
-- structuralBfs / groundingBfs の rotate180 等変性
-- （genericBfs_map_comm + eq_generic による導出）
-- ============================================================

/-- structuralBfs は genericBfs (isStructurallyBonded s) と等しい -/
theorem structuralBfs_eq_generic (s : Shape)
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

/-- groundingBfs は genericBfs (groundingEdge s) と等しい -/
theorem groundingBfs_eq_generic (s : Shape)
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

/-- structuralBfs は rotate180 で等変（genericBfs_map_comm より導出） -/
theorem structuralBfs_rotate180 (s : Shape)
        (allPos visited queue : List QuarterPos) (fuel : Nat) :
        structuralBfs s.rotate180
            (allPos.map QuarterPos.rotate180)
            (visited.map QuarterPos.rotate180)
            (queue.map QuarterPos.rotate180) fuel =
        (structuralBfs s allPos visited queue fuel).map QuarterPos.rotate180 := by
    simp only [structuralBfs_eq_generic]
    exact genericBfs_map_comm
        (isStructurallyBonded s) (isStructurallyBonded s.rotate180) QuarterPos.rotate180
        (fun a b => isStructurallyBonded_rotate180 s a b)
        σ_r180.quarterPos_beq allPos visited queue fuel

/-- isUpwardGroundingContact は rotate180 で不変（レイヤが変わらないため） -/
theorem isUpwardGroundingContact_rotate180 (s : Shape) (p1 p2 : QuarterPos) :
        isUpwardGroundingContact (s.rotate180) (p1.rotate180) (p2.rotate180) =
        isUpwardGroundingContact s p1 p2 := by
    unfold isUpwardGroundingContact
    rw [isGroundingContact_rotate180]
    congr 1

/-- groundingEdge は rotate180 で不変 -/
theorem groundingEdge_rotate180 (s : Shape) (p1 p2 : QuarterPos) :
        groundingEdge (s.rotate180) (p1.rotate180) (p2.rotate180) =
        groundingEdge s p1 p2 := by
    simp only [groundingEdge, isUpwardGroundingContact_rotate180,
        isStructurallyBonded_rotate180]

/-- groundingBfs は rotate180 で等変（genericBfs_map_comm より導出） -/
theorem groundingBfs_rotate180 (s : Shape)
        (allPos visited queue : List QuarterPos) (fuel : Nat) :
        groundingBfs s.rotate180
            (allPos.map QuarterPos.rotate180)
            (visited.map QuarterPos.rotate180)
            (queue.map QuarterPos.rotate180) fuel =
        (groundingBfs s allPos visited queue fuel).map QuarterPos.rotate180 := by
    simp only [groundingBfs_eq_generic]
    exact genericBfs_map_comm
        (groundingEdge s) (groundingEdge s.rotate180) QuarterPos.rotate180
        (fun a b => groundingEdge_rotate180 s a b)
        σ_r180.quarterPos_beq allPos visited queue fuel

-- ============================================================
-- structuralBfs の rotateCW 等変性
-- ============================================================

/-- isStructurallyBonded は rotateCW で不変 -/
theorem isStructurallyBonded_rotateCW (s : Shape) (p1 p2 : QuarterPos) :
        isStructurallyBonded (s.rotateCW) (p1.rotateCW) (p2.rotateCW) =
        isStructurallyBonded s p1 p2 := by
    simp only [isStructurallyBonded, QuarterPos.getQuarter_rotateCW]
    simp only [QuarterPos.rotateCW, Direction.adjacent_rotateCW, σ_rCW.dir_beq]

/-- structuralBfs は rotateCW で等変（genericBfs_map_comm より導出） -/
theorem structuralBfs_rotateCW (s : Shape)
        (allPos visited queue : List QuarterPos) (fuel : Nat) :
        structuralBfs s.rotateCW
            (allPos.map QuarterPos.rotateCW)
            (visited.map QuarterPos.rotateCW)
            (queue.map QuarterPos.rotateCW) fuel =
        (structuralBfs s allPos visited queue fuel).map QuarterPos.rotateCW := by
    simp only [structuralBfs_eq_generic]
    exact genericBfs_map_comm
        (isStructurallyBonded s) (isStructurallyBonded s.rotateCW) QuarterPos.rotateCW
        (fun a b => isStructurallyBonded_rotateCW s a b)
        σ_rCW.quarterPos_beq allPos visited queue fuel

-- ============================================================
-- structuralClusterList / groundedPositionsList の rotate180 等変性
-- ============================================================

/-- structuralClusterList を mapped allPos で呼んだ場合の等変性 -/
theorem structuralClusterList_rotate180_mapped (s : Shape) (pos : QuarterPos) :
        structuralBfs s.rotate180
            ((QuarterPos.allValid s).map QuarterPos.rotate180) []
            [pos.rotate180]
            (s.layerCount * 4 * (s.layerCount * 4)) =
        (structuralClusterList s pos).map QuarterPos.rotate180 := by
    unfold structuralClusterList
    exact structuralBfs_rotate180 s (QuarterPos.allValid s) [] [pos]
        (s.layerCount * 4 * (s.layerCount * 4))

/-- groundedPositionsList を mapped allPos で呼んだ場合の等変性 -/
theorem groundedPositionsList_rotate180_mapped (s : Shape) :
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
theorem ofLayers_rotate180 (ls : List Layer) :
        (Shape.ofLayers ls).map Shape.rotate180 =
        Shape.ofLayers (ls.map Layer.rotate180) := by
    cases ls with
    | nil => rfl
    | cons l rest =>
        simp only [Shape.ofLayers, Option.map]
        congr 1

/-- Option Shape の normalize と rotate180 の可換性 -/
theorem option_bind_normalize_rotate180 (os : Option Shape) :
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
def FallingUnit.rotate180 : FallingUnit → FallingUnit
    | .cluster ps => .cluster (ps.map QuarterPos.rotate180)
    | .pin p => .pin p.rotate180

/-- FallingUnit.positions は rotate180 で等変 -/
theorem FallingUnit.positions_rotate180 (u : FallingUnit) :
        u.rotate180.positions = u.positions.map QuarterPos.rotate180 := by
    cases u with
    | cluster ps => rfl
    | pin p => rfl

/-- QuarterPos.rotate180 は layer を保持 -/
theorem QuarterPos.rotate180_layer (p : QuarterPos) :
        p.rotate180.layer = p.layer := rfl

/-- QuarterPos.rotate180 の dir フィールド -/
theorem QuarterPos.rotate180_dir (p : QuarterPos) :
        p.rotate180.dir = p.dir.rotate180 := rfl

/-- map が foldl の関数を保存する場合、foldl (map g l) = foldl l -/
theorem foldl_map_layer (l : List QuarterPos) (init : Nat) :
        (l.map QuarterPos.rotate180).foldl (fun a q => min a q.layer) init =
        l.foldl (fun a q => min a q.layer) init := by
    induction l generalizing init with
    | nil => rfl
    | cons p ps ih => exact ih _

/-- FallingUnit.minLayer は rotate180 で不変 -/
theorem FallingUnit.minLayer_rotate180 (u : FallingUnit) :
        u.rotate180.minLayer = u.minLayer := by
    simp only [FallingUnit.minLayer, FallingUnit.positions_rotate180]
    cases u.positions with
    | nil => rfl
    | cons p rest => exact foldl_map_layer rest p.layer

/-- typeOrd は rotate180 で不変 -/
theorem FallingUnit.typeOrd_rotate180 (u : FallingUnit) :
        u.rotate180.typeOrd = u.typeOrd := by
    cases u <;> rfl

/-- sortGroup は rotate180 で不変 -/
theorem FallingUnit.sortGroup_rotate180 (u : FallingUnit) :
        u.rotate180.sortGroup = u.sortGroup := by
    simp only [FallingUnit.sortGroup, FallingUnit.minLayer_rotate180,
        FallingUnit.typeOrd_rotate180]

/-- positions の map rotate180 した filterMap は元の filterMap と同じ (layer 列) -/
theorem filterMap_rotate180_layer (ps : List QuarterPos) (d : Direction) :
        (ps.map QuarterPos.rotate180).filterMap (fun p =>
            if p.dir == d.rotate180 then some p.layer else none) =
        ps.filterMap (fun p => if p.dir == d then some p.layer else none) := by
    rw [List.filterMap_map]
    congr 1
    funext p
    simp only [Function.comp, QuarterPos.rotate180, σ_r180.dir_beq]

/-- FallingUnit.minLayerAtDir は rotate180 で等変 -/
theorem FallingUnit.minLayerAtDir_rotate180 (u : FallingUnit) (d : Direction) :
        u.rotate180.minLayerAtDir (d.rotate180) = u.minLayerAtDir d := by
    unfold FallingUnit.minLayerAtDir
    rw [FallingUnit.positions_rotate180, filterMap_rotate180_layer]

-- ============================================================
-- shouldProcessBefore / sortFallingUnits の rotate180 等変性
-- ============================================================

/-- minLayerAtDir は rotate180 適用後に方角も rotate180 で戻る -/
theorem FallingUnit.minLayerAtDir_rotate180' (u : FallingUnit) (d : Direction) :
        u.rotate180.minLayerAtDir d = u.minLayerAtDir d.rotate180 := by
    cases d with
    | ne => exact FallingUnit.minLayerAtDir_rotate180 u .sw
    | se => exact FallingUnit.minLayerAtDir_rotate180 u .nw
    | sw => exact FallingUnit.minLayerAtDir_rotate180 u .ne
    | nw => exact FallingUnit.minLayerAtDir_rotate180 u .se

/-- Direction.all.any は rotate180 置換で不変 -/
theorem Direction.any_rotate180 (f : Direction → Bool) :
        Direction.all.any (f ∘ Direction.rotate180) = Direction.all.any f := by
    simp only [Direction.all, List.any_cons, List.any_nil, Function.comp, Direction.rotate180,
        Bool.or_false]
    cases f Direction.ne <;> cases f Direction.se <;> cases f Direction.sw <;> cases f Direction.nw <;> rfl

/-- shouldProcessBefore は rotate180 で不変 -/
theorem shouldProcessBefore_rotate180 (a b : FallingUnit) :
        shouldProcessBefore a.rotate180 b.rotate180 =
        shouldProcessBefore a b := by
    unfold shouldProcessBefore
    simp only [FallingUnit.minLayerAtDir_rotate180']
    simpa only [Function.comp] using
        (Direction.any_rotate180 (fun d =>
            match a.minLayerAtDir d, b.minLayerAtDir d with
            | some la, some lb => decide (la < lb)
            | _, _ => false))

/-- insertSorted は rotate180 で等変 -/
theorem insertSorted_rotate180 (u : FallingUnit) (sorted : List FallingUnit) (fuel : Nat) :
        (insertSorted u sorted fuel).map FallingUnit.rotate180 =
        insertSorted u.rotate180 (sorted.map FallingUnit.rotate180) fuel := by
    induction fuel generalizing sorted with
    | zero => simp only [insertSorted, List.map_cons]
    | succ n ih =>
        cases sorted with
        | nil => simp only [insertSorted, List.map_cons, List.map]
        | cons v rest =>
            -- rotate180 後の条件は元の条件と一致
            have hspb1 : shouldProcessBefore u.rotate180 v.rotate180 =
                    shouldProcessBefore u v := shouldProcessBefore_rotate180 u v
            -- map を展開して RHS を正規化
            show (insertSorted u (v :: rest) (n + 1)).map FallingUnit.rotate180 =
                insertSorted u.rotate180 (v.rotate180 :: rest.map FallingUnit.rotate180) (n + 1)
            -- 2 分岐を by_cases で場合分け
            by_cases h1 : shouldProcessBefore u v
            · -- shouldProcessBefore u v = true
              have lhs : insertSorted u (v :: rest) (n + 1) = u :: v :: rest := by
                  show (if shouldProcessBefore u v then u :: v :: rest
                      else v :: insertSorted u rest n) = _
                  simp only [h1, ↓reduceIte]
              have rhs : insertSorted u.rotate180 (v.rotate180 :: rest.map FallingUnit.rotate180) (n + 1) =
                  u.rotate180 :: v.rotate180 :: rest.map FallingUnit.rotate180 := by
                  show (if shouldProcessBefore u.rotate180 v.rotate180 then _
                      else _) = _
                  simp only [hspb1, h1, ↓reduceIte]
              rw [lhs, rhs]; simp only [List.map]
            · -- shouldProcessBefore u v = false → スキップして再帰
              simp only [Bool.not_eq_true] at h1
              have h1' : shouldProcessBefore u.rotate180 v.rotate180 = false := by
                  rw [hspb1]; exact h1
              have lhs : insertSorted u (v :: rest) (n + 1) =
                  v :: insertSorted u rest n := by
                  show (if shouldProcessBefore u v then u :: v :: rest
                      else v :: insertSorted u rest n) = _
                  simp only [h1, Bool.false_eq_true, ↓reduceIte]
              have rhs : insertSorted u.rotate180 (v.rotate180 :: rest.map FallingUnit.rotate180) (n + 1) =
                  v.rotate180 :: insertSorted u.rotate180 (rest.map FallingUnit.rotate180) n := by
                  show (if shouldProcessBefore u.rotate180 v.rotate180 then _
                      else _) = _
                  simp only [h1', Bool.false_eq_true, ↓reduceIte]
              rw [lhs, rhs]; simp only [List.map]
              exact congrArg _ (ih rest)

-- sortFallingUnits'_rotate180 は fallingUnitOrd（全順序）では不要
-- Phase 1 は derived comparison で map_mergeSort を使用する

-- ============================================================
-- sortFallingUnits の置換性（Perm）
-- ============================================================

/-- insertSorted の結果は入力の置換である -/
theorem insertSorted_perm (u : FallingUnit) (sorted : List FallingUnit) (fuel : Nat) :
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
            · -- shouldProcessBefore u v = true: u :: v :: rest — そのまま
              exact List.Perm.refl _
            · -- shouldProcessBefore u v = false: v :: insertSorted u rest fuel
              exact ((ih rest).cons v).trans (List.Perm.swap u v rest)

/-- sortFallingUnits の結果は入力の置換である -/
theorem sortFallingUnits_perm (units : List FallingUnit) :
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
theorem insertSorted_any_positions (u : FallingUnit) (sorted : List FallingUnit)
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
            · -- shouldProcessBefore u v = true: u :: v :: rest → そのまま
              rfl
            · -- shouldProcessBefore u v = false: v :: insertSorted u rest fuel
              simp only [List.flatMap_cons, List.any_append]
              rw [ih]
              simp only [List.flatMap_cons, List.any_append]
              cases u.positions.any (· == p) <;>
                  cases v.positions.any (· == p) <;>
                  simp only [List.any_flatMap, Bool.false_or, Bool.true_or, Bool.or_true, Bool.or_self]

/-- sortFallingUnits は flatMap positions の .any メンバーシップを保存する -/
theorem sortFallingUnits_any_positions (units : List FallingUnit) (p : QuarterPos) :
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
    | nil => intro acc; simp only [List.foldl_nil, List.any_flatMap, List.append_nil]
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
            simp only [Bool.or_self, Bool.or_true, Bool.or_false]

/-- sortFallingUnits' の結果は入力の置換である（List.mergeSort_perm から直接） -/
theorem sortFallingUnits'_perm (units : List FallingUnit) :
        (sortFallingUnits' units).Perm units :=
    List.mergeSort_perm ..

/-- sortFallingUnits' は flatMap positions の .any メンバーシップを保存する -/
theorem sortFallingUnits'_any_positions (units : List FallingUnit) (p : QuarterPos) :
        ((sortFallingUnits' units).flatMap FallingUnit.positions).any (· == p) =
        (units.flatMap FallingUnit.positions).any (· == p) := by
    simp only [List.any_flatMap]
    exact (sortFallingUnits'_perm units).any_eq

/-- sortFallingUnits' は長さを保存する -/
theorem sortFallingUnits'_length (units : List FallingUnit) :
        (sortFallingUnits' units).length = units.length :=
    (sortFallingUnits'_perm units).length_eq

-- ============================================================
-- メンバーシップ等変性
-- ============================================================

/-- allValid のメンバーシップは layer < layerCount と同値 -/
theorem allValid_any_iff_layer' (s : Shape) (p : QuarterPos) :
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
theorem allValid_length' (s : Shape) :
        (QuarterPos.allValid s).length = s.layerCount * 4 := by
    simp only [QuarterPos.allValid, Shape.layerCount]
    generalize s.layers.length = n
    induction n with
    | zero => simp only [List.range_zero, List.flatMap_nil, List.length_nil, Nat.zero_mul]
    | succ k ih =>
        rw [List.range_succ, List.flatMap_append, List.length_append, ih]
        simp only [Direction.all, List.map_cons, List.map, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
        omega

/-- isStructurallyBonded s p q = true ならば q.layer < s.layerCount -/
theorem isStructurallyBonded_valid (s : Shape) (p q : QuarterPos)
        (h : isStructurallyBonded s p q = true) :
        q.layer < s.layerCount := by
    simp only [isStructurallyBonded] at h
    cases hq : q.getQuarter s with
    | none => simp only [hq, reduceCtorEq, imp_self, implies_true, Bool.false_eq_true] at h
    | some _ =>
        simp only [Shape.layerCount]
        unfold QuarterPos.getQuarter at hq
        cases hl : s.layers[q.layer]? with
        | none => simp only [hl, reduceCtorEq] at hq
        | some _ => exact (List.getElem?_eq_some_iff.mp hl).1

/-- isGroundingContact s p q = true ならば q.layer < s.layerCount -/
theorem isGroundingContact_valid (s : Shape) (p q : QuarterPos)
        (h : isGroundingContact s p q = true) :
        q.layer < s.layerCount := by
    simp only [isGroundingContact] at h
    cases hq : q.getQuarter s with
    | none => simp only [hq, reduceCtorEq, imp_self, implies_true, Bool.false_eq_true] at h
    | some _ =>
        simp only [Shape.layerCount]
        unfold QuarterPos.getQuarter at hq
        cases hl : s.layers[q.layer]? with
        | none => simp only [hl, reduceCtorEq] at hq
        | some _ => exact (List.getElem?_eq_some_iff.mp hl).1

/-- isGroundingContact s p q = true ならば p.layer < s.layerCount -/
theorem isGroundingContact_valid_fst (s : Shape) (p q : QuarterPos)
        (h : isGroundingContact s p q = true) :
        p.layer < s.layerCount := by
    simp only [isGroundingContact] at h
    cases hp : p.getQuarter s with
    | none => simp only [hp, Bool.false_eq_true] at h
    | some _ =>
        simp only [Shape.layerCount]
        unfold QuarterPos.getQuarter at hp
        cases hl : s.layers[p.layer]? with
        | none => simp only [hl, reduceCtorEq] at hp
        | some _ => exact (List.getElem?_eq_some_iff.mp hl).1

/-- 構造結合到達可能性は rotate180 で保存される -/
theorem structuralReachable_rotate180 (s : Shape) (p q : QuarterPos)
        (h : GenericReachable (isStructurallyBonded s) p q) :
        GenericReachable (isStructurallyBonded s.rotate180) p.rotate180 q.rotate180 := by
    induction h with
    | refl => exact .refl
    | step h_bond _ ih =>
        exact .step (isStructurallyBonded_rotate180 s _ _ ▸ h_bond) ih

/-- 接地接触到達可能性は rotate180 で保存される -/
theorem groundingReachable_rotate180 (s : Shape) (p q : QuarterPos)
        (h : GenericReachable (isGroundingContact s) p q) :
        GenericReachable (isGroundingContact s.rotate180) p.rotate180 q.rotate180 := by
    induction h with
    | refl => exact .refl
    | step h_bond _ ih =>
        exact .step (isGroundingContact_rotate180 s _ _ ▸ h_bond) ih

/-- 上方向接地接触到達可能性は rotate180 で保存される -/
theorem upwardGroundingReachable_rotate180 (s : Shape) (p q : QuarterPos)
        (h : GenericReachable (isUpwardGroundingContact s) p q) :
        GenericReachable (isUpwardGroundingContact s.rotate180) p.rotate180 q.rotate180 := by
    induction h with
    | refl => exact .refl
    | step h_bond _ ih =>
        exact .step (isUpwardGroundingContact_rotate180 s _ _ ▸ h_bond) ih

/-- groundingEdge 到達可能性は rotate180 で保存される -/
theorem groundingEdgeReachable_rotate180 (s : Shape) (p q : QuarterPos)
        (h : GenericReachable (groundingEdge s) p q) :
        GenericReachable (groundingEdge s.rotate180) p.rotate180 q.rotate180 := by
    induction h with
    | refl => exact .refl
    | step h_bond _ ih =>
        exact .step (groundingEdge_rotate180 s _ _ ▸ h_bond) ih

/-- 構造クラスタの健全性: 結果は start から到達可能 -/
theorem structuralClusterList_sound (s : Shape) (start p : QuarterPos) :
        (structuralClusterList s start).any (· == p) = true →
        GenericReachable (isStructurallyBonded s) start p := by
    intro h; unfold structuralClusterList at h
    rw [structuralBfs_eq_generic] at h
    match genericBfs_sound (isStructurallyBonded s) _ [] [start] _ p h with
    | .inl h_vis => simp only [List.any, Bool.false_eq_true] at h_vis
    | .inr ⟨q, h_q, h_reach⟩ =>
        rw [List.any_cons, Bool.or_eq_true_iff] at h_q
        cases h_q with
        | inl h_eq => exact eq_of_beq h_eq ▸ h_reach
        | inr h_rest => simp only [List.any, Bool.false_eq_true] at h_rest

/-- 構造的到達可能性は canFormBond を保存する -/
theorem structuralReachable_canFormBond (s : Shape) (pos q : QuarterPos)
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
theorem structuralClusterList_complete (s : Shape) (start p : QuarterPos)
        (h_lc : s.layerCount > 0)
        (h_reach : GenericReachable (isStructurallyBonded s) start p) :
        (structuralClusterList s start).any (· == p) = true := by
    unfold structuralClusterList
    rw [structuralBfs_eq_generic]
    have h_inv : GenericBfsInv (isStructurallyBonded s) (QuarterPos.allValid s)
        (genericBfs (isStructurallyBonded s) (QuarterPos.allValid s) [] [start]
            (s.layerCount * 4 * (s.layerCount * 4))) [] := by
      apply genericBfs_invariant_preserved
      · exact GenericBfsInv_initial _ _ _
      · have h_filter : (QuarterPos.allValid s).filter (fun p =>
            !(([] : List QuarterPos).any (· == p))) = QuarterPos.allValid s :=
            List.filter_eq_self.mpr (by intro x _; simp only [List.any, Bool.not_false])
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
theorem structuralClusterList_shared_contains_seed (s : Shape) (pos1 pos2 p : QuarterPos)
        (h_lc : s.layerCount > 0)
        (hp1 : (structuralClusterList s pos1).any (· == p) = true)
        (hp2 : (structuralClusterList s pos2).any (· == p) = true) :
        (structuralClusterList s pos1).any (· == pos2) = true := by
    have h_r1 := structuralClusterList_sound s pos1 p hp1
    have h_r2 := structuralClusterList_sound s pos2 p hp2
    have h_r2_sym := h_r2.symm (isStructurallyBonded_symm s)
    exact structuralClusterList_complete s pos1 pos2 h_lc (h_r1.trans h_r2_sym)

/-- groundedPositionsList の健全性：BFS 結果にメンバーがあれば有効 seed から groundingEdge で到達可能 -/
theorem groundedPositionsList_sound (s : Shape) (p : QuarterPos)
        (h : (groundedPositionsList s).any (· == p) = true) :
        ∃ seed, seed ∈ (QuarterPos.allValid s).filter (fun q =>
            q.layer == 0 && match q.getQuarter s with
            | some q => !q.isEmpty | none => false) ∧
        GenericReachable (groundingEdge s) seed p := by
    unfold groundedPositionsList at h
    rw [groundingBfs_eq_generic] at h
    match genericBfs_sound (groundingEdge s) (QuarterPos.allValid s) []
            _ _ p h with
    | .inl h_vis => simp only [List.any, Bool.false_eq_true] at h_vis
    | .inr ⟨seed, h_seed, h_reach⟩ =>
        exact ⟨seed, by
            rw [List.any_eq_true] at h_seed
            obtain ⟨y, hy, hye⟩ := h_seed; exact eq_of_beq hye ▸ hy,
            h_reach⟩

/-- groundedPositionsList で使う genericBfs の fuel 下界。 -/
private theorem groundedPositionsList_fuel_adequate (s : Shape) :
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
    simp only [h_filter, allValid_length']
    have := List.length_filter_le (fun p =>
        p.layer == 0 && match p.getQuarter s with
        | some q => !q.isEmpty | none => false) (QuarterPos.allValid s)
    rw [allValid_length' s] at this
    omega

/-- groundedPositionsList の完全性：有効 seed から groundingEdge で到達可能なら BFS 結果に含まれる -/
theorem groundedPositionsList_complete (s : Shape) (seed p : QuarterPos)
        (h_seed : seed ∈ (QuarterPos.allValid s).filter (fun q =>
            q.layer == 0 && match q.getQuarter s with
            | some q => !q.isEmpty | none => false))
        (h_reach : GenericReachable (groundingEdge s) seed p) :
        (groundedPositionsList s).any (· == p) = true := by
    unfold groundedPositionsList; rw [groundingBfs_eq_generic]
    have h_fuel := groundedPositionsList_fuel_adequate s
    have h_inv := genericBfs_invariant_preserved (groundingEdge s)
        (QuarterPos.allValid s) []
        ((QuarterPos.allValid s).filter fun p =>
            p.layer == 0 && match p.getQuarter s with
            | some q => !q.isEmpty | none => false)
        (s.layerCount * 4 * (s.layerCount * 4) + s.layerCount * 4)
        (by intro v hv; simp only [List.any, Bool.false_eq_true] at hv)
        h_fuel
        (fun p q h =>
            (allValid_any_iff_layer' s p).mpr
                (isGroundingContact_valid_fst s p q
                    (groundingEdge_base h)))
    have h_seed_layer : seed.layer < s.layerCount := by
        have ⟨h_allValid, _⟩ := List.mem_filter.mp h_seed
        exact (allValid_any_iff_layer' s seed).mp
            (List.any_eq_true.mpr ⟨seed, h_allValid, BEq.rfl⟩)
    have h_seed_in := genericBfs_queue_in_result
        (groundingEdge s) (QuarterPos.allValid s) []
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
                (isGroundingContact_valid_fst s a b
                    (groundingEdge_base h)))
    exact genericBfs_closed_contains_reachable _ _ _ h_inv
        seed p h_seed_in h_reach
        (fun q r h_bond =>
            (allValid_any_iff_layer' s r).mpr
                (isGroundingContact_valid s q r
                    (groundingEdge_base h_bond)))

/-- groundedPositionsList の閉包性：BFS 結果内の点から groundingEdge で到達可能なら BFS 結果に含まれる -/
theorem groundedPositionsList_closed (s : Shape) (start p : QuarterPos)
        (h_start : (groundedPositionsList s).any (· == start) = true)
        (h_reach : GenericReachable (groundingEdge s) start p) :
        (groundedPositionsList s).any (· == p) = true := by
    unfold groundedPositionsList at h_start ⊢
    rw [groundingBfs_eq_generic] at h_start ⊢
    have h_fuel := groundedPositionsList_fuel_adequate s
    have h_inv := genericBfs_invariant_preserved (groundingEdge s)
        (QuarterPos.allValid s) []
        ((QuarterPos.allValid s).filter fun p =>
            p.layer == 0 && match p.getQuarter s with
            | some q => !q.isEmpty | none => false)
        (s.layerCount * 4 * (s.layerCount * 4) + s.layerCount * 4)
        (by intro v hv; simp only [List.any, Bool.false_eq_true] at hv)
        h_fuel
        (fun p q h =>
            (allValid_any_iff_layer' s p).mpr
                (isGroundingContact_valid_fst s p q
                    (groundingEdge_base h)))
    exact genericBfs_closed_contains_reachable _ _ _ h_inv
        start p h_start h_reach
        (fun q r h_bond =>
            (allValid_any_iff_layer' s r).mpr
                (isGroundingContact_valid s q r
                    (groundingEdge_base h_bond)))

/-- 接地 seed の rotate180 変換: seeds(s.r180) → seeds(s) -/
theorem grounding_seed_rotate180 (s : Shape) (seed : QuarterPos)
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
theorem grounding_seed_to_rotate180 (s : Shape) (seed : QuarterPos)
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
theorem any_beq_iff_mem (l : List QuarterPos) (p : QuarterPos) :
        l.any (· == p) = true ↔ p ∈ l := by
    constructor
    · intro h
      rw [List.any_eq_true] at h
      obtain ⟨x, hx, he⟩ := h
      exact eq_of_beq he ▸ hx
    · intro h
      exact List.any_eq_true.mpr ⟨p, h, BEq.rfl⟩

/-- p ∉ groundedPositions s ↔ (groundedPositionsList s).any (· == p) = false -/
theorem not_mem_groundedPositions_iff (s : Shape) (p : QuarterPos) :
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
theorem decide_not_mem_groundedPositions (s : Shape) (p : QuarterPos) :
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

/-- structuralCluster の等変性（汎用版）。
    σ / σ_inv が構造結合到達可能性を双方向保存し、キャンセル条件を満たせば、
    structuralCluster は Finset.image で等変。rotate180 / rotateCW を統合する。 -/
theorem structuralCluster_σ (s : Shape) (start : QuarterPos)
        (σ : QuarterPos → QuarterPos) (σ_inv : QuarterPos → QuarterPos)
        (σ_shape : Shape)
        (h_reach_fwd : ∀ p q, GenericReachable (isStructurallyBonded s) p q →
            GenericReachable (isStructurallyBonded σ_shape) (σ p) (σ q))
        (h_reach_bwd : ∀ p q, GenericReachable (isStructurallyBonded σ_shape) p q →
            GenericReachable (isStructurallyBonded s) (σ_inv p) (σ_inv q))
        (h_cancel : ∀ p, σ (σ_inv p) = p)
        (h_cancel_inv : ∀ p, σ_inv (σ p) = p)
        (h_allValid_σ : QuarterPos.allValid σ_shape = QuarterPos.allValid s)
        (h_layerCount_σ : σ_shape.layerCount = s.layerCount) :
        structuralCluster σ_shape (σ start) =
        (structuralCluster s start).image σ := by
    ext p
    simp only [structuralCluster, Finset.mem_image, List.mem_toFinset]
    constructor
    · intro hp
      have h_reach := structuralClusterList_sound σ_shape (σ start) p
          ((any_beq_iff_mem _ _).mpr hp)
      have h_back : GenericReachable (isStructurallyBonded s) start (σ_inv p) := by
          have := h_reach_bwd (σ start) p h_reach
          rw [h_cancel_inv] at this; exact this
      refine ⟨σ_inv p, ?_, by simp only [h_cancel]⟩
      cases h_lc : s.layerCount with
      | zero =>
          exfalso
          unfold structuralClusterList at hp
          rw [structuralBfs_eq_generic, h_allValid_σ, h_layerCount_σ] at hp
          simp only [h_lc, Nat.zero_mul, Nat.mul_zero, genericBfs, List.not_mem_nil] at hp
      | succ n =>
          exact (any_beq_iff_mem _ _).mp
              (structuralClusterList_complete s start (σ_inv p) (by omega) h_back)
    · rintro ⟨q, hq, rfl⟩
      have h_reach := structuralClusterList_sound s start q
          ((any_beq_iff_mem _ _).mpr hq)
      have h_σ := h_reach_fwd start q h_reach
      cases h_lc : s.layerCount with
      | zero =>
          exfalso
          unfold structuralClusterList at hq
          rw [structuralBfs_eq_generic] at hq
          simp only [h_lc, Nat.zero_mul, Nat.mul_zero, genericBfs, List.not_mem_nil] at hq
      | succ n =>
          exact (any_beq_iff_mem _ _).mp
              (structuralClusterList_complete σ_shape (σ start) (σ q)
                  (by rw [h_layerCount_σ]; omega) h_σ)

/-- structuralCluster のメンバーシップ等変性（汎用版） -/
theorem mem_structuralCluster_σ (s : Shape) (start p : QuarterPos)
        (σ : QuarterPos → QuarterPos) (σ_inv : QuarterPos → QuarterPos)
        (σ_shape : Shape)
        (h_cancel_inv : ∀ p, σ_inv (σ p) = p)
        (h_sc : structuralCluster σ_shape (σ start) = (structuralCluster s start).image σ) :
        p ∈ structuralCluster s start ↔
        σ p ∈ structuralCluster σ_shape (σ start) := by
    rw [h_sc, Finset.mem_image]
    constructor
    · exact fun h => ⟨p, h, rfl⟩
    · rintro ⟨q, hq, hqe⟩
      have := congr_arg σ_inv hqe
      simp only [h_cancel_inv] at this
      exact this ▸ hq

-- ============================================================
-- Finset 等変性の汎用版 (σ 版)
-- structuralCluster / groundedPositions / floatingUnits_isEmpty
-- ============================================================

/-- structuralCluster の rotate180 等変性（Finset.image 形式）。
    structuralCluster_σ の rotate180 インスタンス。 -/
theorem structuralCluster_rotate180 (s : Shape) (start : QuarterPos) :
        structuralCluster s.rotate180 start.rotate180 =
        (structuralCluster s start).image QuarterPos.rotate180 :=
    structuralCluster_σ s start QuarterPos.rotate180 QuarterPos.rotate180 s.rotate180
        (structuralReachable_rotate180 s)
        (fun p q h => by
            have := structuralReachable_rotate180 s.rotate180 p q h
            simp only [Shape.rotate180_rotate180] at this
            exact this)
        QuarterPos.rotate180_rotate180
        QuarterPos.rotate180_rotate180
        (CrystalBond.allValid_rotate180 s)
        (Shape.layerCount_rotate180 s)

/-- structuralCluster の rotateCW 等変性（Finset.image 形式）。
    structuralCluster_σ の rotateCW インスタンス。 -/
theorem structuralCluster_rotateCW (s : Shape) (start : QuarterPos) :
        structuralCluster s.rotateCW start.rotateCW =
        (structuralCluster s start).image QuarterPos.rotateCW :=
    structuralCluster_σ s start QuarterPos.rotateCW QuarterPos.rotateCCW s.rotateCW
        (fun p q h => h.rec .refl (fun h_bond _ ih =>
            .step (isStructurallyBonded_rotateCW s _ _ ▸ h_bond) ih))
        (fun p q h => by
            induction h with
            | refl => exact .refl
            | @step a b c h_bond _ ih =>
                have : isStructurallyBonded s a.rotateCCW b.rotateCCW = true := by
                    have h_eq := isStructurallyBonded_rotateCW s a.rotateCCW b.rotateCCW
                    simp only [QuarterPos.rotateCCW_rotateCW] at h_eq
                    rw [← h_eq]; exact h_bond
                exact .step this ih)
        QuarterPos.rotateCCW_rotateCW
        QuarterPos.rotateCW_rotateCCW
        (CrystalBond.allValid_rotateCW s)
        (Shape.layerCount_rotateCW s)

/-- structuralCluster のメンバーシップは rotate180 で保存される -/
theorem mem_structuralCluster_rotate180 (s : Shape) (start p : QuarterPos) :
        p ∈ structuralCluster s start ↔
        p.rotate180 ∈ structuralCluster s.rotate180 start.rotate180 :=
    mem_structuralCluster_σ s start p QuarterPos.rotate180 QuarterPos.rotate180 s.rotate180
        QuarterPos.rotate180_rotate180 (structuralCluster_rotate180 s start)

/-- structuralCluster のメンバーシップは rotateCW で保存される -/
theorem mem_structuralCluster_rotateCW (s : Shape) (start p : QuarterPos) :
        p ∈ structuralCluster s start ↔
        p.rotateCW ∈ structuralCluster s.rotateCW start.rotateCW :=
    mem_structuralCluster_σ s start p QuarterPos.rotateCW QuarterPos.rotateCCW s.rotateCW
        QuarterPos.rotateCW_rotateCCW (structuralCluster_rotateCW s start)

/-- groundedPositions の σ 等変性（汎用版）。
    σ / σ_inv が groundingEdge 到達可能性を双方向保存し、
    grounding seed 条件を双方向転送できれば、groundedPositions は Finset.image で等変。 -/
theorem groundedPositions_σ (s : Shape)
        (σ : QuarterPos → QuarterPos) (σ_inv : QuarterPos → QuarterPos)
        (σ_shape : Shape)
        (h_ge_reach_fwd : ∀ p q, GenericReachable (groundingEdge s) p q →
            GenericReachable (groundingEdge σ_shape) (σ p) (σ q))
        (h_ge_reach_bwd : ∀ p q, GenericReachable (groundingEdge σ_shape) p q →
            GenericReachable (groundingEdge s) (σ_inv p) (σ_inv q))
        (h_cancel : ∀ p, σ (σ_inv p) = p)
        (h_seed_fwd : ∀ seed,
            seed ∈ (QuarterPos.allValid s).filter (fun q =>
                q.layer == 0 && match q.getQuarter s with
                | some q => !q.isEmpty | none => false) →
            σ seed ∈ (QuarterPos.allValid σ_shape).filter (fun q =>
                q.layer == 0 && match q.getQuarter σ_shape with
                | some q => !q.isEmpty | none => false))
        (h_seed_bwd : ∀ seed,
            seed ∈ (QuarterPos.allValid σ_shape).filter (fun q =>
                q.layer == 0 && match q.getQuarter σ_shape with
                | some q => !q.isEmpty | none => false) →
            σ_inv seed ∈ (QuarterPos.allValid s).filter (fun q =>
                q.layer == 0 && match q.getQuarter s with
                | some q => !q.isEmpty | none => false)) :
        groundedPositions σ_shape = (groundedPositions s).image σ := by
    ext p
    simp only [groundedPositions, Finset.mem_image, List.mem_toFinset]
    constructor
    · intro hp
      have h_any := (any_beq_iff_mem _ _).mpr hp
      obtain ⟨seed', h_seed', h_reach'⟩ := groundedPositionsList_sound σ_shape p h_any
      have h_reach_back := h_ge_reach_bwd seed' p h_reach'
      have h_seed_valid := h_seed_bwd seed' h_seed'
      refine ⟨σ_inv p, ?_, by simp only [h_cancel]⟩
      exact (any_beq_iff_mem _ _).mp
          (groundedPositionsList_complete s (σ_inv seed') (σ_inv p)
              h_seed_valid h_reach_back)
    · rintro ⟨q, hq, rfl⟩
      have h_any := (any_beq_iff_mem _ _).mpr hq
      obtain ⟨seed, h_seed, h_reach⟩ := groundedPositionsList_sound s q h_any
      have h_reach_σ := h_ge_reach_fwd seed q h_reach
      have h_seed_σ := h_seed_fwd seed h_seed
      exact (any_beq_iff_mem _ _).mp
          (groundedPositionsList_complete σ_shape (σ seed) (σ q)
              h_seed_σ h_reach_σ)

/-- groundedPositions のメンバーシップ等変性（汎用版） -/
theorem mem_groundedPositions_σ (s : Shape) (p : QuarterPos)
        (σ : QuarterPos → QuarterPos) (σ_inv : QuarterPos → QuarterPos)
        (σ_shape : Shape)
        (h_cancel_inv : ∀ q, σ_inv (σ q) = q)
        (h_gp : groundedPositions σ_shape = (groundedPositions s).image σ) :
        p ∈ groundedPositions s ↔ σ p ∈ groundedPositions σ_shape := by
    rw [h_gp, Finset.mem_image]
    constructor
    · exact fun h => ⟨p, h, rfl⟩
    · rintro ⟨q, hq, hqe⟩
      have := congr_arg σ_inv hqe
      simp only [h_cancel_inv] at this
      exact this ▸ hq

/-- groundedPositions の rotate180 等変性（Finset.image 形式） -/
theorem groundedPositions_rotate180 (s : Shape) :
        groundedPositions s.rotate180 =
        (groundedPositions s).image QuarterPos.rotate180 :=
    groundedPositions_σ s QuarterPos.rotate180 QuarterPos.rotate180 s.rotate180
        (groundingEdgeReachable_rotate180 s)
        (fun p q h => by
            have := groundingEdgeReachable_rotate180 s.rotate180 p q h
            simp only [Shape.rotate180_rotate180] at this
            exact this)
        QuarterPos.rotate180_rotate180
        (fun seed h => by
            rw [CrystalBond.allValid_rotate180 s]
            exact grounding_seed_to_rotate180 s seed h)
        (fun seed h => grounding_seed_rotate180 s seed
            (CrystalBond.allValid_rotate180 s ▸ h))

/-- groundedPositions のメンバーシップは rotate180 で保存される -/
theorem mem_groundedPositions_rotate180 (s : Shape) (p : QuarterPos) :
        p ∈ groundedPositions s ↔
        p.rotate180 ∈ groundedPositions s.rotate180 :=
    mem_groundedPositions_σ s p QuarterPos.rotate180 QuarterPos.rotate180 s.rotate180
        QuarterPos.rotate180_rotate180 (groundedPositions_rotate180 s)

/-- floatingUnits の isEmpty は σ 変換で不変（汎用版） -/
theorem floatingUnits_isEmpty_σ (s σ_shape : Shape)
        (h_fwd : (floatingUnits s).isEmpty = false → (floatingUnits σ_shape).isEmpty = false)
        (h_bwd : (floatingUnits σ_shape).isEmpty = false → (floatingUnits s).isEmpty = false) :
        (floatingUnits s).isEmpty = (floatingUnits σ_shape).isEmpty := by
    cases h : (floatingUnits s).isEmpty <;>
        cases h' : (floatingUnits σ_shape).isEmpty
    · rfl
    · exact absurd (h_fwd (by rw [h])) (by rw [h']; decide)
    · exact absurd (h_bwd h') (by rw [h]; decide)
    · rfl

-- ============================================================
-- floatingUnits_isEmpty のヘルパー補題群
-- ============================================================

/-- 接地接触は対称的である -/
theorem isGroundingContact_symm (s : Shape) (p1 p2 : QuarterPos) :
        isGroundingContact s p1 p2 = isGroundingContact s p2 p1 := by
    simp only [isGroundingContact]
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
                Direction.adjacent_symm p1.dir p2.dir]
            -- match 式は cross-file unfold で内部表現が異なるため、直接 cases で解決
            cases v1 <;> cases v2 <;> rfl

/-- GenericReachable の推移律 -/
theorem genericReachable_trans {edge : α → α → Bool}
        (h1 : GenericReachable edge a b) (h2 : GenericReachable edge b c) :
        GenericReachable edge a c := by
    induction h1 with
    | refl => exact h2
    | step h_bond _ ih => exact .step h_bond (ih h2)

/-- 対称エッジでの GenericReachable 逆転 -/
theorem genericReachable_reverse {edge : α → α → Bool}
        (h_symm : ∀ x y, edge x y = edge y x)
        (h : GenericReachable edge a b) :
        GenericReachable edge b a := by
    induction h with
    | refl => exact .refl
    | step h_bond _ ih =>
        exact genericReachable_trans ih (.step (h_symm _ _ ▸ h_bond) .refl)

/-- エッジ述語の包含による GenericReachable の単調性 -/
theorem genericReachable_mono {edge1 edge2 : α → α → Bool}
        (h_sub : ∀ a b, edge1 a b = true → edge2 a b = true)
        (h : GenericReachable edge1 a b) :
        GenericReachable edge2 a b := by
    induction h with
    | refl => exact .refl
    | step h_bond _ ih => exact .step (h_sub _ _ h_bond) ih

/-- groundedPositionsList の BFS 不変条件 -/
theorem groundedPositionsList_inv (s : Shape) :
        GenericBfsInv (groundingEdge s) (QuarterPos.allValid s)
            (groundedPositionsList s) [] := by
    -- 定義を展開するが、rfl 経由で明示的な形式を維持し内部表現の不一致を回避
    have h_def : groundedPositionsList s =
        let allPos := QuarterPos.allValid s
        let seeds := allPos.filter fun p =>
            p.layer == 0 && match p.getQuarter s with | some q => !q.isEmpty | none => false
        let n := s.layerCount * 4
        groundingBfs s allPos [] seeds (n * n + n) := rfl
    rw [h_def]; dsimp only []
    rw [groundingBfs_eq_generic]
    apply genericBfs_invariant_preserved
    · intro v hv; simp only [List.any, Bool.false_eq_true] at hv
    · have h_filter : (QuarterPos.allValid s).filter (fun p =>
          !(([] : List QuarterPos).any (· == p))) = QuarterPos.allValid s :=
          List.filter_eq_self.mpr (by intro x _; simp only [List.any, Bool.not_false])
      simp only [h_filter, allValid_length']
      have := List.length_filter_le (fun p =>
          p.layer == 0 && match p.getQuarter s with
          | some q => !q.isEmpty | none => false) (QuarterPos.allValid s)
      rw [allValid_length' s] at this; omega
    · intro p q h
      exact (allValid_any_iff_layer' s p).mpr
          (isGroundingContact_valid_fst s p q
              (groundingEdge_base h))

/-- allStructuralClustersList は全ての bondable 位置をカバーする -/
theorem allStructuralClustersList_covers (s : Shape) (p : QuarterPos)
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
theorem allStructuralClustersList_is_structuralClusterList (s : Shape) (c : List QuarterPos)
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
          | none => simp only [hq, Bool.false_eq_true] at h_bond
          | some q =>
              cases q with
              | empty => simp only [hq, Quarter.canFormBond, Bool.false_eq_true] at h_bond
              | pin => simp only [hq, Quarter.canFormBond, Bool.false_eq_true] at h_bond
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
theorem allStructuralClustersList_disjoint (s : Shape)
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
      exact this _ [] (fun _ hk => absurd hk (by simp only [List.length, Nat.not_lt_zero, not_false_eq_true])) (fun _ _ ha => absurd ha (by simp only [List.length, Nat.not_lt_zero, not_false_eq_true]))
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
            exact ⟨pos, by simp only [Nat.sub_self, List.getElem_cons_zero], h_pos_layer⟩
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
private theorem floatingUnits_isEmpty_false_of_exists_mem (s : Shape)
        (h_exists : ∃ u, u ∈ floatingUnits s) :
        (floatingUnits s).isEmpty = false := by
    obtain ⟨u, hu⟩ := h_exists
    cases hl : floatingUnits s with
    | nil => rw [hl] at hu; nomatch hu
    | cons _ _ => rfl

private theorem ungrounded_nonempty_implies_floatingUnits_nonempty_pinCase
        (s : Shape) (p : QuarterPos)
        (h_p_allValid : p ∈ QuarterPos.allValid s)
    (h_is_pin : p.getQuarter s = some .pin)
        (h_ug_bool : (groundedPositionsList s).any (· == p) = false) :
        ∃ u, u ∈ floatingUnits s := by
    exact ⟨.pin p, by
        unfold floatingUnits
        simp_rw [decide_not_mem_groundedPositions]
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨p, List.mem_filter.mpr
            ⟨by unfold allIsolatedPins
                exact List.mem_filter.mpr ⟨h_p_allValid, by simp [h_is_pin]⟩,
                by simp only [h_ug_bool, Bool.not_false]⟩, rfl⟩⟩

private theorem ungrounded_nonempty_implies_floatingUnits_nonempty_bondCase
        (s : Shape) (p : QuarterPos)
        (h_valid : p.layer < s.layerCount)
        (h_bondable : match p.getQuarter s with
            | some q => q.canFormBond = true
            | none => False)
        (h_ug_bool : (groundedPositionsList s).any (· == p) = false) :
        ∃ u, u ∈ floatingUnits s := by
    have h_covers := allStructuralClustersList_covers s p h_valid h_bondable
    rw [List.any_eq_true] at h_covers
    obtain ⟨c, hc_mem, hc_has_p⟩ := h_covers
    obtain ⟨pos, hc_is_sc, _, _⟩ :=
        allStructuralClustersList_is_structuralClusterList s c hc_mem
    have h_all_ug : c.all
            (fun x => !((groundedPositionsList s).any (· == x))) = true := by
        rw [List.all_eq_true]
        intro x hx
        cases h_x_ground : (groundedPositionsList s).any (· == x) with
        | false => rfl
        | true =>
            exfalso
            have h_x_in_sc : (structuralClusterList s pos).any (· == x) = true := by
                rw [← hc_is_sc]; exact List.any_eq_true.mpr ⟨x, hx, BEq.rfl⟩
            have h_p_in_sc := hc_is_sc ▸ hc_has_p
            have h_reach_pos_x := structuralClusterList_sound s pos x h_x_in_sc
            have h_reach_pos_p := structuralClusterList_sound s pos p h_p_in_sc
            have h_reach_x_pos := genericReachable_reverse
                (fun a b => isStructurallyBonded_symm s a b) h_reach_pos_x
            have h_reach_x_p :=
                genericReachable_trans h_reach_x_pos h_reach_pos_p
            have h_reach_ge := h_reach_x_p.mono
                (fun _ _ h => groundingEdge_of_isStructurallyBonded h)
            have h_p_ground := groundedPositionsList_closed s x p
                h_x_ground h_reach_ge
            rw [h_ug_bool] at h_p_ground
            exact absurd h_p_ground (by decide)
    exact ⟨.cluster c, by
        unfold floatingUnits
        simp_rw [decide_not_mem_groundedPositions]
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc_mem, h_all_ug⟩, rfl⟩⟩

theorem ungrounded_nonempty_implies_floatingUnits_nonempty (s : Shape) (p : QuarterPos)
        (h_valid : p.layer < s.layerCount)
        (h_ne : ∃ q, p.getQuarter s = some q ∧ !q.isEmpty = true)
        (h_ug : p ∉ groundedPositions s) :
        (floatingUnits s).isEmpty = false := by
    have h_ug_bool := (not_mem_groundedPositions_iff s p).mp h_ug
    obtain ⟨q, hq_some, hq_ne⟩ := h_ne
    -- 非空象限はピンか結合可能のいずれか
    have h_cases : q = .pin ∨ q.canFormBond = true := by
        cases q with
        | empty => simp only [Quarter.isEmpty, decide_true, Bool.not_true, Bool.false_eq_true] at hq_ne
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
    have h_exists : ∃ u, u ∈ floatingUnits s := by
        cases h_cases with
        | inl h_pin =>
            subst h_pin
            exact ungrounded_nonempty_implies_floatingUnits_nonempty_pinCase
                s p h_p_allValid (by simp [hq_some]) h_ug_bool
        | inr h_bond =>
            have h_bondable : match p.getQuarter s with
                    | some q => q.canFormBond = true | none => False := by
                rw [hq_some]; exact h_bond
            exact ungrounded_nonempty_implies_floatingUnits_nonempty_bondCase
                s p h_valid h_bondable h_ug_bool
    exact floatingUnits_isEmpty_false_of_exists_mem s h_exists

/-- floatingUnits が非空なら非空かつ非接地の位置が存在する -/
theorem floatingUnits_nonempty_implies_exists_ungrounded (s : Shape)
        (h : (floatingUnits s).isEmpty = false) :
        ∃ p : QuarterPos, p.layer < s.layerCount ∧
            (∃ q, p.getQuarter s = some q ∧ !q.isEmpty = true) ∧
            p ∉ groundedPositions s := by
    -- floatingUnits s が非空なので要素を取得
    obtain ⟨u, hu_mem⟩ : ∃ u, u ∈ floatingUnits s := by
        cases hfl : floatingUnits s with
        | nil => rw [hfl] at h; simp only [List.isEmpty_nil, Bool.true_eq_false] at h
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
            revert this; cases (groundedPositionsList s).any (· == pos) <;> simp only [Bool.not_false, imp_self, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false]
        -- pos は非空（canFormBond → not empty）
        have h_pos_ne : !q_pos.isEmpty = true := by
            cases q_pos <;> simp only [Quarter.canFormBond, Bool.false_eq_true] at h_pos_bond
                <;> simp only [Quarter.isEmpty, Bool.false_eq_true, decide_false, Bool.not_false]
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
            | none => simp only [hq, Bool.false_eq_true] at hp'_is_pin
            | some q =>
                cases q <;> simp_all only [List.isEmpty_eq_false_iff, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false, beq_iff_eq, Bool.false_eq_true, Option.some.injEq, Quarter.isEmpty, Bool.decide_eq_true, exists_eq_left']
        -- p' は非接地
        have h_p'_ug : (groundedPositionsList s).any (· == p') = false := by
            revert hp'_ug; cases (groundedPositionsList s).any (· == p') <;> simp only [Bool.not_false, imp_self, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false]
        exact ⟨p', h_p'_valid, h_p'_ne,
            (not_mem_groundedPositions_iff s p').mpr h_p'_ug⟩

/-- floatingUnits 非空ならば σ 変換後も非空（汎用版） -/
theorem floatingUnits_nonempty_implies_σ_nonempty (s : Shape)
        (σ_qpos : QuarterPos → QuarterPos) (σ_shape : Shape)
        (h_lc : σ_shape.layerCount = s.layerCount)
        (h_layer : ∀ p, (σ_qpos p).layer = p.layer)
        (h_gq : ∀ p, (σ_qpos p).getQuarter σ_shape = p.getQuarter s)
        (h_gp : ∀ p, p ∈ groundedPositions s ↔ σ_qpos p ∈ groundedPositions σ_shape)
        (h : (floatingUnits s).isEmpty = false) :
        (floatingUnits σ_shape).isEmpty = false := by
    obtain ⟨p, h_valid, ⟨q, hq, h_ne⟩, h_ug⟩ :=
        floatingUnits_nonempty_implies_exists_ungrounded s h
    apply ungrounded_nonempty_implies_floatingUnits_nonempty σ_shape (σ_qpos p)
    · rw [h_layer, h_lc]; exact h_valid
    · exact ⟨q, by rw [h_gq]; exact hq, h_ne⟩
    · exact fun h => h_ug ((h_gp p).mpr h)

/-- floatingUnits が非空なら s.rotate180 でも非空 -/
theorem floatingUnits_nonempty_implies_rotate180_nonempty (s : Shape)
        (h : (floatingUnits s).isEmpty = false) :
        (floatingUnits s.rotate180).isEmpty = false :=
    floatingUnits_nonempty_implies_σ_nonempty s QuarterPos.rotate180 s.rotate180
        (Shape.layerCount_rotate180 s) (fun _ => rfl) (fun _ => getQuarter_rotate180 s _)
        (fun p => mem_groundedPositions_rotate180 s p) h

/-- floatingUnits の isEmpty は rotate180 で不変 -/
theorem floatingUnits_isEmpty_rotate180 (s : Shape) :
        (floatingUnits s).isEmpty = (floatingUnits s.rotate180).isEmpty :=
    floatingUnits_isEmpty_σ s s.rotate180
        (floatingUnits_nonempty_implies_rotate180_nonempty s)
        (fun h => by
            have := floatingUnits_nonempty_implies_rotate180_nonempty s.rotate180 h
            rw [Shape.rotate180_rotate180] at this; exact this)

-- ============================================================
-- rotateCW 等変性チェーン
-- ============================================================

/-- isGroundingContact は rotateCW で不変 -/
theorem isGroundingContact_rotateCW (s : Shape) (p1 p2 : QuarterPos) :
        isGroundingContact (s.rotateCW) (p1.rotateCW) (p2.rotateCW) =
        isGroundingContact s p1 p2 := by
    simp only [isGroundingContact, QuarterPos.getQuarter_rotateCW]
    simp only [QuarterPos.rotateCW, Direction.adjacent_rotateCW]
    cases h1 : p1.getQuarter s <;> cases h2 : p2.getQuarter s <;> try rfl
    rename_i q1 q2
    cases q1 <;> cases q2 <;> simp only [Quarter.isEmpty] <;> (try rfl) <;>
    simp only [Bool.not_false, Bool.true_and] <;>
    congr 1 <;> cases p1.dir <;> cases p2.dir <;> rfl

/-- isUpwardGroundingContact は rotateCW で不変（レイヤが変わらないため） -/
theorem isUpwardGroundingContact_rotateCW (s : Shape) (p1 p2 : QuarterPos) :
        isUpwardGroundingContact (s.rotateCW) (p1.rotateCW) (p2.rotateCW) =
        isUpwardGroundingContact s p1 p2 := by
    unfold isUpwardGroundingContact
    rw [isGroundingContact_rotateCW]
    congr 1

/-- groundingEdge は rotateCW で不変 -/
theorem groundingEdge_rotateCW (s : Shape) (p1 p2 : QuarterPos) :
        groundingEdge (s.rotateCW) (p1.rotateCW) (p2.rotateCW) =
        groundingEdge s p1 p2 := by
    simp only [groundingEdge, isUpwardGroundingContact_rotateCW,
        isStructurallyBonded_rotateCW]

/-- groundingBfs は rotateCW で等変（genericBfs_map_comm より導出） -/
theorem groundingBfs_rotateCW (s : Shape)
        (allPos visited queue : List QuarterPos) (fuel : Nat) :
        groundingBfs s.rotateCW
            (allPos.map QuarterPos.rotateCW)
            (visited.map QuarterPos.rotateCW)
            (queue.map QuarterPos.rotateCW) fuel =
        (groundingBfs s allPos visited queue fuel).map QuarterPos.rotateCW := by
    simp only [groundingBfs_eq_generic]
    exact genericBfs_map_comm
        (groundingEdge s) (groundingEdge s.rotateCW) QuarterPos.rotateCW
        (fun a b => groundingEdge_rotateCW s a b)
        σ_rCW.quarterPos_beq allPos visited queue fuel

/-- allValid は rotateCW で不変 -/
theorem allValid_rotateCW (s : Shape) :
        QuarterPos.allValid s.rotateCW = QuarterPos.allValid s := by
    unfold QuarterPos.allValid; simp only [Shape.layerCount_rotateCW]

/-- groundedPositionsList の rotateCW 等変性 -/
theorem groundedPositionsList_rotateCW_mapped (s : Shape) :
        let allPos := QuarterPos.allValid s
        let seeds := allPos.filter fun p =>
            p.layer == 0 &&
            match p.getQuarter s with
            | some q => !q.isEmpty | none => false
        groundingBfs s.rotateCW
            (allPos.map QuarterPos.rotateCW)
            []
            (seeds.map QuarterPos.rotateCW)
            (s.layerCount * 4 * (s.layerCount * 4) + s.layerCount * 4) =
        (groundedPositionsList s).map QuarterPos.rotateCW := by
    unfold groundedPositionsList
    exact groundingBfs_rotateCW s (QuarterPos.allValid s) []
        ((QuarterPos.allValid s).filter fun p =>
            p.layer == 0 &&
            match p.getQuarter s with
            | some q => !q.isEmpty
            | none   => false)
        (s.layerCount * 4 * (s.layerCount * 4) + s.layerCount * 4)

/-- grounding seed の rotateCW 変換 -/
theorem grounding_seed_to_rotateCW (s : Shape) (seed : QuarterPos)
        (h_seed : seed ∈ (QuarterPos.allValid s).filter (fun q =>
            q.layer == 0 && match q.getQuarter s with
            | some q => !q.isEmpty | none => false)) :
        seed.rotateCW ∈ (QuarterPos.allValid s.rotateCW).filter (fun q =>
            q.layer == 0 && match q.getQuarter s.rotateCW with
            | some q => !q.isEmpty | none => false) := by
    rw [allValid_rotateCW]
    have ⟨h_allValid, h_pred⟩ := List.mem_filter.mp h_seed
    have h_layer : seed.layer < s.layerCount :=
        (allValid_any_iff_layer' s seed).mp
            (List.any_eq_true.mpr ⟨seed, h_allValid, BEq.rfl⟩)
    have h_cw_allValid : seed.rotateCW ∈ QuarterPos.allValid s := by
        have h_any := (allValid_any_iff_layer' s seed.rotateCW).mpr h_layer
        rw [List.any_eq_true] at h_any
        obtain ⟨y, hy, hye⟩ := h_any; exact eq_of_beq hye ▸ hy
    exact List.mem_filter.mpr ⟨h_cw_allValid, by
        simp only [QuarterPos.getQuarter_rotateCW]; exact h_pred⟩

/-- grounding seed の逆 rotateCW 変換 -/
theorem grounding_seed_from_rotateCW (s : Shape) (seed : QuarterPos)
        (h_seed : seed ∈ (QuarterPos.allValid s.rotateCW).filter (fun q =>
            q.layer == 0 && match q.getQuarter s.rotateCW with
            | some q => !q.isEmpty | none => false)) :
        seed.rotateCCW ∈ (QuarterPos.allValid s).filter (fun q =>
            q.layer == 0 && match q.getQuarter s with
            | some q => !q.isEmpty | none => false) := by
    rw [allValid_rotateCW] at h_seed
    have ⟨h_allValid, h_pred⟩ := List.mem_filter.mp h_seed
    have h_layer : seed.layer < s.layerCount :=
        (allValid_any_iff_layer' s seed).mp
            (List.any_eq_true.mpr ⟨seed, h_allValid, BEq.rfl⟩)
    have h_ccw_allValid : seed.rotateCCW ∈ QuarterPos.allValid s := by
        have h_any := (allValid_any_iff_layer' s seed.rotateCCW).mpr h_layer
        rw [List.any_eq_true] at h_any
        obtain ⟨y, hy, hye⟩ := h_any; exact eq_of_beq hye ▸ hy
    exact List.mem_filter.mpr ⟨h_ccw_allValid, by
        simp only [← QuarterPos.getQuarter_rotateCW_inv]; exact h_pred⟩

/-- 上方向接地接触到達可能性は rotateCW で保存される -/
theorem upwardGroundingReachable_rotateCW (s : Shape) (p q : QuarterPos)
        (h : GenericReachable (isUpwardGroundingContact s) p q) :
        GenericReachable (isUpwardGroundingContact s.rotateCW) p.rotateCW q.rotateCW := by
    induction h with
    | refl => exact .refl
    | step h_bond _ ih =>
        exact .step (isUpwardGroundingContact_rotateCW s _ _ ▸ h_bond) ih

/-- groundingEdge 到達可能性は rotateCW で保存される -/
theorem groundingEdgeReachable_rotateCW (s : Shape) (p q : QuarterPos)
        (h : GenericReachable (groundingEdge s) p q) :
        GenericReachable (groundingEdge s.rotateCW) p.rotateCW q.rotateCW := by
    induction h with
    | refl => exact .refl
    | step h_bond _ ih =>
        exact .step (groundingEdge_rotateCW s _ _ ▸ h_bond) ih

/-- 上方向接地接触到達可能性は rotateCW 逆方向でも保存される -/
theorem upwardGroundingReachable_from_rotateCW (s : Shape) (p q : QuarterPos)
        (h : GenericReachable (isUpwardGroundingContact s.rotateCW) p q) :
        GenericReachable (isUpwardGroundingContact s) p.rotateCCW q.rotateCCW := by
    induction h with
    | refl => exact .refl
    | @step a b c h_bond _ ih =>
        have : isUpwardGroundingContact s a.rotateCCW b.rotateCCW = true := by
            have h_eq := isUpwardGroundingContact_rotateCW s a.rotateCCW b.rotateCCW
            simp only [QuarterPos.rotateCCW_rotateCW] at h_eq
            rw [← h_eq]; exact h_bond
        exact .step this ih

/-- groundingEdge 到達可能性は rotateCW 逆方向でも保存される -/
theorem groundingEdgeReachable_from_rotateCW (s : Shape) (p q : QuarterPos)
        (h : GenericReachable (groundingEdge s.rotateCW) p q) :
        GenericReachable (groundingEdge s) p.rotateCCW q.rotateCCW := by
    induction h with
    | refl => exact .refl
    | @step a b c h_bond _ ih =>
        have : groundingEdge s a.rotateCCW b.rotateCCW = true := by
            have h_eq := groundingEdge_rotateCW s a.rotateCCW b.rotateCCW
            simp only [QuarterPos.rotateCCW_rotateCW] at h_eq
            rw [← h_eq]; exact h_bond
        exact .step this ih

/-- groundedPositions は rotateCW で等変（Finset レベル）。
    groundedPositions_σ の rotateCW インスタンス。 -/
theorem groundedPositions_rotateCW (s : Shape) :
        groundedPositions s.rotateCW =
        (groundedPositions s).image QuarterPos.rotateCW :=
    groundedPositions_σ s QuarterPos.rotateCW QuarterPos.rotateCCW s.rotateCW
        (groundingEdgeReachable_rotateCW s)
        (groundingEdgeReachable_from_rotateCW s)
        QuarterPos.rotateCCW_rotateCW
        (grounding_seed_to_rotateCW s)
        (grounding_seed_from_rotateCW s)

/-- groundedPositions のメンバーシップは rotateCW で保存される -/
theorem mem_groundedPositions_rotateCW (s : Shape) (p : QuarterPos) :
        p ∈ groundedPositions s ↔
        p.rotateCW ∈ groundedPositions s.rotateCW :=
    mem_groundedPositions_σ s p QuarterPos.rotateCW QuarterPos.rotateCCW s.rotateCW
        QuarterPos.rotateCW_rotateCCW (groundedPositions_rotateCW s)

/-- floatingUnits 非空ならば rotateCW でも非空 -/
theorem floatingUnits_nonempty_implies_rotateCW_nonempty (s : Shape)
        (h : (floatingUnits s).isEmpty = false) :
        (floatingUnits s.rotateCW).isEmpty = false :=
    floatingUnits_nonempty_implies_σ_nonempty s QuarterPos.rotateCW s.rotateCW
        (Shape.layerCount_rotateCW s) (fun _ => rfl) (fun _ => QuarterPos.getQuarter_rotateCW s _)
        (fun p => mem_groundedPositions_rotateCW s p) h

/-- floatingUnits の isEmpty は rotateCW で不変 -/
theorem floatingUnits_isEmpty_rotateCW (s : Shape) :
        (floatingUnits s).isEmpty = (floatingUnits s.rotateCW).isEmpty :=
    floatingUnits_isEmpty_σ s s.rotateCW
        (floatingUnits_nonempty_implies_rotateCW_nonempty s)
        (fun h => by
            have h1 := floatingUnits_nonempty_implies_rotateCW_nonempty s.rotateCW h
            have h2 := floatingUnits_nonempty_implies_rotateCW_nonempty s.rotateCW.rotateCW h1
            have h3 := floatingUnits_nonempty_implies_rotateCW_nonempty
                s.rotateCW.rotateCW.rotateCW h2
            rw [Shape.rotateCW_four] at h3; exact h3)

/-- isOccupied は rotate180 で等変 -/
theorem isOccupied_rotate180 (obs : List Layer) (layer : Nat) (d : Direction) :
        isOccupied (obs.map Layer.rotate180) layer (d.rotate180) =
        isOccupied obs layer d := by
    simp only [isOccupied, List.getElem?_map]
    cases obs[layer]? with
    | none => rfl
    | some l => simp only [Option.map_some, getDir_rotate180]

/-- landed 判定 (positions.any) は rotate180 で不変 -/
theorem landed_rotate180 (positions : List QuarterPos) (obs : List Layer) (d : Nat) :
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
theorem landingDistance_check_rotate180 (positions : List QuarterPos) (obs : List Layer)
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
theorem landingDistance_rotate180 (u : FallingUnit) (obs : List Layer) :
        landingDistance u.rotate180 (obs.map Layer.rotate180) = landingDistance u obs := by
    simp only [landingDistance]
    simp only [FallingUnit.minLayer_rotate180, FallingUnit.positions_rotate180]
    exact landingDistance_check_rotate180 u.positions obs u.minLayer 1 (u.minLayer + 1)

/-- setDir と rotate180 の可換性（一般版） -/
theorem setDir_rotate180 (l : Layer) (d : Direction) (q : Quarter) :
        (QuarterPos.setDir l d q).rotate180 =
        QuarterPos.setDir (l.rotate180) (d.rotate180) q := by
    cases d <;> rfl

/-- replicate Layer.empty の map rotate180 -/
theorem replicate_empty_rotate180 (n : Nat) :
        (List.replicate n Layer.empty).map Layer.rotate180 = List.replicate n Layer.empty := by
    induction n with
    | zero => rfl
    | succ n ih =>
        show Layer.empty.rotate180 :: (List.replicate n Layer.empty).map Layer.rotate180 =
             Layer.empty :: List.replicate n Layer.empty
        rw [ih]
        rfl

/-- placeQuarter は rotate180 で等変 -/
theorem placeQuarter_rotate180 (layers : List Layer) (lay : Nat) (d : Direction) (q : Quarter) :
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
theorem placeFallingUnit_rotate180 (origShape : Shape) (obs : List Layer)
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
theorem flatMap_map_rotate180 (units : List FallingUnit) :
        (units.map FallingUnit.rotate180).flatMap FallingUnit.positions =
        (units.flatMap FallingUnit.positions).map QuarterPos.rotate180 := by
    induction units with
    | nil => rfl
    | cons u rest ih =>
        simp only [List.map_cons, List.flatMap_cons, List.map_append]
        rw [FallingUnit.positions_rotate180, ih]

/-- sorted.foldl (placeFallingUnit + landingDistance) の rotate180 等変性 -/
theorem foldl_place_rotate180 (s : Shape) (sorted : List FallingUnit) (obs : List Layer) :
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


end Gravity
