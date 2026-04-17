-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Behavior.Gravity.SettleFoldlEq_obsolated

namespace Gravity

open Shape (layers_rotate180 clearPositions_rotate180)

-- ============================================================
-- sort-foldl bridge 基盤: グループ毎のソート済み Perm foldl 等価性
-- fallingUnitOrd は r180 等変でないが、minLayer（1次キー）は保存される。
-- canonicalKey（2次キー）の変化は同一 minLayer グループ内の並び替えのみ生じ、
-- 同一グループ内の position-disjoint FU ペアは ≤5L で可換であるため bridge が成立。
-- ============================================================

/-- pre の全要素が a と可換なら、a をリスト先頭にバブルできる -/
private theorem foldl_bubble {α β : Type} (f : β → α → β)
    (pre : List α) (a : α) (suf : List α) (init : β)
    (h_comm : ∀ x ∈ pre, ∀ s, f (f s x) a = f (f s a) x) :
    (pre ++ a :: suf).foldl f init = (a :: pre ++ suf).foldl f init := by
  induction pre generalizing init with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.cons_append, List.foldl_cons]
    rw [ih (f init x) (fun y hy => h_comm y (.tail x hy))]
    simp only [List.cons_append, List.foldl_cons]
    congr 1
    exact h_comm x (.head rest) init

/-- pre ++ a :: suf が Pairwise R なら pre ++ suf も Pairwise R -/
private theorem pairwise_remove_mid {R : α → α → Prop}
    {pre : List α} {a : α} {suf : List α}
    (h : (pre ++ a :: suf).Pairwise R) :
    (pre ++ suf).Pairwise R :=
  h.sublist (List.Sublist.append_left (List.sublist_cons_self a suf) pre)

/-- ソート済みリストで、a の前にある要素 x は R x a を満たす -/
private theorem rel_of_mem_prefix {R : α → α → Prop}
    {pre : List α} {a : α} {suf : List α}
    (h : (pre ++ a :: suf).Pairwise R) {x : α} (hx : x ∈ pre) :
    R x a := by
  induction pre with
  | nil => exact (List.not_mem_nil hx).elim
  | cons y rest ih =>
    rw [List.cons_append] at h
    cases hx with
    | head => exact List.rel_of_pairwise_cons h (List.mem_append_right _ (.head _))
    | tail _ hm => exact ih h.of_cons hm

/-- グループ昇順でソートされた 2 リストが Perm で、グループ内可換 → foldl 等価 -/
private theorem foldl_perm_sorted_eq {α β : Type} [DecidableEq α]
    (f : β → α → β) (group : α → Nat) (l1 l2 : List α) (init : β)
    (h_perm : l1.Perm l2)
    (h_sorted1 : l1.Pairwise (fun a b => group a ≤ group b))
    (h_sorted2 : l2.Pairwise (fun a b => group a ≤ group b))
    (h_comm : ∀ a ∈ l1, ∀ b ∈ l1, group a = group b →
        ∀ s, f (f s a) b = f (f s b) a) :
    l1.foldl f init = l2.foldl f init := by
  induction l1 generalizing l2 init with
  | nil => have : l2 = [] := h_perm.symm.eq_nil; subst this; rfl
  | cons a rest1 ih =>
    obtain ⟨pre, suf, h_split⟩ := List.append_of_mem (h_perm.mem_iff.mp (.head _))
    subst h_split
    have h_pre_eq : ∀ x ∈ pre, group x = group a := by
      intro x hx
      have h_le := rel_of_mem_prefix h_sorted2 hx
      have hx_l1 := h_perm.mem_iff.mpr (List.mem_append_left _ hx)
      have h_ge : group a ≤ group x := by
        cases hx_l1 with
        | head => omega
        | tail _ h => exact List.rel_of_pairwise_cons h_sorted1 h
      omega
    rw [foldl_bubble f pre a suf init
      (fun x hx s => h_comm x (h_perm.mem_iff.mpr (List.mem_append_left _ hx))
        a (.head _) (h_pre_eq x hx) s)]
    simp only [List.foldl_cons]
    exact ih (pre ++ suf) (f init a)
      ((List.perm_cons a).mp (h_perm.trans List.perm_middle))
      h_sorted1.of_cons (pairwise_remove_mid h_sorted2)
      (fun x hx y hy hg s => h_comm x (.tail a hx) y (.tail a hy) hg s)

-- ============================================================
-- sort-foldl bridge: fallingUnitOrd ソート + r180 マッピングの等価性
-- ============================================================

/-- fallingUnitOrd a b = true → a.sortGroup ≤ b.sortGroup -/
private theorem fallingUnitOrd_sortGroup_le {a b : FallingUnit}
    (h : fallingUnitOrd a b = true) : a.sortGroup ≤ b.sortGroup := by
  have ha := a.typeOrd_le_one
  have hb := b.typeOrd_le_one
  simp only [FallingUnit.sortGroup, fallingUnitOrd] at *
  split at h
  · omega
  · split at h
    · simp only [Bool.false_eq_true] at h
    · split at h
      · omega
      · split at h
        · simp only [Bool.false_eq_true] at h
        · omega

/-- sortFallingUnits' の結果は sortGroup 昇順 -/
private theorem sortFallingUnits'_pairwise_sortGroup (l : List FallingUnit) :
    (sortFallingUnits' l).Pairwise (fun a b => a.sortGroup ≤ b.sortGroup) := by
  simp only [sortFallingUnits']
  exact (List.pairwise_mergeSort (le := fallingUnitOrd)
    (fun a b c hab hbc => fallingUnitOrd_trans hab hbc)
    fallingUnitOrd_total' l).imp (fun hab => fallingUnitOrd_sortGroup_le hab)

/-- 任意の sortGroup 保存マッピングが sortGroup ソート順を保存 -/
private theorem map_perm_pairwise_sortGroup (map_fu : FallingUnit → FallingUnit)
    (h_sortGroup : ∀ u, (map_fu u).sortGroup = u.sortGroup) (l : List FallingUnit) :
    ((sortFallingUnits' l).map map_fu).Pairwise
        (fun a b => a.sortGroup ≤ b.sortGroup) := by
  rw [List.pairwise_map]
  exact (sortFallingUnits'_pairwise_sortGroup l).imp
    (fun h => by rw [h_sortGroup, h_sortGroup]; exact h)

/-- sort-foldl bridge: (sort l).map f と sort(l.map f) の foldl は等しい（汎用版）。
    同一 sortGroup（= minLayer + typeOrd）内の可換性のみ必要。 -/
theorem sort_foldl_map_perm_bridge (s' : Shape)
    (map_fu : FallingUnit → FallingUnit)
    (h_sortGroup : ∀ u, (map_fu u).sortGroup = u.sortGroup)
    (units : List FallingUnit) (obs : List Layer)
    (h_comm : ∀ u ∈ (sortFallingUnits' units).map map_fu,
        ∀ v ∈ (sortFallingUnits' units).map map_fu,
        u.sortGroup = v.sortGroup →
        ∀ obs', (fun obs u => placeFallingUnit s' obs u (landingDistance u obs))
            ((fun obs u => placeFallingUnit s' obs u (landingDistance u obs)) obs' u) v =
          (fun obs u => placeFallingUnit s' obs u (landingDistance u obs))
            ((fun obs u => placeFallingUnit s' obs u (landingDistance u obs)) obs' v) u) :
    ((sortFallingUnits' units).map map_fu).foldl
        (fun obs u => placeFallingUnit s' obs u (landingDistance u obs)) obs =
    (sortFallingUnits' (units.map map_fu)).foldl
        (fun obs u => placeFallingUnit s' obs u (landingDistance u obs)) obs := by
  have h_perm : ((sortFallingUnits' units).map map_fu).Perm
      (sortFallingUnits' (units.map map_fu)) := by
    simp only [sortFallingUnits']
    exact ((List.mergeSort_perm units fallingUnitOrd).map _).trans
      (List.mergeSort_perm (units.map _) fallingUnitOrd).symm
  exact foldl_perm_sorted_eq
    (fun obs u => placeFallingUnit s' obs u (landingDistance u obs))
    FallingUnit.sortGroup
    _ _ obs h_perm
    (map_perm_pairwise_sortGroup map_fu h_sortGroup units)
    (sortFallingUnits'_pairwise_sortGroup (units.map map_fu))
    (fun u hu v hv hml obs' => h_comm u hu v hv hml obs')

-- ============================================================
-- クラスタペアの構造的性質
-- ============================================================

/-- 異なるクラスタ FU が同方角を共有する場合、レイヤは垂直隣接しない（gap ≥ 2） -/
private theorem cluster_same_dir_not_adj (s : Shape)
        (ps_u ps_v : List QuarterPos)
        (hu : FallingUnit.cluster ps_u ∈ floatingUnits s)
        (hv : FallingUnit.cluster ps_v ∈ floatingUnits s)
        (h_ne : FallingUnit.cluster ps_u ≠ FallingUnit.cluster ps_v)
        (p : QuarterPos) (hp : p ∈ ps_u)
        (q : QuarterPos) (hq : q ∈ ps_v)
        (h_dir : p.dir = q.dir) :
        LayerIndex.verticallyAdjacent p.layer q.layer = false := by
    by_contra h_adj
    rw [Bool.not_eq_false] at h_adj
    have h_u_all := floatingUnits_cluster_in_allStructuralClustersList s ps_u hu
    have h_v_all := floatingUnits_cluster_in_allStructuralClustersList s ps_v hv
    have ⟨vp, hvp, hvp_bond⟩ := allStructuralClustersList_all_bondable s ps_u h_u_all p
        (List.any_eq_true.mpr ⟨p, hp, BEq.rfl⟩)
    have ⟨vq, hvq, hvq_bond⟩ := allStructuralClustersList_all_bondable s ps_v h_v_all q
        (List.any_eq_true.mpr ⟨q, hq, BEq.rfl⟩)
    have h_bond : isStructurallyBonded s p q = true := by
        simp only [isStructurallyBonded, hvp, hvq, hvp_bond, hvq_bond, Bool.true_and]
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
        right; exact ⟨h_adj, h_dir⟩
    have h_reach : GenericReachable (isStructurallyBonded s) p q :=
        .step h_bond .refl
    have hq_in_u := genReachable_mem_cluster s ps_u h_u_all p q hp h_reach
    have h_disj := floatingUnits_elem_positions_disjoint s _ _ hu hv h_ne q hq_in_u
    simp only [FallingUnit.positions] at h_disj
    have h_mem : ps_v.any (· == q) = true := List.any_eq_true.mpr ⟨q, hq, BEq.rfl⟩
    simp only [h_disj] at h_mem
    exact Bool.noConfusion h_mem

-- ============================================================
-- settle foldl の同 sortGroup ペア可換性（rotation-generic 版）
-- ============================================================

/-- settle foldl で同 sortGroup のペアは可換（rotation-generic 版）。
    LayerPerm σ のもとで mapFU が positions/sortGroup/minLayer を保存すれば、
    foldl 内の同 sortGroup ペアの配置順序は可換。
    process_rotate180 / process_rotateCW の h_comm ブロックを統合する -/
theorem settleStep_comm_mapped_perm (s s_rot : Shape) (σ : LayerPerm)
        (mapFU : FallingUnit → FallingUnit)
        (h_layers : s.layerCount ≤ 5)
        (h_positions_pin : ∀ p, (mapFU (.pin p)).positions = [σ.onQPos p])
        (h_positions_cluster : ∀ ps, (mapFU (.cluster ps)).positions = ps.map σ.onQPos)
        (h_sortGroup : ∀ u, (mapFU u).sortGroup = u.sortGroup)
        (h_minLayer : ∀ u, (mapFU u).minLayer = u.minLayer)
        : ∀ u ∈ (sortFallingUnits' (floatingUnits s)).map mapFU,
          ∀ v ∈ (sortFallingUnits' (floatingUnits s)).map mapFU,
          u.sortGroup = v.sortGroup →
          ∀ obs', (fun obs u => placeFallingUnit s_rot obs u (landingDistance u obs))
              ((fun obs u => placeFallingUnit s_rot obs u (landingDistance u obs)) obs' u) v =
            (fun obs u => placeFallingUnit s_rot obs u (landingDistance u obs))
              ((fun obs u => placeFallingUnit s_rot obs u (landingDistance u obs)) obs' v) u := by
    intro u hu v hv h_sg obs'
    obtain ⟨u₀, hu₀_sorted, rfl⟩ := List.mem_map.mp hu
    obtain ⟨v₀, hv₀_sorted, rfl⟩ := List.mem_map.mp hv
    rw [h_sortGroup, h_sortGroup] at h_sg
    by_cases huv : u₀ = v₀
    · subst huv; rfl
    · have hu₀ : u₀ ∈ floatingUnits s :=
        (List.mergeSort_perm (floatingUnits s) fallingUnitOrd).mem_iff.mp hu₀_sorted
      have hv₀ : v₀ ∈ floatingUnits s :=
        (List.mergeSort_perm (floatingUnits s) fallingUnitOrd).mem_iff.mp hv₀_sorted
      obtain ⟨h_ml, h_type⟩ := FallingUnit.sortGroup_eq_iff.mp h_sg
      cases u₀ with
      | pin p =>
        cases v₀ with
        | pin q =>
          simp only [FallingUnit.minLayer, FallingUnit.positions, List.foldl] at h_ml
          have h_ne_pq : p ≠ q := fun h => huv (congrArg FallingUnit.pin h)
          have h_dir : p.dir ≠ q.dir := by
            intro h; exact h_ne_pq (by rcases p with ⟨lp, dp⟩; rcases q with ⟨lq, dq⟩; simp_all)
          have h_dir_r : (σ.onQPos p).dir ≠ (σ.onQPos q).dir := by
            rw [σ.qpos_dir, σ.qpos_dir]
            exact fun h => h_dir (σ.onDir_injective h)
          apply settleStep_comm_ne_dir
          · intro r hr
            rw [h_positions_pin] at hr
            simp only [List.mem_singleton] at hr
            subst hr
            rw [h_positions_pin]
            simp only [List.any_cons, List.any_nil, Bool.or_false]
            exact beq_false_of_ne (Ne.symm h_dir_r)
          · intro r hr
            rw [h_positions_pin] at hr
            simp only [List.mem_singleton] at hr
            subst hr
            rw [h_positions_pin]
            simp only [List.any_cons, List.any_nil, Bool.or_false]
            exact beq_false_of_ne h_dir_r
        | cluster ps_v =>
          simp only [FallingUnit.typeOrd] at h_type; omega
      | cluster ps_u =>
        cases v₀ with
        | pin q =>
          simp only [FallingUnit.typeOrd] at h_type; omega
        | cluster ps_v =>
          by_cases h_disj : ∀ p ∈ (mapFU (FallingUnit.cluster ps_u)).positions,
              (mapFU (FallingUnit.cluster ps_v)).positions.any
                (fun q => q.dir == p.dir) = false
          · -- 方角素ケース
            apply settleStep_comm_ne_dir
            · exact h_disj
            · intro r hr
              apply List.any_eq_false.mpr
              intro q hq
              have := List.any_eq_false.mp (h_disj q hq) r hr
              rwa [BEq.comm] at this
          · -- 方角共有ケース
            have h_ne_same_dir : ∀ p₀ ∈ ps_u, ∀ q₀ ∈ ps_v,
                p₀.dir = q₀.dir → p₀.layer ≠ q₀.layer := by
              intro p₀ hp₀ q₀ hq₀ hd hl
              have h_eq_pos : p₀ = q₀ := by
                cases p₀; cases q₀; simp only [QuarterPos.mk.injEq] at *; exact ⟨hl, hd⟩
              have h_dp := floatingUnits_elem_positions_disjoint s
                (FallingUnit.cluster ps_u) (FallingUnit.cluster ps_v) hu₀ hv₀ huv p₀ hp₀
              simp only [FallingUnit.positions] at h_dp
              rw [h_eq_pos] at h_dp
              exact absurd BEq.rfl (List.any_eq_false.mp h_dp q₀ hq₀)
            -- h_gap: σ-mapped positions でも layer は保持、gap ≥ 2 は不変
            have h_gap : ∀ p ∈ (mapFU (FallingUnit.cluster ps_u)).positions,
                ∀ q ∈ (mapFU (FallingUnit.cluster ps_v)).positions,
                p.dir = q.dir → p.layer ≠ q.layer ∧
                  ¬(LayerIndex.verticallyAdjacent p.layer q.layer = true) := by
              intro p' hp' q' hq' hdir'
              rw [h_positions_cluster] at hp' hq'
              obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp hp'
              obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hq'
              simp only [σ.qpos_layer]
              rw [σ.qpos_dir, σ.qpos_dir] at hdir'
              have h_dir₀ : p₀.dir = q₀.dir := σ.onDir_injective hdir'
              exact ⟨h_ne_same_dir p₀ hp₀ q₀ hq₀ h_dir₀,
                Bool.eq_false_iff.mp
                  (cluster_same_dir_not_adj s ps_u ps_v hu₀ hv₀ huv p₀ hp₀ q₀ hq₀ h_dir₀)⟩
            by_cases h_ml_bound : (FallingUnit.cluster ps_u).minLayer ≤ 2
            · -- minLayer ≤ 2: settleStep_comm_dir_gap 適用
              apply settleStep_comm_dir_gap
              · exact h_gap
              · rw [h_minLayer]; exact h_ml_bound
              · rw [h_minLayer, ← h_ml]; exact h_ml_bound
              · rw [h_minLayer, h_minLayer]; exact h_ml
            · -- minLayer ≥ 3: ≤5L 制約との矛盾
              exfalso
              push Not at h_ml_bound
              rw [not_forall] at h_disj
              obtain ⟨p', hp'_rest⟩ := h_disj
              rw [Classical.not_imp] at hp'_rest
              obtain ⟨hp', h_any_ne⟩ := hp'_rest
              replace h_any_ne : (mapFU (FallingUnit.cluster ps_v)).positions.any
                  (fun q => q.dir == p'.dir) = true := by
                cases h_b : (mapFU (FallingUnit.cluster ps_v)).positions.any
                    (fun q => q.dir == p'.dir)
                · exact absurd h_b h_any_ne
                · rfl
              -- p' ∈ σ-mapped positions → p₀ ∈ ps_u
              have hp'_mem : p' ∈ ps_u.map σ.onQPos := by
                rw [← h_positions_cluster]; exact hp'
              obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp hp'_mem
              -- q' ∈ σ-mapped positions → q₀ ∈ ps_v
              rw [List.any_eq_true] at h_any_ne
              obtain ⟨q', hq', h_dir_beq⟩ := h_any_ne
              have hq'_mem : q' ∈ ps_v.map σ.onQPos := by
                rw [← h_positions_cluster]; exact hq'
              obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hq'_mem
              simp only [σ.qpos_dir, beq_iff_eq] at h_dir_beq
              have h_dir₀ : p₀.dir = q₀.dir := (σ.onDir_injective h_dir_beq).symm
              -- レイヤ範囲: getQuarter が some → layer < layerCount
              have h_u_all := floatingUnits_cluster_in_allStructuralClustersList s ps_u hu₀
              have ⟨_, hvp, _⟩ := allStructuralClustersList_all_bondable s ps_u h_u_all p₀
                (List.any_eq_true.mpr ⟨p₀, hp₀, BEq.rfl⟩)
              have h_p_lt : p₀.layer < s.layerCount := by
                simp only [Shape.layerCount]; unfold QuarterPos.getQuarter at hvp
                cases hl : s.layers[p₀.layer]? with
                | none => simp only [hl, reduceCtorEq] at hvp
                | some _ => exact (List.getElem?_eq_some_iff.mp hl).1
              have h_v_all := floatingUnits_cluster_in_allStructuralClustersList s ps_v hv₀
              have ⟨_, hvq, _⟩ := allStructuralClustersList_all_bondable s ps_v h_v_all q₀
                (List.any_eq_true.mpr ⟨q₀, hq₀, BEq.rfl⟩)
              have h_q_lt : q₀.layer < s.layerCount := by
                simp only [Shape.layerCount]; unfold QuarterPos.getQuarter at hvq
                cases hl : s.layers[q₀.layer]? with
                | none => simp only [hl, reduceCtorEq] at hvq
                | some _ => exact (List.getElem?_eq_some_iff.mp hl).1
              -- gap ≥ 2 と layer ∈ {3,4} の矛盾
              have h_adj := cluster_same_dir_not_adj s ps_u ps_v hu₀ hv₀ huv p₀ hp₀ q₀ hq₀ h_dir₀
              simp only [LayerIndex.verticallyAdjacent] at h_adj
              have h_adj1 : p₀.layer + 1 ≠ q₀.layer := by
                intro h; simp [h] at h_adj
              have h_adj2 : q₀.layer + 1 ≠ p₀.layer := by
                intro h; simp [h] at h_adj
              have h_ne := h_ne_same_dir p₀ hp₀ q₀ hq₀ h_dir₀
              have h_p_ge := minLayer_le_layer hp₀
                (FallingUnit.cluster ps_u).minLayer (le_refl _)
              have h_q_ge := minLayer_le_layer hq₀
                (FallingUnit.cluster ps_v).minLayer (le_refl _)
              omega

-- ============================================================

end Gravity


