-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity
import S2IL.Operations.Settled.GroundedCore
import S2IL.Operations.Settled.GroundedInvariant

namespace Shape

-- gravity_IsSettled の配置ステップ補題
-- ============================================================

/-- 非接地の非空位置の直下が接地 + 非空であれば、isGroundingContact により
    当該位置自体も接地になる。対偶: 非接地位置の直下は接地 + 非空でない -/
private theorem below_grounded_implies_grounded (s : Shape) (p : QuarterPos)
        (h_ne : ∃ q, p.getQuarter s = some q ∧ !q.isEmpty = true)
        (h_ug : p ∉ Gravity.groundedPositions s)
        (h_below_valid : p.layer ≥ 1) :
        ¬ (∃ q, (⟨p.layer - 1, p.dir⟩ : QuarterPos).getQuarter s = some q ∧
           !q.isEmpty = true ∧ ⟨p.layer - 1, p.dir⟩ ∈ Gravity.groundedPositions s) := by
    intro ⟨q_below, hq_below, hne_below, h_below_g⟩
    apply h_ug
    simp only [Gravity.groundedPositions, List.mem_toFinset] at h_below_g ⊢
    obtain ⟨seed, h_seed_mem, h_reach⟩ := Gravity.groundedPositionsList_sound s
        ⟨p.layer - 1, p.dir⟩ ((Gravity.any_beq_iff_mem _ _).mpr h_below_g)
    obtain ⟨q_p, hq_p, hne_p⟩ := h_ne
    have h_ne_bl : q_below.isEmpty = false := by
        cases q_below <;> simp_all only [ge_iff_le, Quarter.isEmpty, List.mem_filter, Bool.and_eq_true, beq_iff_eq, Bool.decide_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_true, Bool.false_eq_true, decide_false, Bool.not_false]
    have h_ne_qp : q_p.isEmpty = false := by
        cases q_p <;> simp_all only [ge_iff_le, Quarter.isEmpty, Bool.decide_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.mem_filter, Bool.and_eq_true, beq_iff_eq, decide_true, Bool.false_eq_true, decide_false, Bool.not_false]
    have h_contact : Gravity.isGroundingContact s ⟨p.layer - 1, p.dir⟩ p = true := by
        unfold Gravity.isGroundingContact
        rw [hq_below, hq_p]
        simp only [h_ne_bl, h_ne_qp, Bool.not_false, Bool.true_and, Bool.or_eq_true,
            Bool.and_eq_true, beq_iff_eq]
        left
        constructor
        · trivial
        · unfold LayerIndex.verticallyAdjacent
          simp only [Bool.or_eq_true, beq_iff_eq]
          left; omega
    exact (Gravity.any_beq_iff_mem _ _).mp
        (Gravity.groundedPositionsList_complete s seed p h_seed_mem
            (GenericReachable.trans h_reach
                (GenericReachable.step
                    (Gravity.groundingEdge_of_isUpwardGroundingContact
                        (Gravity.isGroundingContact_to_isUpwardGroundingContact
                            h_contact (Nat.sub_le p.layer 1)))
                    GenericReachable.refl)))

/-- 浮遊ユニット内の全位置は layer ≥ 1 を満たす。
    レイヤ 0 の非空位置は常に接地しているため、非接地ユニットにはレイヤ 0 の位置は含まれない。 -/
private lemma floatingUnits_minLayer_ge_one (s : Shape) (u : Gravity.FallingUnit)
        (h_fu : u ∈ Gravity.floatingUnits s) :
        u.minLayer ≥ 1 := by
    rw [Gravity.floatingUnits_eq_append, List.mem_append] at h_fu
    rcases h_fu with h_cl | h_pin
    · -- cluster case
      rw [List.mem_map] at h_cl
      obtain ⟨c, h_c_filtered, rfl⟩ := h_cl
      have h_c_mem := (List.mem_filter.mp h_c_filtered).1
      have h_c_not_grounded := (List.mem_filter.mp h_c_filtered).2
      simp only [Gravity.FallingUnit.minLayer, Gravity.FallingUnit.positions]
      by_contra h_not
      simp only [Nat.not_le] at h_not
      obtain ⟨pos, h_eq, h_valid, _⟩ :=
          Gravity.allStructuralClustersList_is_structuralClusterList s c h_c_mem
      cases hc : c with
      | nil =>
          simp only [hc] at h_eq
          have h_nonempty : (Gravity.structuralClusterList s pos).any (· == pos) = true := by
              unfold Gravity.structuralClusterList; rw [Gravity.structuralBfs_eq_generic]
              exact genericBfs_contains_start _ _ _
                  (s.layerCount * 4 * (s.layerCount * 4))
                  (Nat.mul_pos (Nat.mul_pos (by omega) (by omega))
                      (Nat.mul_pos (by omega) (by omega)))
          rw [← h_eq] at h_nonempty
          simp only [List.any, Bool.false_eq_true] at h_nonempty
      | cons p rest =>
          simp only [hc] at h_not h_c_not_grounded h_c_mem
          have h_min_zero : rest.foldl (fun acc q => min acc q.layer) p.layer = 0 := by omega
          obtain ⟨q, hq_mem, hq_layer⟩ : ∃ q ∈ p :: rest, q.layer = 0 := by
              rcases Gravity.foldl_min_attained rest p.layer with h_init | ⟨q, hq, hq_eq⟩
              · exact ⟨p, .head _, by omega⟩
              · exact ⟨q, .tail _ hq, by omega⟩
          obtain ⟨v, h_gq, h_cfb⟩ :=
              Gravity.allStructuralClustersList_all_bondable s (p :: rest) h_c_mem q
                  ((Gravity.any_beq_iff_mem _ _).mpr hq_mem)
          have h_ng : ((Gravity.groundedPositionsList s).any fun x => x == q) = false := by
              have := (List.all_eq_true.mp h_c_not_grounded) q hq_mem
              simp only [Bool.not_eq_true'] at this; exact this
          have h_q_layer : q.layer < s.layerCount := by
              unfold QuarterPos.getQuarter at h_gq; simp only [Shape.layerCount]
              cases hl : s.layers[q.layer]? with
              | none => simp only [hl, reduceCtorEq] at h_gq
              | some _ => exact (List.getElem?_eq_some_iff.mp hl).1
          have h_seed : q ∈ (QuarterPos.allValid s).filter (fun p =>
                  p.layer == 0 && match p.getQuarter s with
                  | some q => !q.isEmpty | none => false) :=
              List.mem_filter.mpr
                  ⟨(Gravity.any_beq_iff_mem _ _).mp
                      ((Gravity.allValid_any_iff_layer' s q).mpr h_q_layer), by
                      simp only [hq_layer, h_gq, beq_self_eq_true, Bool.true_and]
                      cases v <;> simp_all only [List.mem_filter, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false, beq_iff_eq, Quarter.canFormBond, Nat.lt_add_one, not_false_eq_true, implies_true, Bool.false_eq_true, Quarter.isEmpty, Bool.not_false]⟩
          exact absurd (Gravity.groundedPositionsList_complete s q q h_seed GenericReachable.refl)
              (by rw [h_ng]; exact Bool.false_ne_true)
    · -- pin case
      rw [List.mem_map] at h_pin
      obtain ⟨p, h_p_filtered, rfl⟩ := h_pin
      have h_p_iso := (List.mem_filter.mp h_p_filtered).1
      have h_p_not_grounded := (List.mem_filter.mp h_p_filtered).2
      simp only [Gravity.FallingUnit.minLayer, Gravity.FallingUnit.positions]
      by_contra h_not
      simp only [Nat.not_le] at h_not
      have h_layer_zero : p.layer = 0 := Nat.lt_one_iff.mp h_not
      have h_pin := Gravity.allIsolatedPins_is_pin s p
          ((Gravity.any_beq_iff_mem _ _).mpr h_p_iso)
      have h_seed : p ∈ (QuarterPos.allValid s).filter (fun q =>
          q.layer == 0 && match q.getQuarter s with
          | some q => !q.isEmpty | none => false) := by
        rw [List.mem_filter]
        constructor
        · unfold Gravity.allIsolatedPins at h_p_iso
          exact List.mem_of_mem_filter h_p_iso
        · simp only [h_layer_zero, h_pin, beq_self_eq_true, Quarter.isEmpty,
              Bool.not_false, Bool.true_and]
      simp only [Bool.not_eq_true'] at h_p_not_grounded
      exact absurd (Gravity.groundedPositionsList_complete s p p h_seed GenericReachable.refl)
          (by rw [h_p_not_grounded]; exact Bool.false_ne_true)


    /-- cluster の着地位置で isStructurallyBonded → groundingEdge（シフト後）
        foldl 配置により両端が canFormBond → isStructurallyBonded 保存。隣接は uniform shift で保存。 -/
private theorem cluster_step_groundingEdge
        (s : Shape) (obs : List Layer) (ps : List QuarterPos) (d : Nat)
        (a b : QuarterPos) (ha : a ∈ ps) (hb : b ∈ ps)
        (h_sb : Gravity.isStructurallyBonded s a b = true)
        (h_bond : ∀ q ∈ ps, ∃ qv, q.getQuarter s = some qv ∧ qv.canFormBond = true)
        (h_d_le : d ≤ (Gravity.FallingUnit.cluster ps).minLayer)
        (s_result : Shape)
        (h_of : Shape.ofLayers (Gravity.placeFallingUnit s obs (.cluster ps) d) =
            some s_result) :
        Gravity.groundingEdge s_result
            ⟨a.layer - d, a.dir⟩ ⟨b.layer - d, b.dir⟩ = true := by
    set obs' := Gravity.placeFallingUnit s obs (.cluster ps) d with h_obs'_def
    -- foldl で a, b の着地位置に canFormBond の quarter が配置される
    have h_foldl_a := Gravity.foldl_placeQuarter_written_canFormBond s obs ps d
        (a.layer - d) a.dir ⟨a, ha, rfl, rfl⟩ h_bond
    have h_foldl_b := Gravity.foldl_placeQuarter_written_canFormBond s obs ps d
        (b.layer - d) b.dir ⟨b, hb, rfl, rfl⟩ h_bond
    obtain ⟨qa, h_gd_a, h_bond_a⟩ := h_foldl_a
    obtain ⟨qb, h_gd_b, h_bond_b⟩ := h_foldl_b
    -- foldl 結果を obs' に正規化（set が後から導入された仮説には効かないため）
    change QuarterPos.getDir (obs'.getD (a.layer - d) Layer.empty) a.dir = qa at h_gd_a
    change QuarterPos.getDir (obs'.getD (b.layer - d) Layer.empty) b.dir = qb at h_gd_b
    -- obs' → s_result bridging
    have h_layers : s_result.layers = obs' := by
        cases h_obs'_list : obs' with
        | nil => simp only [Shape.ofLayers, h_obs'_list] at h_of; cases h_of
        | cons hd tl =>
            simp only [Shape.ofLayers, h_obs'_list] at h_of
            exact (Option.some.inj h_of) ▸ rfl
    -- a.layer - d < obs'.length（canFormBond から empty でない → layer 存在）
    have h_a_lt : a.layer - d < obs'.length := by
        by_contra h_ge
        have h_ge' : obs'.length ≤ a.layer - d := by omega
        simp only [List.getD_eq_getElem?_getD,
            List.getElem?_eq_none_iff.mpr h_ge', Option.getD_none] at h_gd_a
        subst h_gd_a
        cases hd : a.dir <;>
            simp only [Quarter.canFormBond, QuarterPos.getDir, hd, Layer.empty, Bool.false_eq_true] at h_bond_a
    have h_b_lt : b.layer - d < obs'.length := by
        by_contra h_ge
        have h_ge' : obs'.length ≤ b.layer - d := by omega
        simp only [List.getD_eq_getElem?_getD,
            List.getElem?_eq_none_iff.mpr h_ge', Option.getD_none] at h_gd_b
        subst h_gd_b
        cases hd : b.dir <;>
            simp only [Quarter.canFormBond, QuarterPos.getDir, hd, Layer.empty, Bool.false_eq_true] at h_bond_b
    -- getQuarter s_result の具体値
    have h_getD_a : obs'.getD (a.layer - d) Layer.empty = obs'[a.layer - d] := by
        simp only [List.getD, List.getElem?_eq_getElem h_a_lt, Option.getD_some]
    have h_getD_b : obs'.getD (b.layer - d) Layer.empty = obs'[b.layer - d] := by
        simp only [List.getD, List.getElem?_eq_getElem h_b_lt, Option.getD_some]
    have h_gq_a : (⟨a.layer - d, a.dir⟩ : QuarterPos).getQuarter s_result = some qa := by
        simp only [QuarterPos.getQuarter, h_layers,
            List.getElem?_eq_getElem h_a_lt]
        rw [← h_getD_a]; exact congrArg some h_gd_a
    have h_gq_b : (⟨b.layer - d, b.dir⟩ : QuarterPos).getQuarter s_result = some qb := by
        simp only [QuarterPos.getQuarter, h_layers,
            List.getElem?_eq_getElem h_b_lt]
        rw [← h_getD_b]; exact congrArg some h_gd_b
    -- groundingEdge = isStructurallyBonded 経由で証明
    apply Gravity.groundingEdge_of_isStructurallyBonded
    simp only [Gravity.isStructurallyBonded, h_gq_a, h_gq_b, h_bond_a, h_bond_b,
        Bool.true_and, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
    -- isStructurallyBonded から隣接条件を抽出
    simp only [Gravity.isStructurallyBonded] at h_sb
    cases h_qa_orig : a.getQuarter s with
    | none => simp only [h_qa_orig] at h_sb; cases h_sb
    | some qa_orig =>
      cases h_qb_orig : b.getQuarter s with
      | none => simp only [h_qa_orig, h_qb_orig] at h_sb; cases h_sb
      | some qb_orig =>
        simp only [h_qa_orig, h_qb_orig, Bool.and_eq_true, Bool.or_eq_true,
            beq_iff_eq] at h_sb
        obtain ⟨_, h_adj⟩ := h_sb
        -- d ≤ a.layer, d ≤ b.layer
        have h_d_a : d ≤ a.layer :=
            Gravity.minLayer_le_layer (u := .cluster ps) ha d h_d_le
        have h_d_b : d ≤ b.layer :=
            Gravity.minLayer_le_layer (u := .cluster ps) hb d h_d_le
        rcases h_adj with ⟨h_eq, h_adj_dir⟩ | ⟨h_vadj, h_eq_dir⟩
        · -- 水平方向: 同レイヤ + 隣接方角
          left; exact ⟨by omega, h_adj_dir⟩
        · -- 垂直方向: 垂直隣接 + 同方角
          right; refine ⟨?_, h_eq_dir⟩
          simp only [LayerIndex.verticallyAdjacent, Bool.or_eq_true, beq_iff_eq] at h_vadj ⊢
          rcases h_vadj with h1 | h1 <;> [left; right] <;> omega

/-- 1 つの FU 配置が接地不変量を保存する。
    obstacle（全非空位置が接地）に FU u を配置した結果も全非空位置が接地。
    証明構造: 2 ケースに分解
    (A) FU 着地位置: landing contact → grounded
    (B) 非 FU 位置: getQuarter 保存 → groundedPositions_mono で保存
    着地位置空の仮説が必要（pin FU が非空セルを上書きすると horizontal edge 破壊で
    隣接位置が接地を失う反例が存在するため）。 -/
private theorem one_step_all_grounded
        (s : Shape) (obs : List Layer) (u : Gravity.FallingUnit)
        (h_inv : AllNonEmptyGrounded obs)
        (h_empty_landing : ∀ q ∈ u.positions,
            (QuarterPos.getDir (obs.getD (q.layer - Gravity.landingDistance u obs)
                Layer.empty) q.dir).isEmpty = true)
        (h_connected : ∀ q1 ∈ u.positions, ∀ q2 ∈ u.positions,
            GenericReachable (Gravity.isStructurallyBonded s) q1 q2)
        (h_cluster_bond : match u with
            | .cluster _ => ∀ q ∈ u.positions,
                ∃ qv, q.getQuarter s = some qv ∧ qv.canFormBond = true
            | .pin _ => True)
        (h_cluster_closed : match u with
            | .cluster _ => ∀ q ∈ u.positions, ∀ r,
                Gravity.isStructurallyBonded s q r = true → r ∈ u.positions
            | .pin _ => True) :
        AllNonEmptyGrounded (Gravity.placeFallingUnit s obs u
            (Gravity.landingDistance u obs)) := by
    set d := Gravity.landingDistance u obs with h_d_def
    set obs' := Gravity.placeFallingUnit s obs u d with h_obs'_def
    intro s_result h_of p h_valid h_ne
    -- p が FU 着地位置集合に含まれるかで場合分け
    by_cases h_mod :
            (u.positions.any fun q => (q.layer - d) == p.layer && q.dir == p.dir) = true
    · -- ★ Case A: p は FU の着地位置
      cases u with
      | cluster ps =>
          -- cluster case: 構造連結性 + 着地接触 → 全着地位置が接地
          -- h_mod から p に対応するクラスタ位置 q_i を抽出
          rw [List.any_eq_true] at h_mod
          obtain ⟨q_i, h_qi_mem, h_qi_match⟩ := h_mod
          have h_qi_beq := Bool.and_eq_true_iff.mp h_qi_match
          have h_qi_layer : q_i.layer - d = p.layer := beq_iff_eq.mp h_qi_beq.1
          have h_qi_dir : q_i.dir = p.dir := beq_iff_eq.mp h_qi_beq.2
          -- p.layer = 0 なら直接 seed → grounded（pin floor case と同一）
          by_cases h_floor_p : p.layer = 0
          · simp only [Gravity.groundedPositions, List.mem_toFinset]
            obtain ⟨q_ne, hq_ne, hq_ne_ne⟩ := h_ne
            have h_seed : p ∈ (QuarterPos.allValid s_result).filter (fun q =>
                q.layer == 0 && match q.getQuarter s_result with
                | some q => !q.isEmpty | none => false) := by
              apply List.mem_filter.mpr
              constructor
              · exact (Gravity.any_beq_iff_mem _ _).mp
                  ((Gravity.allValid_any_iff_layer' s_result p).mpr h_valid)
              · show (p.layer == 0 && match p.getQuarter s_result with
                    | some q => !q.isEmpty | none => false) = true
                have h_ne_bool : (!q_ne.isEmpty) = true := by
                  rcases q_ne with _ | _ | _ | _ <;> simp only [Quarter.isEmpty, decide_true, Bool.not_true, Bool.false_eq_true, decide_false, Bool.not_false] at hq_ne_ne ⊢
                simp only [show (p.layer == 0) = true from beq_iff_eq.mpr h_floor_p,
                    Bool.true_and, hq_ne, h_ne_bool]
            exact (Gravity.any_beq_iff_mem _ _).mp
                (Gravity.groundedPositionsList_complete s_result p p h_seed
                    GenericReachable.refl)
          · -- ★ p.layer ≥ 1: 構造連結性による接地伝播
            -- q_min: 最小着地レイヤの位置（obstacle below が非着地保証）
            have h_ne_ps : ps ≠ [] := List.ne_nil_of_mem h_qi_mem
            have h_d_le_min : d ≤ (Gravity.FallingUnit.cluster ps).minLayer :=
                Gravity.landingDistance_le_minLayer (.cluster ps) obs
            obtain ⟨q_min, h_qmin_mem, h_qmin_layer⟩ :=
                Gravity.minLayer_witness (.cluster ps) h_ne_ps
            simp only [Gravity.FallingUnit.positions] at h_qmin_mem
            have h_d_le_qmin : d ≤ q_min.layer := h_qmin_layer ▸ h_d_le_min
            -- q_min → q_i の到達可能性
            have h_reach_qi := h_connected q_min
                (show q_min ∈ (Gravity.FallingUnit.cluster ps).positions from h_qmin_mem)
                q_i
                (show q_i ∈ (Gravity.FallingUnit.cluster ps).positions from h_qi_mem)
            -- ★ 任意の接地クラスタメンバーから q_i への接地伝播
            suffices h_exists_grounded :
                ∃ q_g ∈ ps, ⟨q_g.layer - d, q_g.dir⟩ ∈
                    Gravity.groundedPositions s_result from by
              obtain ⟨q_g, hq_g_mem, hq_g_grounded⟩ := h_exists_grounded
              -- connectivity bridging: map_step_inv で変換 (q_g → q_i)
              have h_reach_qi_g := h_connected q_g
                  (show q_g ∈ (Gravity.FallingUnit.cluster ps).positions from hq_g_mem)
                  q_i
                  (show q_i ∈ (Gravity.FallingUnit.cluster ps).positions from h_qi_mem)
              -- map_step_inv で isStructurallyBonded チェーンを groundingEdge チェーンに変換
              have h_mapped := h_reach_qi_g.map_step_inv
                  (edge2 := Gravity.groundingEdge s_result)
                  (f := fun q => ⟨q.layer - d, q.dir⟩)
                  (P := fun q => q ∈ ps)
                  (fun a' b' ha' h_sb' =>
                      ⟨h_cluster_closed a'
                          (show a' ∈ (Gravity.FallingUnit.cluster ps).positions from ha')
                          b' h_sb',
                       cluster_step_groundingEdge s obs ps d a' b' ha'
                          (h_cluster_closed a'
                              (show a' ∈ (Gravity.FallingUnit.cluster ps).positions from ha')
                              b' h_sb')
                          h_sb' h_cluster_bond h_d_le_min s_result h_of⟩)
                  hq_g_mem
              -- groundedPositionsList_closed で閉包
              have h_g_any : (Gravity.groundedPositionsList s_result).any
                  (· == ⟨q_g.layer - d, q_g.dir⟩) = true :=
                  (Gravity.any_beq_iff_mem _ _).mpr
                      (by rwa [Gravity.groundedPositions, List.mem_toFinset] at hq_g_grounded)
              have h_qi_any := Gravity.groundedPositionsList_closed s_result
                  ⟨q_g.layer - d, q_g.dir⟩ ⟨q_i.layer - d, q_i.dir⟩
                  h_g_any h_mapped.2
              have h_p_eq : p = ⟨q_i.layer - d, q_i.dir⟩ := by
                  rcases p with ⟨p_l, p_d⟩
                  simp only [] at h_qi_layer h_qi_dir
                  subst h_qi_layer; subst h_qi_dir; rfl
              rw [h_p_eq]
              rw [Gravity.groundedPositions, List.mem_toFinset]
              exact (Gravity.any_beq_iff_mem _ _).mp h_qi_any
            -- ★ ∃ grounded cluster member: 強帰納法で証明
            -- landingDistance_landed で obstacle/floor 接触位置を取得
            have h_landed := Gravity.landingDistance_landed (.cluster ps) obs h_ne_ps
            simp only [Gravity.FallingUnit.positions] at h_landed
            rw [List.any_eq_true] at h_landed
            obtain ⟨q_btl, h_btl_mem, h_btl_cond⟩ := h_landed
            simp only [Bool.or_eq_true, beq_iff_eq] at h_btl_cond
            -- ★ q_btl の接地を直接証明（obstacle は必ず obs 由来、強帰納法不要）
            have h_foldl_btl := Gravity.foldl_placeQuarter_written_canFormBond
                s obs ps d (q_btl.layer - d) q_btl.dir
                ⟨q_btl, h_btl_mem, rfl, rfl⟩ h_cluster_bond
            obtain ⟨qv_btl, h_gd_btl, h_bond_btl⟩ := h_foldl_btl
            change QuarterPos.getDir (obs'.getD (q_btl.layer - d) Layer.empty)
                q_btl.dir = qv_btl at h_gd_btl
            have h_ne_btl : (!qv_btl.isEmpty) = true := by
                rcases qv_btl with _ | _ | _ | _ <;>
                    simp only [Quarter.canFormBond, Bool.false_eq_true, Quarter.isEmpty, Bool.not_false] at h_bond_btl ⊢
            have h_btl_lt : q_btl.layer - d < obs'.length := by
                by_contra h_ge'
                have h_ge'' : obs'.length ≤ q_btl.layer - d := by omega
                simp only [List.getD_eq_getElem?_getD,
                    List.getElem?_eq_none_iff.mpr h_ge'',
                    Option.getD_none] at h_gd_btl
                subst h_gd_btl
                cases hd' : q_btl.dir <;>
                    simp only [Quarter.canFormBond, QuarterPos.getDir, hd', Layer.empty, Bool.false_eq_true] at h_bond_btl
            have h_layers : s_result.layers = obs' := by
                cases h_obs'_list : obs' with
                | nil => simp only [Shape.ofLayers, h_obs'_list] at h_of
                         cases h_of
                | cons hd tl =>
                    simp only [Shape.ofLayers, h_obs'_list] at h_of
                    exact (Option.some.inj h_of) ▸ rfl
            have h_gq_btl : (⟨q_btl.layer - d, q_btl.dir⟩ :
                QuarterPos).getQuarter s_result = some qv_btl := by
                simp only [QuarterPos.getQuarter, h_layers,
                    List.getElem?_eq_getElem h_btl_lt]
                rw [← (show obs'.getD (q_btl.layer - d) Layer.empty =
                    obs'[q_btl.layer - d] from by
                    simp only [List.getD_eq_getElem?_getD,
                        List.getElem?_eq_getElem h_btl_lt,
                        Option.getD_some])]
                exact congrArg some h_gd_btl
            have h_valid_btl : q_btl.layer - d < s_result.layerCount := by
                simp only [Shape.layerCount, h_layers]; exact h_btl_lt
            refine ⟨q_btl, h_btl_mem, ?_⟩
            by_cases h_z : q_btl.layer - d = 0
            · -- Layer 0: seed → grounded
              simp only [Gravity.groundedPositions, List.mem_toFinset]
              have h_seed : ⟨q_btl.layer - d, q_btl.dir⟩ ∈
                  (QuarterPos.allValid s_result).filter (fun p' =>
                      p'.layer == 0 && match p'.getQuarter s_result with
                      | some q => !q.isEmpty | none => false) := by
                  apply List.mem_filter.mpr
                  exact ⟨(Gravity.any_beq_iff_mem _ _).mp
                      ((Gravity.allValid_any_iff_layer' s_result
                          ⟨q_btl.layer - d, q_btl.dir⟩).mpr
                          h_valid_btl),
                      show ((q_btl.layer - d) == 0 &&
                          match (⟨q_btl.layer - d, q_btl.dir⟩ :
                              QuarterPos).getQuarter s_result with
                          | some q => !q.isEmpty
                          | none => false) = true from by
                      simp only [show ((q_btl.layer - d) == 0) =
                              true from beq_iff_eq.mpr h_z,
                          Bool.true_and, h_gq_btl, h_ne_btl]⟩
              exact (Gravity.any_beq_iff_mem _ _).mp
                  (Gravity.groundedPositionsList_complete s_result
                      ⟨q_btl.layer - d, q_btl.dir⟩
                      ⟨q_btl.layer - d, q_btl.dir⟩
                      h_seed GenericReachable.refl)
            · -- Layer ≥ 1: obstacle below → groundedPositions_mono
              have h_btl_ge1 : q_btl.layer - d ≥ 1 :=
                  Nat.one_le_iff_ne_zero.mpr h_z
              -- h_btl_cond から obstacle を抽出（floor は h_z と矛盾）
              have h_occ : Gravity.isOccupied obs
                  (q_btl.layer - d - 1) q_btl.dir = true := by
                  rcases h_btl_cond with h_floor | h_obs
                  · omega
                  · exact h_obs
              have h_below_lt : q_btl.layer - d - 1 < obs.length := by
                  unfold Gravity.isOccupied at h_occ
                  by_contra h_ge; simp only [not_lt] at h_ge
                  simp only [List.getElem?_eq_none_iff.mpr h_ge]
                      at h_occ
                  cases h_occ
              -- by_contra + below_grounded_implies_grounded
              by_contra h_ug
              have h_no_below := below_grounded_implies_grounded
                  s_result ⟨q_btl.layer - d, q_btl.dir⟩
                  ⟨qv_btl, h_gq_btl,
                      by cases qv_btl <;>
                          simp_all only [Quarter.isEmpty, Bool.decide_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.getD_eq_getElem?_getD, BEq.rfl, Bool.and_true, beq_iff_eq, and_self, ne_eq, ge_iff_le, getElem?_pos, Option.getD_some, Bool.false_eq_true, Bool.not_false, decide_false]⟩
                  h_ug h_btl_ge1
              apply h_no_below
              -- ★ (q_btl.layer-d-1, q_btl.dir) が s_result で
              --   非空かつ接地を示す
              cases h_obs_cas : obs with
              | nil => simp only [h_obs_cas, List.length_nil, Nat.not_lt_zero] at h_below_lt
              | cons obs_hd obs_tl =>
                set s_obs : Shape := ⟨obs_hd :: obs_tl,
                    List.cons_ne_nil obs_hd obs_tl⟩
                have h_obs_of : Shape.ofLayers obs = some s_obs :=
                    by rw [h_obs_cas]; rfl
                have h_layers_obs : s_obs.layers = obs := by
                    show (obs_hd :: obs_tl) = obs
                    exact h_obs_cas.symm
                -- 着地位置でない（h_empty_landing + isOccupied 矛盾）
                have h_below_not_landing : ∀ q ∈
                    (Gravity.FallingUnit.cluster ps).positions,
                    ¬(q.layer - d = q_btl.layer - d - 1 ∧
                        q.dir = q_btl.dir) := by
                  simp only [Gravity.FallingUnit.positions]
                  intro q' hq'_mem ⟨h1, h2⟩
                  have h_el := h_empty_landing q' hq'_mem
                  rw [h1, h2] at h_el
                  have h_getD_eq :
                      obs.getD (q_btl.layer - d - 1)
                          Layer.empty =
                      obs[q_btl.layer - d - 1] := by
                    simp only [List.getD,
                        List.getElem?_eq_getElem h_below_lt,
                        Option.getD_some]
                  rw [h_getD_eq] at h_el
                  have h_q_ne : (QuarterPos.getDir
                      obs[q_btl.layer - d - 1]
                      q_btl.dir).isEmpty = false := by
                    unfold Gravity.isOccupied at h_occ
                    simp only [
                        List.getElem?_eq_getElem h_below_lt,
                        Bool.not_eq_true'] at h_occ
                    exact h_occ
                  rw [h_el] at h_q_ne; cases h_q_ne
                -- obs → obs' quarter 保存
                have h_gd_below :=
                    Gravity.foldl_placeQuarter_getDir_preserved
                        s obs
                        (Gravity.FallingUnit.cluster
                            ps).positions d
                        (q_btl.layer - d - 1) q_btl.dir
                        h_below_not_landing
                -- obs での非空性
                have h_obs_getD :
                    obs.getD (q_btl.layer - d - 1)
                        Layer.empty =
                    obs[q_btl.layer - d - 1] := by
                  simp only [List.getD,
                      List.getElem?_eq_getElem h_below_lt,
                      Option.getD_some]
                have h_q_ne_empty : (QuarterPos.getDir
                    obs[q_btl.layer - d - 1]
                    q_btl.dir).isEmpty = false := by
                  unfold Gravity.isOccupied at h_occ
                  simp only [
                      List.getElem?_eq_getElem h_below_lt,
                      Bool.not_eq_true'] at h_occ
                  exact h_occ
                set q_below := QuarterPos.getDir
                    obs[q_btl.layer - d - 1] q_btl.dir
                have h_q_ne_bool : !q_below.isEmpty = true := by
                  cases h_qb : q_below <;>
                    simp only [Quarter.isEmpty, h_qb, Bool.true_eq_false, Bool.false_eq_true, decide_false, Bool.not_false]
                        at h_q_ne_empty ⊢
                -- getQuarter s_obs
                have h_gq_obs : (⟨q_btl.layer - d - 1,
                    q_btl.dir⟩ : QuarterPos).getQuarter
                    s_obs = some q_below := by
                  show (match s_obs.layers[
                      (q_btl.layer - d - 1)]? with
                      | some l => some
                          (QuarterPos.getDir l q_btl.dir)
                      | none => none) = some q_below
                  rw [h_layers_obs,
                      List.getElem?_eq_getElem h_below_lt]
                have h_below_valid_obs :
                    (q_btl.layer - d - 1) <
                    s_obs.layerCount := by
                  simp only [Shape.layerCount, h_layers_obs]
                  exact h_below_lt
                -- h_inv で s_obs において接地
                have h_grounded_obs :
                    (⟨q_btl.layer - d - 1, q_btl.dir⟩ :
                        QuarterPos) ∈
                    Gravity.groundedPositions s_obs :=
                  h_inv s_obs h_obs_of
                      ⟨q_btl.layer - d - 1, q_btl.dir⟩
                      h_below_valid_obs
                      ⟨q_below, h_gq_obs, h_q_ne_bool⟩
                -- ★ groundedPositions_mono: s_obs → s_result
                have h_lc : s_obs.layerCount ≤
                    s_result.layerCount := by
                  simp only [Shape.layerCount, h_layers_obs,
                      h_layers, h_obs'_def]
                  exact placeFallingUnit_length_ge s obs
                      (.cluster ps) d
                have h_gq_mono : ∀ p' : QuarterPos,
                    p'.layer < s_obs.layerCount →
                    (∃ q, p'.getQuarter s_obs = some q ∧
                        !q.isEmpty = true) →
                    p'.getQuarter s_result =
                        p'.getQuarter s_obs := by
                  intro p' h_p'_valid h_p'_ne
                  by_cases h_p'_land :
                      ((Gravity.FallingUnit.cluster
                          ps).positions.any fun q =>
                          (q.layer - d) == p'.layer &&
                              q.dir == p'.dir) = true
                  · -- p' は着地位置 → obs 空 → 矛盾
                    rw [List.any_eq_true] at h_p'_land
                    obtain ⟨q_fu, h_q_mem, h_q_match⟩ :=
                        h_p'_land
                    simp only [
                        Gravity.FallingUnit.positions]
                        at h_q_mem
                    have h_q_beq :=
                        Bool.and_eq_true_iff.mp h_q_match
                    have h_layer_eq :
                        q_fu.layer - d = p'.layer :=
                        beq_iff_eq.mp h_q_beq.1
                    have h_dir_eq :
                        q_fu.dir = p'.dir :=
                        beq_iff_eq.mp h_q_beq.2
                    have h_el :=
                        h_empty_landing q_fu h_q_mem
                    rw [h_layer_eq, h_dir_eq] at h_el
                    have h_p'_lt_obs :
                        p'.layer < obs.length := by
                      simp only [Shape.layerCount,
                          h_layers_obs] at h_p'_valid
                      exact h_p'_valid
                    have h_obs_getD_p' :
                        obs.getD p'.layer Layer.empty =
                        obs[p'.layer] := by
                      simp only [List.getD,
                          List.getElem?_eq_getElem
                              h_p'_lt_obs,
                          Option.getD_some]
                    rw [h_obs_getD_p'] at h_el
                    have h_gq_obs_p' :
                        p'.getQuarter s_obs =
                        some (QuarterPos.getDir
                            obs[p'.layer] p'.dir) := by
                      simp only [QuarterPos.getQuarter,
                          h_layers_obs,
                          List.getElem?_eq_getElem
                              h_p'_lt_obs]
                    have h_q_empty :
                        QuarterPos.getDir obs[p'.layer]
                            p'.dir = Quarter.empty := by
                      cases h_q :
                          QuarterPos.getDir obs[p'.layer]
                              p'.dir <;>
                        simp only [Quarter.isEmpty, h_q, Bool.false_eq_true]
                            at h_el ⊢
                    rw [h_q_empty] at h_gq_obs_p'
                    obtain ⟨q', hq', hq'_ne⟩ := h_p'_ne
                    rw [h_gq_obs_p'] at hq'
                    have := Option.some.inj hq'; subst this
                    exact absurd hq'_ne (by native_decide)
                  · -- p' は非着地位置 → 保存
                    have h_p'_not_land : ∀ q ∈
                        (Gravity.FallingUnit.cluster
                            ps).positions,
                        ¬(q.layer - d = p'.layer ∧
                            q.dir = p'.dir) := by
                      intro q h_q_mem ⟨h_lay, h_dir⟩
                      have : (Gravity.FallingUnit.cluster
                          ps).positions.any
                          (fun r =>
                              (r.layer - d) == p'.layer &&
                              r.dir == p'.dir) = true := by
                        rw [List.any_eq_true]
                        exact ⟨q, h_q_mem,
                            by simp only [h_lay, BEq.rfl, h_dir, Bool.and_self]⟩
                      simp only [this, not_true_eq_false] at h_p'_land
                    have h_gd_p' :=
                        Gravity.foldl_placeQuarter_getDir_preserved
                            s obs
                            (Gravity.FallingUnit.cluster
                                ps).positions d
                            p'.layer p'.dir h_p'_not_land
                    have h_p'_lt_obs :
                        p'.layer < obs.length := by
                      simp only [Shape.layerCount,
                          h_layers_obs] at h_p'_valid
                      exact h_p'_valid
                    have h_obs_getD_p' :
                        obs.getD p'.layer Layer.empty =
                        obs[p'.layer] := by
                      simp only [List.getD,
                          List.getElem?_eq_getElem
                              h_p'_lt_obs,
                          Option.getD_some]
                    have h_obs'_valid_p' :
                        p'.layer < obs'.length := by
                      rw [← h_layers]
                      exact Nat.lt_of_lt_of_le
                          h_p'_valid h_lc
                    have h_obs'_getD_p' :
                        obs'.getD p'.layer Layer.empty =
                        obs'[p'.layer] := by
                      simp only [List.getD,
                          List.getElem?_eq_getElem
                              h_obs'_valid_p',
                          Option.getD_some]
                    have h_dir_eq_p' :
                        QuarterPos.getDir obs'[p'.layer]
                            p'.dir =
                        QuarterPos.getDir obs[p'.layer]
                            p'.dir := by
                      rw [← h_obs'_getD_p',
                          ← h_obs_getD_p']
                      exact h_gd_p'
                    simp only [QuarterPos.getQuarter,
                        h_layers, h_layers_obs,
                        List.getElem?_eq_getElem
                            h_obs'_valid_p',
                        List.getElem?_eq_getElem
                            h_p'_lt_obs,
                        h_dir_eq_p']
                have h_grounded_res :=
                    groundedPositions_mono s_obs s_result
                        h_lc h_gq_mono h_grounded_obs
                have h_gq_res : (⟨q_btl.layer - d - 1,
                    q_btl.dir⟩ : QuarterPos).getQuarter
                    s_result = some q_below := by
                  rw [h_gq_mono
                      ⟨q_btl.layer - d - 1, q_btl.dir⟩
                      h_below_valid_obs
                      ⟨q_below, h_gq_obs, h_q_ne_bool⟩]
                  exact h_gq_obs
                exact ⟨q_below, h_gq_res, h_q_ne_bool,
                    h_grounded_res⟩
      | pin pos =>
          -- pin case: positions = [pos], q_contact = p（自明）
          -- h_mod から pos.layer - d = p.layer かつ pos.dir = p.dir
          simp only [Gravity.FallingUnit.positions, List.any_cons, List.any_nil,
              Bool.or_false, Bool.and_eq_true, beq_iff_eq] at h_mod
          obtain ⟨h_lay, h_dir⟩ := h_mod
          -- p.layer = pos.layer - d かつ p.dir = pos.dir
          have h_p_layer : p.layer = pos.layer - d := h_lay.symm
          have h_p_dir : p.dir = pos.dir := h_dir.symm
          -- landingDistance_landed: floor contact 又は obstacle contact
          have h_landed : pos.layer - d = 0 ∨
              Gravity.isOccupied obs (pos.layer - d - 1) pos.dir = true := by
            have h := Gravity.landingDistance_landed (.pin pos) obs (List.cons_ne_nil _ _)
            simp only [Gravity.FallingUnit.positions, List.any_cons, List.any_nil,
                Bool.or_false, Bool.or_eq_true, beq_iff_eq] at h
            exact h
          -- floor/obstacle 共通: layer 0 非空 → seed → grounded のヘルパー
          suffices h_goal : p ∈ Gravity.groundedPositions s_result from h_goal
          rcases h_landed with h_floor | h_obstacle
          · -- ★ Floor contact: p.layer = 0 → seed → grounded
            have h_layer0 : p.layer = 0 := by omega
            simp only [Gravity.groundedPositions, List.mem_toFinset]
            obtain ⟨q_ne, hq_ne, hq_ne_ne⟩ := h_ne
            have h_seed : p ∈ (QuarterPos.allValid s_result).filter (fun q =>
                q.layer == 0 && match q.getQuarter s_result with
                | some q => !q.isEmpty | none => false) := by
              apply List.mem_filter.mpr
              constructor
              · exact (Gravity.any_beq_iff_mem _ _).mp
                  ((Gravity.allValid_any_iff_layer' s_result p).mpr h_valid)
              · show (p.layer == 0 && match p.getQuarter s_result with
                    | some q => !q.isEmpty | none => false) = true
                have h_ne_bool : (!q_ne.isEmpty) = true := by
                  rcases q_ne with _ | _ | _ | _ <;> simp only [Quarter.isEmpty, decide_true, Bool.not_true, Bool.false_eq_true, decide_false, Bool.not_false] at hq_ne_ne ⊢
                simp only [show (p.layer == 0) = true from beq_iff_eq.mpr h_layer0,
                    Bool.true_and, hq_ne, h_ne_bool]
            exact (Gravity.any_beq_iff_mem _ _).mp
                (Gravity.groundedPositionsList_complete s_result p p h_seed
                    GenericReachable.refl)
          · -- ★ Obstacle contact: (p.layer - 1, p.dir) が obs で occupied
            -- p.layer = 0 なら floor と同じ方法で直接 grounded
            cases h_pz : Nat.decEq p.layer 0 with
            | isTrue h_zero =>
              simp only [Gravity.groundedPositions, List.mem_toFinset]
              obtain ⟨q_ne, hq_ne, hq_ne_ne⟩ := h_ne
              have h_seed : p ∈ (QuarterPos.allValid s_result).filter (fun q =>
                  q.layer == 0 && match q.getQuarter s_result with
                  | some q => !q.isEmpty | none => false) := by
                apply List.mem_filter.mpr
                constructor
                · exact (Gravity.any_beq_iff_mem _ _).mp
                    ((Gravity.allValid_any_iff_layer' s_result p).mpr h_valid)
                · show (p.layer == 0 && match p.getQuarter s_result with
                      | some q => !q.isEmpty | none => false) = true
                  have h_ne_bool : (!q_ne.isEmpty) = true := by
                    rcases q_ne with _ | _ | _ | _ <;> simp only [Quarter.isEmpty, decide_true, Bool.not_true, Bool.false_eq_true, decide_false, Bool.not_false] at hq_ne_ne ⊢
                  simp only [show (p.layer == 0) = true from beq_iff_eq.mpr h_zero,
                      Bool.true_and, hq_ne, h_ne_bool]
              exact (Gravity.any_beq_iff_mem _ _).mp
                  (Gravity.groundedPositionsList_complete s_result p p h_seed
                      GenericReachable.refl)
            | isFalse h_pos =>
              -- p.layer ≥ 1、(p.layer - 1, p.dir) が obs で occupied
              -- by_contra + below_grounded_implies_grounded で証明
              have h_p_ge1 : p.layer ≥ 1 := Nat.one_le_iff_ne_zero.mpr h_pos
              -- h_obstacle を p の項に変換
              have h_occ : Gravity.isOccupied obs (p.layer - 1) p.dir = true := by
                rw [show p.layer - 1 = pos.layer - d - 1 from by omega, h_p_dir]
                exact h_obstacle
              -- p.layer - 1 < obs.length
              have h_below_lt : p.layer - 1 < obs.length := by
                unfold Gravity.isOccupied at h_occ
                by_contra h_ge; simp only [not_lt] at h_ge
                simp only [List.getElem?_eq_none_iff.mpr h_ge] at h_occ; cases h_occ
              -- by_contra: p が非接地と仮定し矛盾を導く
              by_contra h_ug
              have h_no_below := below_grounded_implies_grounded s_result p h_ne
                  h_ug h_p_ge1
              apply h_no_below
              -- ★ (p.layer-1, p.dir) が s_result で非空かつ接地を示す
              -- obs の非空性
              cases h_obs_cas : obs with
              | nil => simp only [h_obs_cas, List.length_nil, Nat.not_lt_zero] at h_below_lt
              | cons hd tl =>
                -- ofLayers obs = some s_obs
                set s_obs : Shape := ⟨hd :: tl, List.cons_ne_nil hd tl⟩
                have h_obs_of : Shape.ofLayers obs = some s_obs := by
                  rw [h_obs_cas]; rfl
                have h_layers_obs : s_obs.layers = obs := by
                  show (hd :: tl) = obs; exact h_obs_cas.symm
                -- s_result.layers = obs'
                have h_layers_res : s_result.layers = obs' := by
                  cases h_obs'_list : obs' with
                  | nil => simp only [Shape.ofLayers, h_obs'_list] at h_of; cases h_of
                  | cons hd' tl' =>
                    simp only [Shape.ofLayers, h_obs'_list] at h_of
                    exact (Option.some.inj h_of) ▸ rfl
                -- (p.layer-1, p.dir) は着地位置でない（pin は p.layer にしか着地しない）
                have h_below_not_landing : ∀ q ∈
                    (Gravity.FallingUnit.pin pos).positions,
                    ¬(q.layer - d = p.layer - 1 ∧ q.dir = p.dir) := by
                  simp only [Gravity.FallingUnit.positions, List.mem_singleton]
                  intro q h_eq ⟨h1, _⟩; subst h_eq; omega
                -- obs → obs' での quarter 保存
                have h_gd_below := Gravity.foldl_placeQuarter_getDir_preserved s obs
                    (Gravity.FallingUnit.pin pos).positions d
                    (p.layer - 1) p.dir h_below_not_landing
                -- obs での (p.layer-1) の非空性
                have h_obs_getD : obs.getD (p.layer - 1) Layer.empty =
                    obs[p.layer - 1] := by
                  simp only [List.getD, List.getElem?_eq_getElem h_below_lt,
                      Option.getD_some]
                have h_q_ne_empty : (QuarterPos.getDir obs[p.layer - 1] p.dir).isEmpty
                    = false := by
                  unfold Gravity.isOccupied at h_occ
                  simp only [List.getElem?_eq_getElem h_below_lt,
                      Bool.not_eq_true'] at h_occ
                  exact h_occ
                set q_below := QuarterPos.getDir obs[p.layer - 1] p.dir
                have h_q_ne_bool : !q_below.isEmpty = true := by
                  cases h_qb : q_below <;>
                    simp only [Quarter.isEmpty, h_qb, Bool.true_eq_false, Bool.false_eq_true, decide_false, Bool.not_false] at h_q_ne_empty ⊢
                -- getQuarter s_obs ⟨p.layer-1, p.dir⟩ = some q_below
                have h_gq_obs : (⟨p.layer - 1, p.dir⟩ : QuarterPos).getQuarter s_obs
                    = some q_below := by
                  show (match s_obs.layers[(p.layer - 1)]? with
                      | some l => some (QuarterPos.getDir l p.dir)
                      | none => none)
                      = some q_below
                  rw [h_layers_obs, List.getElem?_eq_getElem h_below_lt]
                -- h_inv で s_obs において接地
                have h_below_valid_obs : (p.layer - 1) < s_obs.layerCount := by
                  simp only [Shape.layerCount, h_layers_obs]; exact h_below_lt
                have h_grounded_obs : (⟨p.layer - 1, p.dir⟩ : QuarterPos) ∈
                    Gravity.groundedPositions s_obs :=
                  h_inv s_obs h_obs_of ⟨p.layer - 1, p.dir⟩ h_below_valid_obs
                      ⟨q_below, h_gq_obs, h_q_ne_bool⟩
                -- ★ groundedPositions_mono: s_obs → s_result
                have h_lc : s_obs.layerCount ≤ s_result.layerCount := by
                  simp only [Shape.layerCount, h_layers_obs, h_layers_res, h_obs'_def]
                  exact placeFallingUnit_length_ge s obs (.pin pos) d
                have h_gq_mono : ∀ p' : QuarterPos,
                    p'.layer < s_obs.layerCount →
                    (∃ q, p'.getQuarter s_obs = some q ∧ !q.isEmpty = true) →
                    p'.getQuarter s_result = p'.getQuarter s_obs := by
                  intro p' h_p'_valid h_p'_ne
                  by_cases h_p'_land :
                      ((Gravity.FallingUnit.pin pos).positions.any fun q =>
                          (q.layer - d) == p'.layer && q.dir == p'.dir) = true
                  · -- p' は着地位置 → h_empty_landing で obs 空 → 矛盾
                    rw [List.any_eq_true] at h_p'_land
                    obtain ⟨q_fu, h_q_mem, h_q_match⟩ := h_p'_land
                    have h_q_beq := Bool.and_eq_true_iff.mp h_q_match
                    have h_layer_eq : q_fu.layer - d = p'.layer :=
                        beq_iff_eq.mp h_q_beq.1
                    have h_dir_eq : q_fu.dir = p'.dir :=
                        beq_iff_eq.mp h_q_beq.2
                    have h_el := h_empty_landing q_fu h_q_mem
                    rw [h_layer_eq, h_dir_eq] at h_el
                    have h_p'_lt_obs : p'.layer < obs.length := by
                      simp only [Shape.layerCount, h_layers_obs] at h_p'_valid
                      exact h_p'_valid
                    have h_obs_getD_p' : obs.getD p'.layer Layer.empty =
                        obs[p'.layer] := by
                      simp only [List.getD,
                          List.getElem?_eq_getElem h_p'_lt_obs, Option.getD_some]
                    rw [h_obs_getD_p'] at h_el
                    have h_gq_obs_p' : p'.getQuarter s_obs =
                        some (QuarterPos.getDir obs[p'.layer] p'.dir) := by
                      simp only [QuarterPos.getQuarter, h_layers_obs,
                          List.getElem?_eq_getElem h_p'_lt_obs]
                    have h_q_empty : QuarterPos.getDir obs[p'.layer] p'.dir =
                        Quarter.empty := by
                      cases h_q : QuarterPos.getDir obs[p'.layer] p'.dir <;>
                        simp only [Quarter.isEmpty, h_q, Bool.false_eq_true] at h_el ⊢
                    rw [h_q_empty] at h_gq_obs_p'
                    obtain ⟨q', hq', hq'_ne⟩ := h_p'_ne
                    rw [h_gq_obs_p'] at hq'
                    have := Option.some.inj hq'; subst this
                    exact absurd hq'_ne (by native_decide)
                  · -- p' は非着地位置 → getQuarter 保存
                    have h_p'_not_land : ∀ q ∈
                        (Gravity.FallingUnit.pin pos).positions,
                        ¬(q.layer - d = p'.layer ∧ q.dir = p'.dir) := by
                      intro q h_q_mem ⟨h_lay, h_dir⟩
                      have : (Gravity.FallingUnit.pin pos).positions.any
                          (fun r => (r.layer - d) == p'.layer &&
                              r.dir == p'.dir) = true := by
                        rw [List.any_eq_true]
                        exact ⟨q, h_q_mem, by simp only [h_lay, BEq.rfl, h_dir, Bool.and_self]⟩
                      simp only [this, not_true_eq_false] at h_p'_land
                    have h_gd_p' :=
                        Gravity.foldl_placeQuarter_getDir_preserved s obs
                            (Gravity.FallingUnit.pin pos).positions d
                            p'.layer p'.dir h_p'_not_land
                    have h_p'_lt_obs : p'.layer < obs.length := by
                      simp only [Shape.layerCount, h_layers_obs] at h_p'_valid
                      exact h_p'_valid
                    have h_obs_getD_p' : obs.getD p'.layer Layer.empty =
                        obs[p'.layer] := by
                      simp only [List.getD,
                          List.getElem?_eq_getElem h_p'_lt_obs, Option.getD_some]
                    have h_obs'_valid_p' : p'.layer < obs'.length := by
                      rw [← h_layers_res]
                      exact Nat.lt_of_lt_of_le h_p'_valid h_lc
                    have h_obs'_getD_p' : obs'.getD p'.layer Layer.empty =
                        obs'[p'.layer] := by
                      simp only [List.getD,
                          List.getElem?_eq_getElem h_obs'_valid_p',
                          Option.getD_some]
                    have h_dir_eq_p' :
                        QuarterPos.getDir obs'[p'.layer] p'.dir =
                        QuarterPos.getDir obs[p'.layer] p'.dir := by
                      rw [← h_obs'_getD_p', ← h_obs_getD_p']; exact h_gd_p'
                    simp only [QuarterPos.getQuarter, h_layers_res, h_layers_obs,
                        List.getElem?_eq_getElem h_obs'_valid_p',
                        List.getElem?_eq_getElem h_p'_lt_obs, h_dir_eq_p']
                have h_grounded_res := groundedPositions_mono s_obs s_result
                    h_lc h_gq_mono h_grounded_obs
                -- (p.layer-1, p.dir) の s_result での quarter（h_gq_mono で直接取得）
                have h_gq_res : (⟨p.layer - 1, p.dir⟩ : QuarterPos).getQuarter
                    s_result = some q_below := by
                  rw [h_gq_mono ⟨p.layer - 1, p.dir⟩ h_below_valid_obs
                      ⟨q_below, h_gq_obs, h_q_ne_bool⟩]
                  exact h_gq_obs
                exact ⟨q_below, h_gq_res, h_q_ne_bool, h_grounded_res⟩
    · -- ★ Case B: p は FU 着地位置でない
      -- h_mod を = false 形式に変換
      have h_mod_false : (u.positions.any fun q =>
              (q.layer - d) == p.layer && q.dir == p.dir) = false :=
          Bool.eq_false_iff.mpr h_mod
      have h_not_landing : ∀ q ∈ u.positions, ¬(q.layer - d = p.layer ∧ q.dir = p.dir) := by
          intro q h_q_mem ⟨h_lay, h_dir⟩
          have : u.positions.any (fun r => (r.layer - d) == p.layer && r.dir == p.dir) = true := by
              rw [List.any_eq_true]
              refine ⟨q, h_q_mem, ?_⟩
              show ((q.layer - d) == p.layer && q.dir == p.dir) = true
              simp only [h_lay, h_dir, beq_self_eq_true, Bool.and_self]
          simp only [this] at h_mod_false
          exact absurd h_mod_false (by decide)
      -- obs が非空であることを確認（空なら非FU位置は全て empty → h_ne と矛盾）
      cases h_obs_ne : obs with
      | nil =>
          -- obs = [] → 非FU位置は全て Quarter.empty → 非空矛盾
          exfalso
          -- foldl_placeQuarter_getDir_preserved で非FU位置の getDir が保存されることを示す
          -- obs を渡す（obs' は obs を含む let 束縛のため定義的に一致する）
          have h_gd := Gravity.foldl_placeQuarter_getDir_preserved s obs u.positions d
              p.layer p.dir h_not_landing
          -- obs.getD = [].getD = Layer.empty (h_obs_ne から)
          have h_obs_gd : obs.getD p.layer Layer.empty = (Layer.empty : Layer) := by
              simp only [h_obs_ne, List.getD, List.getElem?_nil, Option.getD_none]
          have h_empty_dir : QuarterPos.getDir (Layer.empty : Layer) p.dir = Quarter.empty :=
              by cases p.dir <;> rfl
          rw [h_obs_gd, h_empty_dir] at h_gd
          -- h_gd : getDir (obs'.getD p.layer Layer.empty) p.dir = Quarter.empty
          -- s_result.layers = obs' (ofLayers obs' = some s_result)
          have h_layers : s_result.layers = obs' := by
              cases h_obs'_list : obs' with
              | nil => simp only [Shape.ofLayers, h_obs'_list] at h_of; cases h_of
              | cons hd tl =>
                  simp only [Shape.ofLayers, h_obs'_list] at h_of
                  exact (Option.some.inj h_of) ▸ rfl
          -- p.layer < obs'.length
          have h_obs'_valid : p.layer < obs'.length := by
              rw [← h_layers]; exact h_valid
          -- obs'.getD = obs'[p.layer] (有効インデックス)
          have h_getD_eq : obs'.getD p.layer Layer.empty = obs'[p.layer] := by
              simp only [List.getD, List.getElem?_eq_getElem h_obs'_valid, Option.getD_some]
          -- getDir obs'[p.layer] p.dir = Quarter.empty
          have h_qe : QuarterPos.getDir obs'[p.layer] p.dir = Quarter.empty := by
              rw [← h_getD_eq]; exact h_gd
          -- getQuarter s_result p = some Quarter.empty
          have h_gq : p.getQuarter s_result = some Quarter.empty := by
              simp only [QuarterPos.getQuarter, h_layers,
                  List.getElem?_eq_getElem h_obs'_valid, h_qe]
          -- h_ne と矛盾: Quarter.empty.isEmpty = true → !true = false ≠ true
          obtain ⟨q, hq, hq_ne⟩ := h_ne
          rw [h_gq] at hq
          have := Option.some.inj hq; subst this
          exact absurd hq_ne (by native_decide)
      | cons hd tl =>
          -- obs = hd :: tl → ofLayers obs = some s_obs
          have h_obs_of : Shape.ofLayers obs = some ⟨hd :: tl, List.cons_ne_nil hd tl⟩ := by
              simp only [Shape.ofLayers, h_obs_ne]
          set s_obs : Shape := ⟨hd :: tl, List.cons_ne_nil hd tl⟩
          -- s_result.layers = obs' (ofLayers 抽出)
          have h_layers_res : s_result.layers = obs' := by
              cases h_obs'_list : obs' with
              | nil => simp only [Shape.ofLayers, h_obs'_list] at h_of; cases h_of
              | cons hd' tl' =>
                  simp only [Shape.ofLayers, h_obs'_list] at h_of
                  exact (Option.some.inj h_of) ▸ rfl
          -- p.layer < obs.length（範囲外なら Quarter.empty で h_ne と矛盾）
          have h_p_lt_obs : p.layer < obs.length := by
              by_contra h_ge
              simp only [not_lt] at h_ge
              have h_gd := Gravity.foldl_placeQuarter_getDir_preserved s obs u.positions d
                  p.layer p.dir h_not_landing
              have : obs.getD p.layer Layer.empty = Layer.empty := by
                  simp only [List.getD, List.getElem?_eq_none_iff.mpr (by omega),
                      Option.getD_none]
              have h_ed : QuarterPos.getDir (Layer.empty : Layer) p.dir = Quarter.empty :=
                  by cases p.dir <;> rfl
              rw [this, h_ed] at h_gd
              have h_obs'_valid : p.layer < obs'.length := by
                  rw [← h_layers_res]; exact h_valid
              have h_getD_eq : obs'.getD p.layer Layer.empty = obs'[p.layer] := by
                  simp only [List.getD, List.getElem?_eq_getElem h_obs'_valid, Option.getD_some]
              have h_qe : QuarterPos.getDir obs'[p.layer] p.dir = Quarter.empty := by
                  rw [← h_getD_eq]; exact h_gd
              have h_gq : p.getQuarter s_result = some Quarter.empty := by
                  simp only [QuarterPos.getQuarter, h_layers_res,
                      List.getElem?_eq_getElem h_obs'_valid, h_qe]
              obtain ⟨q, hq, hq_ne⟩ := h_ne
              rw [h_gq] at hq
              have := Option.some.inj hq; subst this
              exact absurd hq_ne (by native_decide)
          -- getQuarter s_obs p = getQuarter s_result p（非着地位置で保存）
          have h_gq_eq : p.getQuarter s_result = p.getQuarter s_obs := by
              have h_gd := Gravity.foldl_placeQuarter_getDir_preserved s obs u.positions d
                  p.layer p.dir h_not_landing
              have h_obs_getD : obs.getD p.layer Layer.empty = obs[p.layer] := by
                  simp only [List.getD, List.getElem?_eq_getElem h_p_lt_obs, Option.getD_some]
              have h_obs'_valid : p.layer < obs'.length := by
                  rw [← h_layers_res]; exact h_valid
              have h_obs'_getD : obs'.getD p.layer Layer.empty = obs'[p.layer] := by
                  simp only [List.getD, List.getElem?_eq_getElem h_obs'_valid, Option.getD_some]
              have h_dir_eq : QuarterPos.getDir obs'[p.layer] p.dir =
                      QuarterPos.getDir obs[p.layer] p.dir := by
                  rw [← h_obs'_getD, ← h_obs_getD]; exact h_gd
              have h_layers_obs : s_obs.layers = obs := rfl.trans h_obs_ne.symm
              simp only [QuarterPos.getQuarter, h_layers_res, h_layers_obs,
                  List.getElem?_eq_getElem h_obs'_valid,
                  List.getElem?_eq_getElem h_p_lt_obs, h_dir_eq]
          -- p は s_obs で非空 → h_inv で s_obs で接地
          have h_ne_obs : ∃ q, p.getQuarter s_obs = some q ∧ !q.isEmpty = true := by
              rw [← h_gq_eq]; exact h_ne
          have h_p_valid_obs : p.layer < s_obs.layerCount := by
              show p.layer < (hd :: tl).length
              rw [h_obs_ne.symm]; exact h_p_lt_obs
          have h_p_grounded_obs : p ∈ Gravity.groundedPositions s_obs :=
              h_inv s_obs h_obs_of p h_p_valid_obs h_ne_obs
          -- ★ groundedPositions s_obs ⊆ groundedPositions s_result
          -- h_empty_landing により着地位置は obs で空 → 全 non-empty 位置で getQuarter 保存
          -- → groundedPositions_mono 適用可能
          have h_layers_obs : s_obs.layers = obs := rfl.trans h_obs_ne.symm
          have h_lc : s_obs.layerCount ≤ s_result.layerCount := by
              show (hd :: tl).length ≤ s_result.layerCount
              rw [h_obs_ne.symm]
              show obs.length ≤ s_result.layerCount
              simp only [Shape.layerCount, h_layers_res, h_obs'_def]
              exact placeFallingUnit_length_ge s obs u d
          have h_gq_mono : ∀ p' : QuarterPos, p'.layer < s_obs.layerCount →
              (∃ q, p'.getQuarter s_obs = some q ∧ !q.isEmpty = true) →
              p'.getQuarter s_result = p'.getQuarter s_obs := by
            intro p' h_p'_valid h_p'_ne
            -- p' が着地位置かどうかで場合分け
            by_cases h_p'_landing :
                (u.positions.any fun q => (q.layer - d) == p'.layer && q.dir == p'.dir) = true
            · -- p' は着地位置 → h_empty_landing より obs で空 → s_obs で空 → non-empty 矛盾
              rw [List.any_eq_true] at h_p'_landing
              obtain ⟨q_fu, h_q_mem, h_q_match⟩ := h_p'_landing
              have h_q_beq := Bool.and_eq_true_iff.mp h_q_match
              have h_layer_eq : q_fu.layer - d = p'.layer := by
                  exact beq_iff_eq.mp h_q_beq.1
              have h_dir_eq : q_fu.dir = p'.dir := by
                  exact beq_iff_eq.mp h_q_beq.2
              -- h_empty_landing: getDir (obs.getD (q_fu.layer - d) Layer.empty) q_fu.dir .isEmpty = true
              have h_el := h_empty_landing q_fu h_q_mem
              rw [h_layer_eq, h_dir_eq] at h_el
              -- obs.getD p'.layer Layer.empty の p'.dir 方角が empty
              have h_p'_lt_obs : p'.layer < obs.length := by
                  rw [h_layers_obs.symm]; exact h_p'_valid
              have h_obs_getD : obs.getD p'.layer Layer.empty = obs[p'.layer] := by
                  simp only [List.getD, List.getElem?_eq_getElem h_p'_lt_obs, Option.getD_some]
              rw [h_obs_getD] at h_el
              -- getQuarter s_obs p' = some (getDir obs[p'.layer] p'.dir)
              have h_gq_obs : p'.getQuarter s_obs =
                  some (QuarterPos.getDir obs[p'.layer] p'.dir) := by
                simp only [QuarterPos.getQuarter, h_layers_obs,
                    List.getElem?_eq_getElem h_p'_lt_obs]
              -- getDir obs[p'.layer] p'.dir = Quarter.empty (from isEmpty = true)
              have h_q_empty : QuarterPos.getDir obs[p'.layer] p'.dir = Quarter.empty := by
                cases h_q : QuarterPos.getDir obs[p'.layer] p'.dir <;>
                  simp only [Quarter.isEmpty, h_q, Bool.false_eq_true] at h_el ⊢
              rw [h_q_empty] at h_gq_obs
              -- p'.getQuarter s_obs = some .empty → non-empty 仮説と矛盾
              obtain ⟨q', hq', hq'_ne⟩ := h_p'_ne
              rw [h_gq_obs] at hq'
              have := Option.some.inj hq'; subst this
              exact absurd hq'_ne (by native_decide)
            · -- p' は非着地位置 → getQuarter 保存（foldl_placeQuarter_getDir_preserved）
              have h_p'_not_landing : ∀ q ∈ u.positions,
                  ¬(q.layer - d = p'.layer ∧ q.dir = p'.dir) := by
                intro q h_q_mem ⟨h_lay, h_dir⟩
                have : u.positions.any (fun r =>
                    (r.layer - d) == p'.layer && r.dir == p'.dir) = true := by
                  rw [List.any_eq_true]
                  exact ⟨q, h_q_mem, by simp only [h_lay, BEq.rfl, h_dir, Bool.and_self]⟩
                simp only [this, not_true_eq_false] at h_p'_landing
              have h_gd := Gravity.foldl_placeQuarter_getDir_preserved s obs u.positions d
                  p'.layer p'.dir h_p'_not_landing
              have h_p'_lt_obs : p'.layer < obs.length := by
                  rw [h_layers_obs.symm]; exact h_p'_valid
              have h_obs_getD_p' : obs.getD p'.layer Layer.empty = obs[p'.layer] := by
                  simp only [List.getD, List.getElem?_eq_getElem h_p'_lt_obs, Option.getD_some]
              have h_obs'_valid_p' : p'.layer < obs'.length := by
                  rw [← h_layers_res]; exact (Nat.lt_of_lt_of_le h_p'_valid h_lc)
              have h_obs'_getD_p' : obs'.getD p'.layer Layer.empty = obs'[p'.layer] := by
                  simp only [List.getD, List.getElem?_eq_getElem h_obs'_valid_p', Option.getD_some]
              have h_dir_eq_p' : QuarterPos.getDir obs'[p'.layer] p'.dir =
                      QuarterPos.getDir obs[p'.layer] p'.dir := by
                  rw [← h_obs'_getD_p', ← h_obs_getD_p']; exact h_gd
              simp only [QuarterPos.getQuarter, h_layers_res, h_layers_obs,
                  List.getElem?_eq_getElem h_obs'_valid_p',
                  List.getElem?_eq_getElem h_p'_lt_obs, h_dir_eq_p']
          exact groundedPositions_mono s_obs s_result h_lc h_gq_mono h_p_grounded_obs

/-- canFormBond → 非空 -/
private theorem canFormBond_implies_not_empty (q : Quarter)
        (h : q.canFormBond = true) : q.isEmpty = false := by
    cases q <;> simp only [Quarter.canFormBond, Bool.false_eq_true, Quarter.isEmpty] at h ⊢

/-- isStructurallyBonded から隣接条件（layer/dir のみ依存）を抽出 -/
private theorem isStructurallyBonded_adjacency (s : Shape) (a b : QuarterPos)
        (h : Gravity.isStructurallyBonded s a b = true) :
        (a.layer == b.layer && a.dir.adjacent b.dir ||
            LayerIndex.verticallyAdjacent a.layer b.layer &&
            a.dir == b.dir) = true := by
    have h_gc := Gravity.isStructurallyBonded_implies_isGroundingContact s a b h
    obtain ⟨q1, q2, hq1, hq2, _, _⟩ := Gravity.isGroundingContact_nonEmpty s a b h_gc
    simp only [Gravity.isStructurallyBonded, hq1, hq2, Bool.and_eq_true] at h
    exact h.2

/-- isStructurallyBonded から左端点の canFormBond を抽出 -/
private theorem isStructurallyBonded_canFormBond_left (s : Shape) (a b : QuarterPos)
        (h : Gravity.isStructurallyBonded s a b = true) :
        ∃ qa, a.getQuarter s = some qa ∧ qa.canFormBond = true := by
    have h_gc := Gravity.isStructurallyBonded_implies_isGroundingContact s a b h
    obtain ⟨q1, q2, hq1, hq2, _, _⟩ := Gravity.isGroundingContact_nonEmpty s a b h_gc
    simp only [Gravity.isStructurallyBonded, hq1, hq2, Bool.and_eq_true] at h
    exact ⟨q1, hq1, h.1.1⟩

/-- isStructurallyBonded から右端点の canFormBond を抽出 -/
private theorem isStructurallyBonded_canFormBond_right (s : Shape) (a b : QuarterPos)
        (h : Gravity.isStructurallyBonded s a b = true) :
        ∃ qb, b.getQuarter s = some qb ∧ qb.canFormBond = true := by
    have h_gc := Gravity.isStructurallyBonded_implies_isGroundingContact s a b h
    obtain ⟨q1, q2, hq1, hq2, _, _⟩ := Gravity.isGroundingContact_nonEmpty s a b h_gc
    simp only [Gravity.isStructurallyBonded, hq1, hq2, Bool.and_eq_true] at h
    exact ⟨q2, hq2, h.1.2⟩

/-- canFormBond + 隣接条件から isStructurallyBonded を再構成 -/
private theorem isStructurallyBonded_of_parts (s : Shape) (a b : QuarterPos)
        (qa qb : Quarter)
        (ha : a.getQuarter s = some qa) (hb : b.getQuarter s = some qb)
        (ha_cb : qa.canFormBond = true) (hb_cb : qb.canFormBond = true)
        (h_adj : (a.layer == b.layer && a.dir.adjacent b.dir ||
            LayerIndex.verticallyAdjacent a.layer b.layer &&
            a.dir == b.dir) = true) :
        Gravity.isStructurallyBonded s a b = true := by
    simp only [Gravity.isStructurallyBonded, ha, hb, ha_cb, hb_cb, Bool.true_and]
    exact h_adj

/-- isGroundingContact の edge monotonicity: 一方の象限が canFormBond に変わっても
    元のエッジは保存される（canFormBond 象限は非ピンなので水平エッジも保存） -/
private theorem isGroundingContact_mono_canFormBond_left
        (s1 s2 : Shape) (a b : QuarterPos)
        (qa_new : Quarter) (h_bond : qa_new.canFormBond = true)
        (h_a_new : a.getQuarter s2 = some qa_new)
        (h_b_eq : b.getQuarter s2 = b.getQuarter s1)
        (h_gc : Gravity.isGroundingContact s1 a b = true) :
        Gravity.isGroundingContact s2 a b = true := by
    obtain ⟨q1, q2, hq1, hq2, hne1, hne2⟩ :=
        Gravity.isGroundingContact_nonEmpty s1 a b h_gc
    have hq2' : b.getQuarter s2 = some q2 := by rw [h_b_eq, hq2]
    unfold Gravity.isGroundingContact at h_gc ⊢
    rw [hq1, hq2] at h_gc
    rw [h_a_new, hq2']
    have h_ne_new := canFormBond_implies_not_empty qa_new h_bond
    simp only [hne1, h_ne_new, hne2, Bool.not_false, Bool.true_and] at h_gc ⊢
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h_gc ⊢
    rcases h_gc with h_vert | ⟨⟨h_layer, h_adj⟩, h_match⟩
    · left; exact h_vert
    · right
      have h_qa_not_pin : qa_new ≠ .pin := by
          intro h; subst h; simp only [Quarter.canFormBond, Bool.false_eq_true] at h_bond
      have h_q2_not_pin : q2 ≠ .pin := by
          intro h; subst h; cases q1 <;> simp only [Bool.false_eq_true] at h_match
      refine ⟨⟨h_layer, h_adj⟩, ?_⟩
      clear h_match hne1 hne2 hq1 hq2 hq2' q1
      cases qa_new <;> cases q2 <;>
          simp_all only [beq_iff_eq, Quarter.canFormBond, Bool.false_eq_true, Quarter.isEmpty, ne_eq, reduceCtorEq, not_false_eq_true, not_true_eq_false]

/-- isGroundingContact の edge monotonicity（右象限がcanFormBond に変更） -/
private theorem isGroundingContact_mono_canFormBond_right
        (s1 s2 : Shape) (a b : QuarterPos)
        (qb_new : Quarter) (h_bond : qb_new.canFormBond = true)
        (h_a_eq : a.getQuarter s2 = a.getQuarter s1)
        (h_b_new : b.getQuarter s2 = some qb_new)
        (h_gc : Gravity.isGroundingContact s1 a b = true) :
        Gravity.isGroundingContact s2 a b = true := by
    obtain ⟨q1, q2, hq1, hq2, hne1, hne2⟩ :=
        Gravity.isGroundingContact_nonEmpty s1 a b h_gc
    have hq1' : a.getQuarter s2 = some q1 := by rw [h_a_eq, hq1]
    unfold Gravity.isGroundingContact at h_gc ⊢
    rw [hq1, hq2] at h_gc
    rw [hq1', h_b_new]
    have h_ne_new := canFormBond_implies_not_empty qb_new h_bond
    simp only [hne1, hne2, h_ne_new, Bool.not_false, Bool.true_and] at h_gc ⊢
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h_gc ⊢
    rcases h_gc with h_vert | ⟨⟨h_layer, h_adj⟩, h_match⟩
    · left; exact h_vert
    · right
      have h_q1_not_pin : q1 ≠ .pin := by
          intro h; subst h; cases q2 <;> simp only [Bool.false_eq_true] at h_match
      have h_qb_not_pin : qb_new ≠ .pin := by
          intro h; subst h; simp only [Quarter.canFormBond, Bool.false_eq_true] at h_bond
      refine ⟨⟨h_layer, h_adj⟩, ?_⟩
      clear h_match hne1 hne2 hq1 hq2 hq1' q2
      cases q1 <;> cases qb_new <;>
          simp_all only [beq_iff_eq, ne_eq, not_false_eq_true, Quarter.canFormBond, Bool.false_eq_true, reduceCtorEq, Quarter.isEmpty, not_true_eq_false]

/-- isGroundingContact の edge monotonicity（両方の象限がcanFormBond に変更） -/
private theorem isGroundingContact_mono_canFormBond_both
        (s1 s2 : Shape) (a b : QuarterPos)
        (qa_new qb_new : Quarter)
        (h_bond_a : qa_new.canFormBond = true)
        (h_bond_b : qb_new.canFormBond = true)
        (h_a_new : a.getQuarter s2 = some qa_new)
        (h_b_new : b.getQuarter s2 = some qb_new)
        (h_gc : Gravity.isGroundingContact s1 a b = true) :
        Gravity.isGroundingContact s2 a b = true := by
    obtain ⟨q1, q2, hq1, hq2, hne1, hne2⟩ :=
        Gravity.isGroundingContact_nonEmpty s1 a b h_gc
    unfold Gravity.isGroundingContact at h_gc ⊢
    rw [hq1, hq2] at h_gc
    rw [h_a_new, h_b_new]
    have h_ne_a := canFormBond_implies_not_empty qa_new h_bond_a
    have h_ne_b := canFormBond_implies_not_empty qb_new h_bond_b
    simp only [hne1, hne2, h_ne_a, h_ne_b, Bool.not_false, Bool.true_and]
        at h_gc ⊢
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h_gc ⊢
    rcases h_gc with h_vert | ⟨⟨h_layer, h_adj⟩, h_match⟩
    · left; exact h_vert
    · right
      have h_qa_not_pin : qa_new ≠ .pin := by
          intro h; subst h; simp only [Quarter.canFormBond, Bool.false_eq_true] at h_bond_a
      have h_qb_not_pin : qb_new ≠ .pin := by
          intro h; subst h; simp only [Quarter.canFormBond, Bool.false_eq_true] at h_bond_b
      refine ⟨⟨h_layer, h_adj⟩, ?_⟩
      clear h_match hne1 hne2 hq1 hq2 q1 q2
      cases qa_new <;> cases qb_new <;>
          simp_all only [beq_iff_eq, Quarter.canFormBond, Bool.false_eq_true, Quarter.isEmpty, ne_eq, reduceCtorEq, not_false_eq_true]

/-- 非空着地ケース（d ≤ 1）でのクラスタ FU 配置の接地不変量保存。
    edge monotonicity + cluster connectivity で AllNonEmptyGrounded を証明する。 -/
private theorem one_step_all_grounded_cluster_nonempty_landing
        (s : Shape) (obs : List Layer) (ps : List QuarterPos) (d : Nat)
        (h_inv : AllNonEmptyGrounded obs)
        (h_obs_ne : obs ≠ [])
        (h_ps_ne : ps ≠ [])
        (h_d_eq : d = Gravity.landingDistance (.cluster ps) obs)
        (h_d_le_min : d ≤ (Gravity.FallingUnit.cluster ps).minLayer)
        (h_cluster_bond : ∀ q ∈ ps,
            ∃ qv, q.getQuarter s = some qv ∧ qv.canFormBond = true)
        (h_cluster_closed : ∀ q ∈ ps,
            ∀ r, Gravity.isStructurallyBonded s q r = true → r ∈ ps)
        (h_connected : ∀ q1 ∈ ps, ∀ q2 ∈ ps,
            GenericReachable (Gravity.isStructurallyBonded s) q1 q2) :
        AllNonEmptyGrounded (Gravity.placeFallingUnit s obs (.cluster ps) d) := by
    set obs' := Gravity.placeFallingUnit s obs (.cluster ps) d with h_obs'_def
    intro s_result h_of p h_valid h_ne
    -- s_obs の構築
    cases h_obs_cas : obs with
    | nil => exact absurd h_obs_cas h_obs_ne
    | cons obs_hd obs_tl =>
      set s_obs : Shape := ⟨obs_hd :: obs_tl, List.cons_ne_nil obs_hd obs_tl⟩
      have h_obs_of : Shape.ofLayers obs = some s_obs := by rw [h_obs_cas]; rfl
      have h_layers_obs : s_obs.layers = obs := h_obs_cas.symm
      have h_layers : s_result.layers = obs' := by
          cases h_obs'_list : obs' with
          | nil => simp only [Shape.ofLayers, h_obs'_list] at h_of; cases h_of
          | cons hd tl =>
              simp only [Shape.ofLayers, h_obs'_list] at h_of
              exact (Option.some.inj h_of) ▸ rfl
      have h_lc : s_obs.layerCount ≤ s_result.layerCount := by
          simp only [Shape.layerCount, h_layers_obs, h_layers, h_obs'_def]
          exact placeFallingUnit_length_ge s obs (.cluster ps) d
      -- ★ getQuarter 保存ヘルパー (非着地位置)
      have h_gq_preserved : ∀ (a : QuarterPos),
          a.layer < s_obs.layerCount →
          (∀ q ∈ (Gravity.FallingUnit.cluster ps).positions,
              ¬(q.layer - d = a.layer ∧ q.dir = a.dir)) →
          a.getQuarter s_result = a.getQuarter s_obs := by
        intro a h_a_valid h_not
        have h_a_lt_obs : a.layer < obs.length := by
            simp only [Shape.layerCount, h_layers_obs] at h_a_valid; exact h_a_valid
        have h_a_lt_obs' : a.layer < obs'.length :=
            Nat.lt_of_lt_of_le h_a_lt_obs
                (placeFallingUnit_length_ge s obs (.cluster ps) d)
        have h_gd := Gravity.foldl_placeQuarter_getDir_preserved
            s obs (Gravity.FallingUnit.cluster ps).positions d
            a.layer a.dir h_not
        change QuarterPos.getDir (obs'.getD a.layer Layer.empty)
            a.dir = QuarterPos.getDir (obs.getD a.layer Layer.empty) a.dir at h_gd
        have h_obs_getD : obs.getD a.layer Layer.empty = obs[a.layer] := by
            simp only [List.getD, List.getElem?_eq_getElem h_a_lt_obs, Option.getD_some]
        have h_obs'_getD : obs'.getD a.layer Layer.empty = obs'[a.layer] := by
            simp only [List.getD, List.getElem?_eq_getElem h_a_lt_obs', Option.getD_some]
        rw [h_obs'_getD, h_obs_getD] at h_gd
        simp only [QuarterPos.getQuarter, h_layers, h_layers_obs,
            List.getElem?_eq_getElem h_a_lt_obs', List.getElem?_eq_getElem h_a_lt_obs,
            h_gd]
      -- ★ getQuarter canFormBond ヘルパー (着地位置)
      have h_gq_canFormBond : ∀ (a : QuarterPos),
          (∃ q ∈ ps, q.layer - d = a.layer ∧ q.dir = a.dir) →
          a.layer < obs'.length →
          ∃ qa_new, a.getQuarter s_result = some qa_new ∧
              qa_new.canFormBond = true := by
        intro a ⟨q, hq_mem, hq_lay, hq_dir⟩ h_a_lt_obs'
        have h_foldl := Gravity.foldl_placeQuarter_written_canFormBond
            s obs ps d a.layer a.dir
            ⟨q, hq_mem, hq_lay, hq_dir⟩ h_cluster_bond
        obtain ⟨qv, h_gd_res, h_bond⟩ := h_foldl
        change QuarterPos.getDir (obs'.getD a.layer Layer.empty) a.dir = qv at h_gd_res
        have h_obs'_getD : obs'.getD a.layer Layer.empty = obs'[a.layer] := by
            simp only [List.getD, List.getElem?_eq_getElem h_a_lt_obs', Option.getD_some]
        rw [h_obs'_getD] at h_gd_res
        exact ⟨qv, by simp only [QuarterPos.getQuarter, h_layers,
            List.getElem?_eq_getElem h_a_lt_obs', h_gd_res], h_bond⟩
      -- ★ Edge monotonicity: s_obs → s_result
      have h_gc_mono : ∀ a b,
          Gravity.isGroundingContact s_obs a b = true →
          Gravity.isGroundingContact s_result a b = true := by
        intro a b h_gc
        have h_a_valid := layer_lt_of_isGroundingContact_left s_obs a b h_gc
        have h_b_valid := layer_lt_of_isGroundingContact_right s_obs a b h_gc
        have h_a_lt_obs : a.layer < obs.length := by
            simp only [Shape.layerCount, h_layers_obs] at h_a_valid; exact h_a_valid
        have h_b_lt_obs : b.layer < obs.length := by
            simp only [Shape.layerCount, h_layers_obs] at h_b_valid; exact h_b_valid
        have h_a_lt_obs' : a.layer < obs'.length :=
            Nat.lt_of_lt_of_le h_a_lt_obs
                (placeFallingUnit_length_ge s obs (.cluster ps) d)
        have h_b_lt_obs' : b.layer < obs'.length :=
            Nat.lt_of_lt_of_le h_b_lt_obs
                (placeFallingUnit_length_ge s obs (.cluster ps) d)
        by_cases h_a_land : ∃ q ∈ ps, q.layer - d = a.layer ∧ q.dir = a.dir
        <;> by_cases h_b_land : ∃ q ∈ ps, q.layer - d = b.layer ∧ q.dir = b.dir
        · -- 両方着地
          obtain ⟨qa_new, ha_gq, ha_bond⟩ :=
              h_gq_canFormBond a h_a_land h_a_lt_obs'
          obtain ⟨qb_new, hb_gq, hb_bond⟩ :=
              h_gq_canFormBond b h_b_land h_b_lt_obs'
          exact isGroundingContact_mono_canFormBond_both s_obs s_result a b
              qa_new qb_new ha_bond hb_bond ha_gq hb_gq h_gc
        · -- a 着地, b 非着地
          obtain ⟨qa_new, ha_gq, ha_bond⟩ :=
              h_gq_canFormBond a h_a_land h_a_lt_obs'
          have hb_gq := h_gq_preserved b h_b_valid
              (fun q hq hpq => h_b_land ⟨q, hq, hpq⟩)
          exact isGroundingContact_mono_canFormBond_left s_obs s_result a b
              qa_new ha_bond ha_gq hb_gq h_gc
        · -- a 非着地, b 着地
          have ha_gq := h_gq_preserved a h_a_valid
              (fun q hq hpq => h_a_land ⟨q, hq, hpq⟩)
          obtain ⟨qb_new, hb_gq, hb_bond⟩ :=
              h_gq_canFormBond b h_b_land h_b_lt_obs'
          exact isGroundingContact_mono_canFormBond_right s_obs s_result a b
              qb_new hb_bond ha_gq hb_gq h_gc
        · -- 両方非着地
          have ha_gq := h_gq_preserved a h_a_valid
              (fun q hq hpq => h_a_land ⟨q, hq, hpq⟩)
          have hb_gq := h_gq_preserved b h_b_valid
              (fun q hq hpq => h_b_land ⟨q, hq, hpq⟩)
          rw [← isGroundingContact_eq_of_getQuarter_eq s_obs s_result a b
              ha_gq.symm hb_gq.symm]
          exact h_gc
      -- ★ groundingEdge monotonicity (isGroundingContact + isStructurallyBonded)
      have h_ge_mono : ∀ a b, Gravity.groundingEdge s_obs a b = true →
          Gravity.groundingEdge s_result a b = true := by
        intro a b h_ge
        simp only [Gravity.groundingEdge, Bool.or_eq_true] at h_ge ⊢
        rcases h_ge with h_up | h_sb
        · -- isUpwardGroundingContact: layer condition + isGroundingContact
          left
          simp only [Gravity.isUpwardGroundingContact, Bool.and_eq_true] at h_up ⊢
          exact ⟨h_gc_mono a b h_up.1, h_up.2⟩
        · -- isStructurallyBonded: canFormBond + 隣接条件の保存
          right
          have h_gc := Gravity.groundingEdge_base
              (show Gravity.groundingEdge s_obs a b = true by
                  simp only [Gravity.groundingEdge, h_sb, Bool.or_true])
          have h_a_valid := layer_lt_of_isGroundingContact_left s_obs a b h_gc
          have h_b_valid := layer_lt_of_isGroundingContact_right s_obs a b h_gc
          have h_a_lt_obs' : a.layer < obs'.length :=
              Nat.lt_of_lt_of_le
                  (by simp only [Shape.layerCount, h_layers_obs] at h_a_valid
                      exact h_a_valid)
                  (placeFallingUnit_length_ge s obs (.cluster ps) d)
          have h_b_lt_obs' : b.layer < obs'.length :=
              Nat.lt_of_lt_of_le
                  (by simp only [Shape.layerCount, h_layers_obs] at h_b_valid
                      exact h_b_valid)
                  (placeFallingUnit_length_ge s obs (.cluster ps) d)
          have h_adj := isStructurallyBonded_adjacency s_obs a b h_sb
          have ⟨qa_r, ha_r, ha_cb⟩ :
              ∃ qa, a.getQuarter s_result = some qa ∧
                  qa.canFormBond = true := by
            by_cases h_a_land : ∃ q ∈ ps, q.layer - d = a.layer ∧ q.dir = a.dir
            · exact h_gq_canFormBond a h_a_land h_a_lt_obs'
            · have ha_gq := h_gq_preserved a h_a_valid
                  (fun q hq hpq => h_a_land ⟨q, hq, hpq⟩)
              obtain ⟨qa, ha, ha_cb⟩ :=
                  isStructurallyBonded_canFormBond_left s_obs a b h_sb
              exact ⟨qa, ha_gq.trans ha, ha_cb⟩
          have ⟨qb_r, hb_r, hb_cb⟩ :
              ∃ qb, b.getQuarter s_result = some qb ∧
                  qb.canFormBond = true := by
            by_cases h_b_land : ∃ q ∈ ps, q.layer - d = b.layer ∧ q.dir = b.dir
            · exact h_gq_canFormBond b h_b_land h_b_lt_obs'
            · have hb_gq := h_gq_preserved b h_b_valid
                  (fun q hq hpq => h_b_land ⟨q, hq, hpq⟩)
              obtain ⟨qb, hb, hb_cb⟩ :=
                  isStructurallyBonded_canFormBond_right s_obs a b h_sb
              exact ⟨qb, hb_gq.trans hb, hb_cb⟩
          exact isStructurallyBonded_of_parts s_result a b
              qa_r qb_r ha_r hb_r ha_cb hb_cb h_adj
      -- ★ Seed 保存
      have h_seed_ne : ∀ p' : QuarterPos, p'.layer = 0 →
          p'.layer < s_obs.layerCount →
          (∃ q, p'.getQuarter s_obs = some q ∧ !q.isEmpty = true) →
          ∃ q, p'.getQuarter s_result = some q ∧ !q.isEmpty = true := by
        intro p' h_p0 h_p_valid ⟨q_old, hq_old, hq_ne⟩
        by_cases h_p_land : ∃ q ∈ ps, q.layer - d = p'.layer ∧ q.dir = p'.dir
        · -- 着地位置: canFormBond 象限は非空
          have h_p_lt_obs' : p'.layer < obs'.length :=
              Nat.lt_of_lt_of_le
                  (by simp only [Shape.layerCount, h_layers_obs] at h_p_valid
                      exact h_p_valid)
                  (placeFallingUnit_length_ge s obs (.cluster ps) d)
          obtain ⟨qa_new, ha_gq, ha_bond⟩ :=
              h_gq_canFormBond p' h_p_land h_p_lt_obs'
          exact ⟨qa_new, ha_gq,
              by have := canFormBond_implies_not_empty qa_new ha_bond
                 cases qa_new <;> simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, Quarter.isEmpty, Bool.decide_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, not_and, forall_exists_index, and_imp, Bool.true_eq_false, Bool.false_eq_true, decide_false, Bool.not_false]⟩
        · -- 非着地位置: 保存
          have h_p_gq := h_gq_preserved p' h_p_valid
              (fun q hq hpq => h_p_land ⟨q, hq, hpq⟩)
          exact ⟨q_old, by rw [h_p_gq]; exact hq_old, hq_ne⟩
      -- ★ groundedPositions の包含 (s_obs → s_result)
      have h_grounded_subset :
          Gravity.groundedPositions s_obs ⊆ Gravity.groundedPositions s_result :=
          groundedPositions_mono_of_edge s_obs s_result h_lc h_seed_ne h_ge_mono
      -- ★ p が着地位置かどうかで場合分け
      by_cases h_p_mod :
          (ps.any fun q => (q.layer - d) == p.layer && q.dir == p.dir) = true
      · -- Case A: p は着地位置 → cluster connectivity
        rw [List.any_eq_true] at h_p_mod
        obtain ⟨q_i, h_qi_mem, h_qi_match⟩ := h_p_mod
        have h_qi_beq := Bool.and_eq_true_iff.mp h_qi_match
        have h_qi_layer : q_i.layer - d = p.layer := beq_iff_eq.mp h_qi_beq.1
        have h_qi_dir : q_i.dir = p.dir := beq_iff_eq.mp h_qi_beq.2
        -- landingDistance_landed でアンカー取得
        have h_landed := Gravity.landingDistance_landed (.cluster ps) obs
            (show (Gravity.FallingUnit.cluster ps).positions ≠ [] from h_ps_ne)
        simp only [Gravity.FallingUnit.positions] at h_landed
        rw [List.any_eq_true] at h_landed
        obtain ⟨q_btl, h_btl_mem, h_btl_match⟩ := h_landed
        simp only [Bool.or_eq_true, beq_iff_eq] at h_btl_match
        rw [← h_d_eq] at h_btl_match
        -- q_btl の着地レイヤの事実
        have h_foldl_btl := Gravity.foldl_placeQuarter_written_canFormBond
            s obs ps d (q_btl.layer - d) q_btl.dir
            ⟨q_btl, h_btl_mem, rfl, rfl⟩ h_cluster_bond
        obtain ⟨qv_btl, h_gd_btl, h_bond_btl⟩ := h_foldl_btl
        change QuarterPos.getDir (obs'.getD (q_btl.layer - d) Layer.empty)
            q_btl.dir = qv_btl at h_gd_btl
        have h_ne_btl : (!qv_btl.isEmpty) = true := by
            rcases qv_btl with _ | _ | _ | _ <;>
                simp only [Quarter.canFormBond, Bool.false_eq_true, Quarter.isEmpty, Bool.not_false] at h_bond_btl ⊢
        have h_btl_lt : q_btl.layer - d < obs'.length := by
            by_contra h_ge'
            have h_ge'' : obs'.length ≤ q_btl.layer - d := by omega
            simp only [List.getD_eq_getElem?_getD,
                List.getElem?_eq_none_iff.mpr h_ge'',
                Option.getD_none] at h_gd_btl
            subst h_gd_btl
            cases hd' : q_btl.dir <;>
                simp only [Quarter.canFormBond, QuarterPos.getDir, hd', Layer.empty, Bool.false_eq_true] at h_bond_btl
        have h_gq_btl : (⟨q_btl.layer - d, q_btl.dir⟩ :
            QuarterPos).getQuarter s_result = some qv_btl := by
            simp only [QuarterPos.getQuarter, h_layers,
                List.getElem?_eq_getElem h_btl_lt]
            rw [← (show obs'.getD (q_btl.layer - d) Layer.empty =
                obs'[q_btl.layer - d] from by
                simp only [List.getD,
                    List.getElem?_eq_getElem h_btl_lt,
                    Option.getD_some])]
            exact congrArg some h_gd_btl
        have h_valid_btl : q_btl.layer - d < s_result.layerCount := by
            simp only [Shape.layerCount, h_layers]; exact h_btl_lt
        -- ★ q_btl が接地 → connectivity で q_i が接地 → p が接地
        suffices h_btl_grounded : ⟨q_btl.layer - d, q_btl.dir⟩ ∈
            Gravity.groundedPositions s_result by
          have h_reach := h_connected q_btl h_btl_mem q_i h_qi_mem
          -- map_step_inv で isStructurallyBonded チェーンを groundingEdge チェーンに変換
          have h_mapped := h_reach.map_step_inv
              (edge2 := Gravity.groundingEdge s_result)
              (f := fun q => ⟨q.layer - d, q.dir⟩)
              (P := fun q => q ∈ ps)
              (fun a' b' ha' h_sb' =>
                  ⟨h_cluster_closed a' ha' b' h_sb',
                   cluster_step_groundingEdge s obs ps d a' b' ha'
                      (h_cluster_closed a' ha' b' h_sb')
                      h_sb' h_cluster_bond h_d_le_min s_result h_of⟩)
              h_btl_mem
          -- groundedPositionsList_closed で閉包
          have h_g_any : (Gravity.groundedPositionsList s_result).any
              (· == ⟨q_btl.layer - d, q_btl.dir⟩) = true :=
              (Gravity.any_beq_iff_mem _ _).mpr
                  (by rwa [Gravity.groundedPositions, List.mem_toFinset] at h_btl_grounded)
          have h_qi_any := Gravity.groundedPositionsList_closed s_result
              ⟨q_btl.layer - d, q_btl.dir⟩ ⟨q_i.layer - d, q_i.dir⟩
              h_g_any h_mapped.2
          have h_p_eq : p = ⟨q_i.layer - d, q_i.dir⟩ := by
              rcases p with ⟨p_l, p_d⟩
              simp only [] at h_qi_layer h_qi_dir
              subst h_qi_layer; subst h_qi_dir; rfl
          rw [h_p_eq]
          rw [Gravity.groundedPositions, List.mem_toFinset]
          exact (Gravity.any_beq_iff_mem _ _).mp h_qi_any
        -- ★ q_btl 接地の証明: floor or obstacle
        by_cases h_z : q_btl.layer - d = 0
        · -- Layer 0: seed → grounded
          simp only [Gravity.groundedPositions, List.mem_toFinset]
          have h_seed : ⟨q_btl.layer - d, q_btl.dir⟩ ∈
              (QuarterPos.allValid s_result).filter (fun p' =>
                  p'.layer == 0 && match p'.getQuarter s_result with
                  | some q => !q.isEmpty | none => false) := by
              apply List.mem_filter.mpr
              exact ⟨(Gravity.any_beq_iff_mem _ _).mp
                  ((Gravity.allValid_any_iff_layer' s_result
                      ⟨q_btl.layer - d, q_btl.dir⟩).mpr h_valid_btl),
                  show ((q_btl.layer - d) == 0 && match (⟨q_btl.layer - d, q_btl.dir⟩ :
                      QuarterPos).getQuarter s_result with
                      | some q => !q.isEmpty | none => false) = true from by
                  simp only [show ((q_btl.layer - d) == 0) = true from
                      beq_iff_eq.mpr h_z, Bool.true_and, h_gq_btl, h_ne_btl]⟩
          exact (Gravity.any_beq_iff_mem _ _).mp
              (Gravity.groundedPositionsList_complete s_result
                  ⟨q_btl.layer - d, q_btl.dir⟩
                  ⟨q_btl.layer - d, q_btl.dir⟩
                  h_seed GenericReachable.refl)
        · -- Layer ≥ 1: below position grounded → contradiction approach
          have h_btl_ge1 : q_btl.layer - d ≥ 1 :=
              Nat.one_le_iff_ne_zero.mpr h_z
          have h_occ : Gravity.isOccupied obs
              (q_btl.layer - d - 1) q_btl.dir = true := by
            rcases h_btl_match with h_floor | h_obs
            · omega
            · exact h_obs
          have h_below_lt : q_btl.layer - d - 1 < obs.length := by
              unfold Gravity.isOccupied at h_occ
              by_contra h_ge; push Not at h_ge
              simp only [List.getElem?_eq_none_iff.mpr h_ge] at h_occ
              cases h_occ
          set q_below := QuarterPos.getDir
              obs[q_btl.layer - d - 1] q_btl.dir
          have h_q_ne_empty : q_below.isEmpty = false := by
              unfold Gravity.isOccupied at h_occ
              simp only [List.getElem?_eq_getElem h_below_lt,
                  Bool.not_eq_true'] at h_occ
              exact h_occ
          have h_q_ne_bool : !q_below.isEmpty = true := by
              rw [h_q_ne_empty]; rfl
          have h_gq_obs_below : (⟨q_btl.layer - d - 1, q_btl.dir⟩ :
              QuarterPos).getQuarter s_obs = some q_below := by
              show (match s_obs.layers[(q_btl.layer - d - 1)]? with
                  | some l => some (QuarterPos.getDir l q_btl.dir)
                  | none => none) = some q_below
              rw [h_layers_obs, List.getElem?_eq_getElem h_below_lt]
          have h_below_valid_obs : (q_btl.layer - d - 1) < s_obs.layerCount := by
              simp only [Shape.layerCount, h_layers_obs]; exact h_below_lt
          have h_grounded_obs : (⟨q_btl.layer - d - 1, q_btl.dir⟩ : QuarterPos) ∈
              Gravity.groundedPositions s_obs :=
              h_inv s_obs h_obs_of ⟨q_btl.layer - d - 1, q_btl.dir⟩
                  h_below_valid_obs ⟨q_below, h_gq_obs_below, h_q_ne_bool⟩
          have h_grounded_res := h_grounded_subset h_grounded_obs
          by_contra h_ug
          have h_no_below := below_grounded_implies_grounded
              s_result ⟨q_btl.layer - d, q_btl.dir⟩
              ⟨qv_btl, h_gq_btl,
                  by cases qv_btl <;> simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, Quarter.isEmpty, Bool.decide_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, not_and, forall_exists_index, and_imp, BEq.rfl, Bool.and_true, beq_iff_eq, and_self, ge_iff_le, Bool.false_eq_true, decide_false, Bool.not_false, List.getD_eq_getElem?_getD, getElem?_pos, Option.getD_some]⟩
              h_ug h_btl_ge1
          apply h_no_below
          by_cases h_below_land :
              ∃ q ∈ ps, q.layer - d = q_btl.layer - d - 1 ∧
                  q.dir = q_btl.dir
          · have h_below_lt_obs' : (q_btl.layer - d - 1) < obs'.length :=
                Nat.lt_of_lt_of_le h_below_lt
                    (placeFallingUnit_length_ge s obs (.cluster ps) d)
            obtain ⟨qb_new, hb_gq, hb_bond⟩ :=
                h_gq_canFormBond ⟨q_btl.layer - d - 1, q_btl.dir⟩
                    h_below_land h_below_lt_obs'
            exact ⟨qb_new, hb_gq,
                by have := canFormBond_implies_not_empty qb_new hb_bond; simp only [Bool.false_eq_true, decide_false, Bool.not_false, this],
                h_grounded_res⟩
          · have h_below_gq := h_gq_preserved
                ⟨q_btl.layer - d - 1, q_btl.dir⟩ h_below_valid_obs
                (fun q hq hpq => h_below_land ⟨q, hq, hpq⟩)
            exact ⟨q_below, by rw [h_below_gq]; exact h_gq_obs_below,
                h_q_ne_bool, h_grounded_res⟩
      · -- Case B: p は非着地位置 → quarter 保存 → grounded via edge mono
        have h_p_not_land : ∀ q ∈
            (Gravity.FallingUnit.cluster ps).positions,
            ¬(q.layer - d = p.layer ∧ q.dir = p.dir) := by
          intro q h_q_mem ⟨h_lay, h_dir⟩
          simp only [Gravity.FallingUnit.positions] at h_q_mem
          exact absurd (List.any_eq_true.mpr ⟨q, h_q_mem,
              by simp only [h_lay, BEq.rfl, h_dir, Bool.and_self]⟩) h_p_mod
        -- foldl_placeQuarter は非着地位置を保存
        have h_gdir := Gravity.foldl_placeQuarter_getDir_preserved
            s obs (Gravity.FallingUnit.cluster ps).positions d
            p.layer p.dir h_p_not_land
        change QuarterPos.getDir (obs'.getD p.layer Layer.empty)
            p.dir = QuarterPos.getDir (obs.getD p.layer Layer.empty) p.dir at h_gdir
        -- p は s_result で非空 → obs.getD の quarter も非空 → p.layer < obs.length
        obtain ⟨q_ne, hq_ne, hq_ne_ne⟩ := h_ne
        have h_p_lt_obs' : p.layer < obs'.length := by
            simp only [Shape.layerCount, h_layers] at h_valid; exact h_valid
        have h_p_lt_obs : p.layer < obs.length := by
            by_contra h_ge; push Not at h_ge
            -- obs.getD p.layer empty = empty (p.layer ≥ obs.length)
            have h_obs_none : obs[p.layer]? = none :=
                List.getElem?_eq_none_iff.mpr (by omega)
            have h_obs_getD : obs.getD p.layer Layer.empty = Layer.empty := by
                simp only [List.getD, h_obs_none, Option.getD_none]
            rw [h_obs_getD] at h_gdir
            have h_empty_dir :
                QuarterPos.getDir Layer.empty p.dir = Quarter.empty := by
                cases p.dir <;> rfl
            rw [h_empty_dir] at h_gdir
            -- h_gdir: getDir (obs'.getD ...) = Quarter.empty → p は空
            have h_obs'_getD : obs'.getD p.layer Layer.empty = obs'[p.layer] := by
                simp only [List.getD, List.getElem?_eq_getElem h_p_lt_obs',
                    Option.getD_some]
            rw [h_obs'_getD] at h_gdir
            simp only [QuarterPos.getQuarter, h_layers,
                List.getElem?_eq_getElem h_p_lt_obs'] at hq_ne
            cases hq_ne
            rw [h_gdir] at hq_ne_ne
            exact absurd hq_ne_ne (by decide)
        have h_p_valid_obs : p.layer < s_obs.layerCount := by
            simp only [Shape.layerCount, h_layers_obs]; exact h_p_lt_obs
        have h_p_gq := h_gq_preserved p h_p_valid_obs h_p_not_land
        have hq_ne_obs : p.getQuarter s_obs = some q_ne := by
            rw [← h_p_gq]; exact hq_ne
        exact h_grounded_subset
            (h_inv s_obs h_obs_of p h_p_valid_obs ⟨q_ne, hq_ne_obs, hq_ne_ne⟩)

/-- クラスタ FU 配置は全非空接地不変量を保存する（空着地・非空着地の両方を処理）。
    クラスタの象限は非ピン（canFormBond）であるため、isGroundingContact エッジは
    保存/追加のみで除去されない。これにより groundedPositions_mono_of_edge が適用可能。 -/
private lemma one_step_all_grounded_cluster
        (s : Shape) (obs : List Layer) (ps : List QuarterPos)
        (h_inv : AllNonEmptyGrounded obs)
        (h_fu : (Gravity.FallingUnit.cluster ps) ∈
            Gravity.sortFallingUnits' (Gravity.floatingUnits s)) :
        AllNonEmptyGrounded (Gravity.placeFallingUnit s obs (.cluster ps)
            (Gravity.landingDistance (.cluster ps) obs)) := by
    -- クラスタが floatingUnits に含まれることを導出
    have h_mem_fu : (Gravity.FallingUnit.cluster ps) ∈ Gravity.floatingUnits s :=
        (Gravity.sortFallingUnits'_perm (Gravity.floatingUnits s)).mem_iff.mp h_fu
    rw [Gravity.floatingUnits_eq_append, List.mem_append] at h_mem_fu
    rcases h_mem_fu with h_cl | h_pin
    · -- クラスタの構造的事実を導出
      rw [List.mem_map] at h_cl
      obtain ⟨c, h_c_mem, h_c_eq⟩ := h_cl
      have h_c_asc := (List.mem_filter.mp h_c_mem).1
      have h_eq : ps = c := by cases h_c_eq; rfl
      subst h_eq
      obtain ⟨pos, h_scl, _, _⟩ :=
          Gravity.allStructuralClustersList_is_structuralClusterList s ps h_c_asc
      -- h_connected: クラスタの内部接続性
      have h_connected : ∀ q1 ∈ (Gravity.FallingUnit.cluster ps).positions,
          ∀ q2 ∈ (Gravity.FallingUnit.cluster ps).positions,
          GenericReachable (Gravity.isStructurallyBonded s) q1 q2 := by
        intro q1 hq1 q2 hq2
        have h_r1 := Gravity.structuralClusterList_sound s pos q1
            ((Gravity.any_beq_iff_mem _ _).mpr (h_scl ▸ hq1))
        have h_r2 := Gravity.structuralClusterList_sound s pos q2
            ((Gravity.any_beq_iff_mem _ _).mpr (h_scl ▸ hq2))
        exact (h_r1.symm (Gravity.isStructurallyBonded_symm s)).trans h_r2
      -- h_cluster_bond: canFormBond
      have h_cluster_bond : ∀ q ∈ (Gravity.FallingUnit.cluster ps).positions,
          ∃ qv, q.getQuarter s = some qv ∧ qv.canFormBond = true := by
        intro q hq
        exact Gravity.allStructuralClustersList_all_bondable s ps
            (List.mem_filter.mp h_c_mem).1 q
            ((Gravity.any_beq_iff_mem _ _).mpr hq)
      -- h_cluster_closed: 閉包性
      have h_cluster_closed : ∀ q ∈ (Gravity.FallingUnit.cluster ps).positions,
          ∀ r, Gravity.isStructurallyBonded s q r = true →
          r ∈ (Gravity.FallingUnit.cluster ps).positions := by
        intro q hq r h_sb
        have h_reach_pos_q :=
            Gravity.structuralClusterList_sound s pos q
                ((Gravity.any_beq_iff_mem _ _).mpr (h_scl ▸ hq))
        have h_reach_pos_r :=
            h_reach_pos_q.trans (GenericReachable.step h_sb .refl)
        have h_lc : s.layerCount > 0 := by
            have h_v := Gravity.isStructurallyBonded_valid s q r h_sb
            exact Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt h_v) (le_refl _)
        have h_in := Gravity.structuralClusterList_complete s pos r
            h_lc h_reach_pos_r
        exact (Gravity.any_beq_iff_mem _ _).mp (h_scl ▸ h_in)
      -- 着地位置の空性で場合分け
      set d := Gravity.landingDistance (.cluster ps) obs with h_d_def
      by_cases h_all_empty : ∀ q ∈ (Gravity.FallingUnit.cluster ps).positions,
          (QuarterPos.getDir (obs.getD (q.layer - d) Layer.empty) q.dir).isEmpty = true
      · -- 全着地位置空: one_step_all_grounded を直接使用
        exact one_step_all_grounded s obs (.cluster ps) h_inv h_all_empty
            h_connected
            (by exact h_cluster_bond)
            (by exact h_cluster_closed)
      · -- 一部着地位置非空: d の大きさで場合分け
        by_cases hd : d ≥ 2
        · -- d ≥ 2: landingDistance_not_occupied_at_landing で全着地位置空を導出
          exfalso; apply h_all_empty
          -- ps ≠ [] (structuralClusterList は seed を含むため空でない)
          have h_ps_ne : ps ≠ [] := by
            intro h
            have h_nonempty :
                (Gravity.structuralClusterList s pos).any (· == pos) = true := by
              unfold Gravity.structuralClusterList; rw [Gravity.structuralBfs_eq_generic]
              exact genericBfs_contains_start _ _ _
                  (s.layerCount * 4 * (s.layerCount * 4))
                  (Nat.mul_pos (Nat.mul_pos (by omega) (by omega))
                      (Nat.mul_pos (by omega) (by omega)))
            rw [← h_scl, h] at h_nonempty
            simp only [List.any, Bool.false_eq_true] at h_nonempty
          -- minLayer ≥ 1
          have h_min_ge1 := floatingUnits_minLayer_ge_one s (.cluster ps)
              ((Gravity.sortFallingUnits'_perm (Gravity.floatingUnits s)).mem_iff.mp h_fu)
          -- 全着地位置空
          intro q hq
          have h_not_occ := Gravity.landingDistance_not_occupied_at_landing
              (.cluster ps) obs (by simp only [Gravity.FallingUnit.positions, ne_eq, h_ps_ne, not_false_eq_true]) h_min_ge1
              (by rw [← h_d_def]; exact hd) q hq
          -- isOccupied = false → getDir.isEmpty = true
          exact isOccupied_false_isEmpty obs (q.layer - d) q.dir h_not_occ
        · -- d ≤ 1: edge monotonicity アプローチで接地不変量を保存
          -- 基本事実の導出
          have h_ps_ne : ps ≠ [] := by
            intro h
            have h_nonempty :
                (Gravity.structuralClusterList s pos).any (· == pos) = true := by
              unfold Gravity.structuralClusterList; rw [Gravity.structuralBfs_eq_generic]
              exact genericBfs_contains_start _ _ _
                  (s.layerCount * 4 * (s.layerCount * 4))
                  (Nat.mul_pos (Nat.mul_pos (by omega) (by omega))
                      (Nat.mul_pos (by omega) (by omega)))
            rw [← h_scl, h] at h_nonempty
            simp only [List.any, Bool.false_eq_true] at h_nonempty
          have h_obs_ne : obs ≠ [] := by
              intro h_nil; apply h_all_empty; intro q _; subst h_nil
              simp only [List.getD, List.getElem?_nil, Option.getD_none]
              cases q.dir <;> rfl
          have h_d_le_min : d ≤ (Gravity.FallingUnit.cluster ps).minLayer := by
              rw [h_d_def]; exact Gravity.landingDistance_le_minLayer (.cluster ps) obs
          exact one_step_all_grounded_cluster_nonempty_landing s obs ps d
              h_inv h_obs_ne h_ps_ne h_d_def h_d_le_min
              h_cluster_bond h_cluster_closed h_connected
    · -- ピンとして floatingUnits に含まれるが cluster とされた → 矛盾
      rw [List.mem_map] at h_pin
      obtain ⟨_, _, h_p_eq⟩ := h_pin
      exact absurd h_p_eq (by intro h; cases h)


/-- pin FU 配置が接地不変量を保存する（ImmBelow 仮説付き版）。
    着地位置が空の場合は one_step_all_grounded を適用。
    着地位置が非空の場合（crystal→pin 上書き）は ImmBelow 仮説により
    垂直チェーンが保存されるため AllNonEmptyGrounded が保存される。
    計算検証: 5L 2dir 全ケースで violations=0 確認済（ImmBelow は pin NE 時に成立）。 -/
protected lemma one_step_all_grounded_pin
        (s : Shape) (obs : List Layer) (pos : QuarterPos)
        (h_inv : AllNonEmptyGrounded obs)
        (h_fu : (Gravity.FallingUnit.pin pos) ∈
            Gravity.sortFallingUnits' (Gravity.floatingUnits s))
        (h_ib_ne : ¬(QuarterPos.getDir (obs.getD (pos.layer - Gravity.landingDistance (.pin pos) obs)
            Layer.empty) pos.dir).isEmpty →
            ImmBelow obs) :
        AllNonEmptyGrounded (Gravity.placeFallingUnit s obs (.pin pos)
            (Gravity.landingDistance (.pin pos) obs)) := by
    -- 着地位置の isEmpty で場合分け
    by_cases h_empty_landing :
        (QuarterPos.getDir (obs.getD (pos.layer - Gravity.landingDistance (.pin pos) obs)
            Layer.empty) pos.dir).isEmpty = true
    · -- Case 1: 着地位置が空 → 既存の one_step_all_grounded を適用
      exact one_step_all_grounded s obs (.pin pos) h_inv
          (fun q hq => by
              simp only [Gravity.FallingUnit.positions, List.mem_singleton] at hq
              subst hq; exact h_empty_landing)
          (fun q1 hq1 q2 hq2 => by
              simp only [Gravity.FallingUnit.positions, List.mem_singleton] at hq1 hq2
              subst hq1; subst hq2; exact .refl)
          (by trivial)
          (by trivial)
    · -- Case 2: 着地位置が非空（crystal→pin 上書き）→ ImmBelow により証明
      -- ImmBelow(obs) ならば pin 上書き後も ImmBelow が保存され、
      -- ImmBelow → AllNonEmptyGrounded が即座に導かれる。
      -- pin 上書きは垂直 edge を保存し（pin は非空）、水平 edge のみ除去する。
      -- ImmBelow の下では全位置が垂直チェーンで接地されるため、水平 edge 除去は影響しない。
      have h_ne_landing : ¬(QuarterPos.getDir (obs.getD (pos.layer -
          Gravity.landingDistance (.pin pos) obs) Layer.empty) pos.dir).isEmpty := by
          intro h; exact absurd h h_empty_landing
      have h_ib := h_ib_ne h_ne_landing
      -- pin overwrite は obs の 1 位置のみ変更する。
      -- ImmBelow(obs) → obs の全位置が垂直チェーンで接地 →
      -- pin overwrite 後も全位置が垂直チェーンで接地 →
      -- AllNonEmptyGrounded
      -- placeFallingUnit for pin: pin の positions = [pos]、1 位置のみ overwrite
      -- placeFallingUnit s obs (.pin pos) d = placeQuarter obs (pos.layer - d) pos.dir (pin)
      -- ここで pos の getQuarter s = some pin (floating pin)
      -- 結果の obs' は obs と位置 (pos.layer - d, pos.dir) のみが異なる
      -- ImmBelow(obs) → ImmBelow(obs') を示し、ImmBelow(obs') → AllNonEmptyGrounded(obs')
      set d := Gravity.landingDistance (.pin pos) obs
      set lp := pos.layer - d
      -- obs' = placeFallingUnit の結果
      set obs' := Gravity.placeFallingUnit s obs (.pin pos) d with h_obs'_def
      -- lp < obs.length (着地位置の非空性から)
      have h_lp_lt : lp < obs.length := by
          by_contra h
          push Not at h
          have h_out : obs.getD lp Layer.empty = Layer.empty := by
              simp only [List.getD, List.getElem?_eq_none_iff.mpr h, Option.getD_none]
          exact h_ne_landing (by rw [h_out]; cases pos.dir <;> decide)
      -- pos は floatingUnits の位置 → getQuarter s は非空
      have h_pos_mem_fu : (Gravity.FallingUnit.pin pos) ∈ Gravity.floatingUnits s :=
          (Gravity.sortFallingUnits'_perm (Gravity.floatingUnits s)).mem_iff.mp h_fu
      have h_pos_in_flat : ((Gravity.floatingUnits s).flatMap
          Gravity.FallingUnit.positions).any (· == pos) = true :=
          List.any_eq_true.mpr ⟨pos, List.mem_flatMap.mpr ⟨.pin pos, h_pos_mem_fu,
              List.mem_singleton.mpr rfl⟩, BEq.rfl⟩
      obtain ⟨_, ⟨qv, h_gq, h_qv_ne⟩, _⟩ :=
          Gravity.floatingUnits_positions_getQuarter s pos h_pos_in_flat
      -- positions = [pos]
      have h_positions : (Gravity.FallingUnit.pin pos).positions = [pos] := rfl
      -- obs' の長さ = obs.length (lp < obs.length なので拡張なし)
      have h_obs'_len : obs'.length = obs.length := by
          show (Gravity.placeFallingUnit s obs (.pin pos) d).length = obs.length
          simp only [Gravity.placeFallingUnit, h_positions, List.foldl_cons, List.foldl_nil, h_gq]
          rw [Gravity.placeQuarter_length]
          omega
      -- 非着地位置の getDir 保存
      have h_preserved : ∀ l dir, ¬(lp = l ∧ pos.dir = dir) →
          QuarterPos.getDir (obs'.getD l Layer.empty) dir =
          QuarterPos.getDir (obs.getD l Layer.empty) dir := by
          intro l dir h_not
          show QuarterPos.getDir ((Gravity.placeFallingUnit s obs (.pin pos) d).getD l Layer.empty) dir = _
          simp only [Gravity.placeFallingUnit, h_positions]
          exact Gravity.foldl_placeQuarter_getDir_preserved s obs [pos] d l dir
              (fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact h_not)
      -- 着地位置は非空 (qv が配置され、qv は非空)
      have h_target_ne : ¬(QuarterPos.getDir (obs'.getD lp Layer.empty) pos.dir).isEmpty := by
          have h_at_target : QuarterPos.getDir (obs'.getD lp Layer.empty) pos.dir = qv := by
              show QuarterPos.getDir ((Gravity.placeFallingUnit s obs (.pin pos) d).getD lp Layer.empty) pos.dir = qv
              simp only [Gravity.placeFallingUnit, h_positions]
              exact Gravity.foldl_placeQuarter_getDir_at_target s obs [pos] d pos
                  (List.mem_singleton.mpr rfl) (List.nodup_singleton _)
                  (fun p hp hne => by simp only [List.mem_singleton] at hp; exact absurd hp hne)
                  qv h_gq
          rw [h_at_target]
          intro h_contra
          rw [h_contra] at h_qv_ne
          exact absurd h_qv_ne (by decide)
      -- ImmBelow(obs') の証明本体
      have h_ib' : ImmBelow obs' := by
          intro l dir h_lt h_gt h_ne_l
          by_cases h_eq_l : lp = l ∧ pos.dir = dir
          · -- Case 1: (l, dir) = (lp, pos.dir)
            obtain ⟨hl, hd⟩ := h_eq_l; subst hl; subst hd
            -- below (lp-1, pos.dir): 保存されており、ImmBelow(obs) から非空
            have h_not_below : ¬(lp = lp - 1 ∧ pos.dir = pos.dir) := by omega
            rw [h_preserved (lp - 1) pos.dir h_not_below]
            exact h_ib lp pos.dir (by omega) h_gt h_ne_landing
          · by_cases h_eq_lm1 : lp = l - 1 ∧ pos.dir = dir
            · -- Case 2: (l-1, dir) = (lp, pos.dir) → 着地位置は NE
              obtain ⟨hl, hd⟩ := h_eq_lm1; subst hd
              rw [show l - 1 = lp from hl.symm]
              exact h_target_ne
            · -- Case 3: 両方保存 → ImmBelow(obs) を適用
              rw [h_preserved (l - 1) dir h_eq_lm1]
              rw [h_preserved l dir h_eq_l] at h_ne_l
              exact h_ib l dir (by omega) h_gt h_ne_l
      exact immBelow_implies_allNonEmptyGrounded obs' h_ib'

/-- Perm から flatMap の Perm を導出するユーティリティ -/
private theorem perm_flatMap_of_perm {l1 l2 : List α} (f : α → List β)
        (h : l1.Perm l2) : (l1.flatMap f).Perm (l2.flatMap f) := by
    induction h with
    | nil => exact List.Perm.refl _
    | cons x _ ih => simp only [List.flatMap_cons]; exact ih.append_left (f x)
    | swap x y l =>
        simp only [List.flatMap_cons]
        rw [← List.append_assoc, ← List.append_assoc]
        exact List.perm_append_comm.append_right (l.flatMap f)
    | trans _ _ ih1 ih2 => exact ih1.trans ih2


/-- placeFallingUnit は非空位置の非空性を保存する。
    FU の着地位置に含まれない (l, dir) は、配置後も元の obs と同じ getDir 値を持つ。
    特に非空なら非空のまま保たれる。 -/
private theorem placeFallingUnit_ne_mono
        (s : Shape) (obs : List Layer) (u : Gravity.FallingUnit) (d : Nat)
        (l : Nat) (dir : Direction)
        (h_ne : ¬(QuarterPos.getDir (obs.getD l Layer.empty) dir).isEmpty)
        (h_not_target : ∀ p ∈ u.positions, ¬(p.layer - d = l ∧ p.dir = dir)) :
        ¬(QuarterPos.getDir ((Gravity.placeFallingUnit s obs u d).getD l
            Layer.empty) dir).isEmpty := by
    have h_pres := Gravity.foldl_placeQuarter_getDir_preserved s obs
        u.positions d l dir h_not_target
    unfold Gravity.placeFallingUnit
    exact h_pres ▸ h_ne


/-- pin が非空位置に着地する場合、着地距離は必ず 1 である。
    d > 1 なら d-1 チェックが失敗 → 着地位置が空 → 非空着地仮説と矛盾。 -/
private theorem pin_ne_landing_dist_eq_one (pos : QuarterPos) (obs : List Layer)
        (h_min : pos.layer ≥ 1)
        (h_ne : ¬(QuarterPos.getDir (obs.getD (pos.layer -
            Gravity.landingDistance (.pin pos) obs) Layer.empty) pos.dir).isEmpty) :
        Gravity.landingDistance (.pin pos) obs = 1 := by
    set d := Gravity.landingDistance (.pin pos) obs
    have h_ge : d ≥ 1 := Gravity.landingDistance_ge_one _ obs h_min
    have h_le : d ≤ pos.layer := Gravity.landingDistance_le_minLayer _ obs
    by_contra h_ne_one
    have h_gt : d > 1 := by omega
    -- d > 1 → d-1 チェック失敗 → 着地位置が空
    have h_not_landed := Gravity.landingDistance_check_not_landed_before
        obs [pos] pos.layer 1 (pos.layer + 1) (by omega) (by omega)
        (d - 1) (by omega) (by show d - 1 < d; omega)
    simp only [List.any, Bool.or_false] at h_not_landed
    rw [Bool.or_eq_false_iff] at h_not_landed
    obtain ⟨_, h_nocc⟩ := h_not_landed
    have h_eq_layer : pos.layer - (d - 1) - 1 = pos.layer - d := by omega
    rw [h_eq_layer] at h_nocc
    -- isOccupied false → getDir isEmpty → 非空着地仮説と矛盾
    unfold Gravity.isOccupied at h_nocc
    cases h_cas : obs[pos.layer - d]? with
    | none =>
        have : obs.getD (pos.layer - d) Layer.empty = Layer.empty := by
            simp only [List.getD, h_cas, Option.getD_none]
        rw [this] at h_ne
        revert h_ne; cases pos.dir <;>
            simp only [Quarter.isEmpty, QuarterPos.getDir, Layer.empty, not_true_eq_false, imp_self]
    | some l =>
        rw [h_cas] at h_nocc
        have h_empty : (QuarterPos.getDir l pos.dir).isEmpty = true := by
            cases (QuarterPos.getDir l pos.dir).isEmpty <;> simp_all only [ge_iff_le, List.getD_eq_getElem?_getD, Option.getD_some, Bool.not_eq_true, ne_eq, gt_iff_lt, beq_eq_false_iff_ne, Bool.not_false, Bool.true_eq_false]
        have h_eq : obs.getD (pos.layer - d) Layer.empty = l := by
            simp only [List.getD, h_cas, Option.getD_some]
        rw [h_eq] at h_ne
        exact h_ne h_empty

end Shape

