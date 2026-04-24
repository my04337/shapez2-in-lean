-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity

namespace Shape

-- groundingEdge_eq_of_getQuarter_eq は
-- S2IL/Operations/Gravity/GroundedMono.lean で public 定義済み（2026-04-21 移設）

/-- normalize は groundingEdge を単調に保存する。
    両端点の非空性を確認してから getQuarter の等価性を経由して転送する -/
private theorem groundingEdge_normalize_mono (s s' : Shape)
        (h_norm : s.normalize = some s') (a b : QuarterPos)
        (h : Gravity.groundingEdge s a b = true) :
        Gravity.groundingEdge s' a b = true := by
    have h_gc := Gravity.groundingEdge_base h
    obtain ⟨q1, q2, hq1, hq2, hne1, hne2⟩ :=
        Gravity.isGroundingContact_nonEmpty s a b h_gc
    have h_a_v := normalize_nonEmpty_layer_lt s s' h_norm a q1 hq1 hne1
    have h_b_v := normalize_nonEmpty_layer_lt s s' h_norm b q2 hq2 hne2
    rw [← groundingEdge_eq_of_getQuarter_eq s s' a b
        (normalize_getQuarter_eq s s' h_norm a h_a_v).symm
        (normalize_getQuarter_eq s s' h_norm b h_b_v).symm]
    exact h

/-- normalize は groundedPositions を単調に保存する。
    BFS シード条件を転送し、エッジ単調性（groundingEdge_normalize_mono）で到達可能性を引き継ぐ -/
private theorem groundedPositions_normalize_mono (s s' : Shape)
        (h_norm : s.normalize = some s') (p : QuarterPos)
        (h_grounded : p ∈ Gravity.groundedPositions s) :
        p ∈ Gravity.groundedPositions s' := by
    -- BFS sound: ∃ seed, seed → p が s で到達可能
    have h_any_s := (Gravity.any_beq_iff_mem _ _).mpr
        (List.mem_toFinset.mp h_grounded)
    obtain ⟨seed, h_seed_s, h_reach_s⟩ :=
        Gravity.groundedPositionsList_sound s p h_any_s
    -- seed 条件の s' への転送（layer=0 かつ非空象限を持つ）
    have h_seed_s' : seed ∈ (QuarterPos.allValid s').filter (fun q =>
            q.layer == 0 && match q.getQuarter s' with
            | some q => !q.isEmpty | none => false) := by
        rw [List.mem_filter] at h_seed_s ⊢
        obtain ⟨h_av, h_cond⟩ := h_seed_s
        have h_l0 := (Bool.and_eq_true_iff.mp h_cond).1
        obtain ⟨qs, hqs_eq, hqs_ne_f⟩ :
                ∃ qs, seed.getQuarter s = some qs ∧ qs.isEmpty = false := by
            cases hgq : seed.getQuarter s with
            | none =>
                simp only [hgq] at h_cond
                exact absurd h_cond (by simp only [Bool.and_false, Bool.false_eq_true, not_false_eq_true])
            | some q_val =>
                simp only [hgq] at h_cond
                have h_ne := (Bool.and_eq_true_iff.mp h_cond).2
                have : q_val.isEmpty = false := by
                    cases h_ie : q_val.isEmpty with
                    | true => rw [h_ie] at h_ne; exact absurd h_ne (by decide)
                    | false => rfl
                exact ⟨q_val, rfl, this⟩
        have h_sv := normalize_nonEmpty_layer_lt s s' h_norm seed qs hqs_eq hqs_ne_f
        constructor
        · have h_any := (Gravity.allValid_any_iff_layer' s' seed).mpr h_sv
          rw [List.any_eq_true] at h_any
          obtain ⟨y, hy, hye⟩ := h_any; exact eq_of_beq hye ▸ hy
        · simp only [h_l0, Bool.true_and]
          rw [normalize_getQuarter_eq s s' h_norm seed h_sv]
          simp only [hqs_eq, hqs_ne_f]; decide
    -- BFS 完全性: groundingEdge 単調性で s の到達可能性を s' に転送
    simp only [Gravity.groundedPositions, List.mem_toFinset]
    exact (Gravity.any_beq_iff_mem _ _).mp
        (Gravity.groundedPositionsList_complete s' seed p h_seed_s'
            (GenericReachable.mono (groundingEdge_normalize_mono s s' h_norm) h_reach_s))

/-- normalize は floatingUnits = [] を保存する -/
private theorem floatingUnits_nil_of_normalize (s : Shape) (s' : Shape)
        (h_norm : s.normalize = some s')
        (h_nil : Gravity.floatingUnits s = []) :
        Gravity.floatingUnits s' = [] := by
    -- 背理法: floatingUnits s' が非空なら矛盾
    by_contra h_ne
    have h_ne_false : (Gravity.floatingUnits s').isEmpty = false := by
        match h_check : Gravity.floatingUnits s' with
        | [] => exact absurd h_check h_ne
        | _ :: _ => rfl
    -- s' で非空かつ非接地の位置 p を取得
    obtain ⟨p, h_valid_s', ⟨q, hq_s', hq_ne⟩, h_ug_s'⟩ :=
        Gravity.floatingUnits_nonempty_implies_exists_ungrounded s' h_ne_false
    -- p は s でも非空（normalize は getQuarter を保存）
    have hq_s : p.getQuarter s = some q := by
        rw [← normalize_getQuarter_eq s s' h_norm p h_valid_s']; exact hq_s'
    have hq_ne_false : q.isEmpty = false := by
        cases h_ie : q.isEmpty with
        | true => rw [h_ie] at hq_ne; exact absurd hq_ne (by decide)
        | false => rfl
    -- p.layer < s.layerCount（getQuarter が some を返す → layer は有効）
    have h_valid_s : p.layer < s.layerCount := by
        simp only [Shape.layerCount]
        if h_ge : s.layers.length ≤ p.layer then
            exfalso
            have h_none := List.getElem?_eq_none_iff.mpr h_ge
            have h_eq : p.getQuarter s = none := by
                unfold QuarterPos.getQuarter; rw [h_none]
            rw [h_eq] at hq_s; exact absurd hq_s (by intro h; cases h)
        else
            omega
    -- floatingUnits s = [] なのに p が非接地 → p は s で接地
    have h_grounded_s : p ∈ Gravity.groundedPositions s := by
        by_contra h_ug_s
        have := Gravity.ungrounded_nonempty_implies_floatingUnits_nonempty s p
            h_valid_s ⟨q, hq_s, hq_ne⟩ h_ug_s
        rw [h_nil] at this; exact absurd this (by decide)
    -- groundedPositions 単調性で s' でも接地 → 矛盾
    exact h_ug_s' (groundedPositions_normalize_mono s s' h_norm p h_grounded_s)

/-- normalize の出力は安定状態を保存する -/
theorem IsSettled_normalize (s : Shape) (s' : Shape)
        (h_norm : s.normalize = some s') (h_settled : s.IsSettled) :
        s'.IsSettled := by
    exact floatingUnits_nil_of_normalize s s' h_norm h_settled

-- ============================================================

end Shape
