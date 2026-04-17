-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Behavior.Gravity

namespace Shape

-- gravity_IsSettled の接地不変量補題
-- ============================================================

/-- layers 上の全非空位置が ofLayers layers 上で接地している -/
def AllNonEmptyGrounded (layers : List Layer) : Prop :=
    ∀ (s : Shape), Shape.ofLayers layers = some s →
        ∀ (p : QuarterPos), p.layer < s.layerCount →
            (∃ q, p.getQuarter s = some q ∧ !q.isEmpty = true) →
            p ∈ Gravity.groundedPositions s

/-- ImmBelow: 全非空位置の直下も非空（垂直チェーン完備性）。
    obs 上の全非空位置が垂直に下方と接続されていることを表す。
    この性質が成り立つとき、全非空位置は垂直のみの接地パスを持つため、
    水平 edge を除去しても AllNonEmptyGrounded が保存される。 -/
def ImmBelow (obs : List Layer) : Prop :=
    ∀ (l : Nat) (d : Direction), l < obs.length → l > 0 →
        ¬(QuarterPos.getDir (obs.getD l Layer.empty) d).isEmpty →
        ¬(QuarterPos.getDir (obs.getD (l - 1) Layer.empty) d).isEmpty

/-- ImmBelow の 1 段降下版。layer l の非空性から layer (l-1) の非空性を得る。 -/
theorem ImmBelow.descends_one_layer
        {obs : List Layer} (h_ib : ImmBelow obs)
        {l : Nat} {d : Direction}
        (h_lt : l < obs.length) (h_pos : l > 0)
        (h_ne : ¬(QuarterPos.getDir (obs.getD l Layer.empty) d).isEmpty) :
        ¬(QuarterPos.getDir (obs.getD (l - 1) Layer.empty) d).isEmpty :=
    h_ib l d h_lt h_pos h_ne

/-- 垂直接触の構成: 同方角・垂直隣接・両方非空 → isGroundingContact -/
theorem vertical_grounding_contact
        (s : Shape) (l : Nat) (d : Direction)
        (h_ne_low : ∃ q, (⟨l, d⟩ : QuarterPos).getQuarter s = some q ∧ !q.isEmpty = true)
        (h_ne_high : ∃ q, (⟨l + 1, d⟩ : QuarterPos).getQuarter s = some q ∧ !q.isEmpty = true) :
        Gravity.isGroundingContact s ⟨l, d⟩ ⟨l + 1, d⟩ = true := by
    obtain ⟨q1, hq1, hne1⟩ := h_ne_low
    obtain ⟨q2, hq2, hne2⟩ := h_ne_high
    unfold Gravity.isGroundingContact
    rw [hq1, hq2]; simp only
    have h1 : q1.isEmpty = false := by cases q1 <;> simp_all only [Quarter.isEmpty, Bool.decide_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_true, Bool.false_eq_true, decide_false, Bool.not_false]
    have h2 : q2.isEmpty = false := by cases q2 <;> simp_all only [Quarter.isEmpty, Bool.decide_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_true, Bool.false_eq_true, decide_false, Bool.not_false]
    rw [h1, h2]
    simp only [Bool.not_false, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
    left; exact ⟨.intro, by unfold LayerIndex.verticallyAdjacent; simp only [BEq.rfl, Bool.true_or]⟩

/-- ImmBelow → obs の全非空位置は垂直チェーンで接地される。
    getDir の非空性から任意の Shape s (s.layers = obs) 上の getQuarter 非空性を導出する。 -/
theorem getDir_nonempty_implies_getQuarter
        (s : Shape) (l : Nat) (d : Direction)
        (h_lt : l < s.layerCount)
        (h_ne : ¬(QuarterPos.getDir (s.layers.getD l Layer.empty) d).isEmpty) :
        ∃ q, (⟨l, d⟩ : QuarterPos).getQuarter s = some q ∧ !q.isEmpty = true := by
    have h_lt' : l < s.layers.length := by
        simp only [Shape.layerCount] at h_lt; exact h_lt
    rw [show s.layers.getD l Layer.empty = s.layers[l] from by
        simp only [List.getD, List.getElem?_eq_getElem h_lt', Option.getD_some]] at h_ne
    refine ⟨QuarterPos.getDir s.layers[l] d, ?_, ?_⟩
    · simp only [QuarterPos.getQuarter]
      rw [List.getElem?_eq_getElem h_lt']
    · revert h_ne
      cases QuarterPos.getDir s.layers[l] d with
      | empty => intro h; exact absurd rfl h
      | crystal c => intro _; rfl
      | pin => intro _; rfl
      | colored p c => intro _; rfl

/-- ImmBelow の下で、非空位置の縦列は layer 0 まで全て非空（降下帰納法） -/
theorem immBelow_column_filled
        (obs : List Layer) (h_ib : ImmBelow obs)
        (l : Nat) (d : Direction) (h_lt : l < obs.length)
        (h_ne : ¬(QuarterPos.getDir (obs.getD l Layer.empty) d).isEmpty) :
        ∀ k, k ≤ l → ¬(QuarterPos.getDir (obs.getD k Layer.empty) d).isEmpty := by
    intro k hk
    suffices h_fill : ∀ m, m ≤ l →
            ¬(QuarterPos.getDir (obs.getD m Layer.empty) d).isEmpty →
            ∀ j, j ≤ m → ¬(QuarterPos.getDir (obs.getD j Layer.empty) d).isEmpty by
        exact h_fill l (Nat.le_refl _) h_ne k hk
    intro m
    induction m with
    | zero =>
        intro _ h0 j hj
        have : j = 0 := Nat.le_zero.mp hj
        subst this
        exact h0
    | succ n ih =>
        intro h_n_succ_le h_n_succ_ne j hj
        by_cases h_j_top : j = n + 1
        · subst h_j_top
          exact h_n_succ_ne
        · have h_j_le_n : j ≤ n := by omega
          have h_n_succ_lt_len : n + 1 < obs.length :=
              Nat.lt_of_le_of_lt h_n_succ_le h_lt
          have h_n_ne : ¬(QuarterPos.getDir (obs.getD n Layer.empty) d).isEmpty :=
              ImmBelow.descends_one_layer h_ib h_n_succ_lt_len (by omega) h_n_succ_ne
          exact ih (by omega) h_n_ne j h_j_le_n

/-- ImmBelow → AllNonEmptyGrounded。
    ImmBelow の下では全非空位置が同一方角の垂直チェーンで layer 0 に到達可能。
    垂直チェーンは isGroundingContact を形成するため、全位置が接地される。 -/
theorem immBelow_implies_allNonEmptyGrounded
        (obs : List Layer)
        (h_ib : ImmBelow obs) :
        AllNonEmptyGrounded obs := by
    intro s h_of p h_valid h_ne
    -- s.layers = obs を導出
    have h_layers : s.layers = obs := by
        cases obs with
        | nil => simp only [ofLayers, reduceCtorEq] at h_of
        | cons hd tl =>
            simp only [Shape.ofLayers] at h_of
            exact congrArg Shape.layers (Option.some.inj h_of).symm
    have h_lc_eq : s.layerCount = obs.length := by
        simp only [Shape.layerCount, h_layers]
    have h_p_lt : p.layer < obs.length := by omega
    -- p の getDir が非空
    obtain ⟨q, hq, hq_ne⟩ := h_ne
    have h_p_ne_dir : ¬(QuarterPos.getDir (obs.getD p.layer Layer.empty) p.dir).isEmpty := by
        rw [show obs.getD p.layer Layer.empty = obs[p.layer] from by
            simp only [List.getD, List.getElem?_eq_getElem h_p_lt, Option.getD_some]]
        simp only [QuarterPos.getQuarter, h_layers,
            List.getElem?_eq_getElem h_p_lt] at hq
        rw [Option.some.inj hq]
        cases q <;> simp_all only [Quarter.isEmpty, decide_true, Bool.not_true, Bool.false_eq_true, decide_false, Bool.not_false, Option.some.injEq, not_false_eq_true]
    -- 垂直チェーン: (0, p.dir), ..., (p.layer, p.dir) は全て非空
    have h_chain := immBelow_column_filled obs h_ib p.layer p.dir h_p_lt h_p_ne_dir
    -- seed (0, p.dir) の構築
    set seed : QuarterPos := ⟨0, p.dir⟩
    have h_seed_lt : (0 : Nat) < obs.length := by omega
    have h_seed_ne := h_chain 0 (Nat.zero_le _)
    -- GenericReachable チェーン: seed → p
    have h_reach : GenericReachable (Gravity.isUpwardGroundingContact s) seed p := by
        cases hp_layer : p.layer with
        | zero =>
            have : seed = p := by
                cases p with | mk l d =>
                simp only [seed]
                rw [QuarterPos.mk.injEq]
                exact ⟨hp_layer.symm, rfl⟩
            rw [this]; exact .refl
        | succ n =>
            suffices ∀ k, k ≤ n + 1 →
                GenericReachable (Gravity.isUpwardGroundingContact s) seed ⟨k, p.dir⟩ by
                have h_eq : (⟨n + 1, p.dir⟩ : QuarterPos) = p := by
                    cases p with | mk l d =>
                    rw [QuarterPos.mk.injEq]
                    exact ⟨hp_layer.symm, rfl⟩
                exact h_eq ▸ this (n + 1) (le_refl _)
            intro k hk
            induction k with
            | zero => exact .refl
            | succ m ihm =>
                have h_m_reach := ihm (by omega)
                have h_m_lt : m < obs.length := by omega
                have h_m1_lt : m + 1 < obs.length := by omega
                have h_m_ne := h_chain m (by omega)
                have h_m1_ne := h_chain (m + 1) (by omega)
                have h_contact := vertical_grounding_contact s m p.dir
                    (getDir_nonempty_implies_getQuarter s m p.dir
                        (by omega) (by rw [h_layers]; exact h_m_ne))
                    (getDir_nonempty_implies_getQuarter s (m + 1) p.dir
                        (by omega) (by rw [h_layers]; exact h_m1_ne))
                exact h_m_reach.trans (.step
                    (Gravity.isGroundingContact_to_isUpwardGroundingContact
                        h_contact (Nat.le_succ m))
                    .refl)
    -- seed の接地性を構築して結論
    have h_seed_valid : seed.layer < s.layerCount := by show 0 < s.layerCount; omega
    have h_seed_gq := getDir_nonempty_implies_getQuarter s 0 p.dir
        (by show 0 < s.layerCount; omega) (by rw [h_layers]; exact h_seed_ne)
    obtain ⟨q0, hq0, hne0⟩ := h_seed_gq
    have h_seed_mem : seed ∈ (QuarterPos.allValid s).filter (fun q =>
            q.layer == 0 && match q.getQuarter s with
            | some q => !q.isEmpty | none => false) := by
        apply List.mem_filter.mpr; constructor
        · exact (Gravity.any_beq_iff_mem _ _).mp
            ((Gravity.allValid_any_iff_layer' s seed).mpr h_seed_valid)
        · simp only [beq_iff_eq, Bool.and_eq_true]
          refine ⟨rfl, ?_⟩
          rw [hq0]
          cases q0 <;> simp_all only [Quarter.isEmpty, Bool.decide_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.getD_eq_getElem?_getD, getElem?_pos, Option.getD_some, Bool.not_eq_true, decide_true, Bool.false_eq_true, decide_false, Bool.not_false]
    simp only [Gravity.groundedPositions, List.mem_toFinset]
    exact (Gravity.any_beq_iff_mem _ _).mp
        (Gravity.groundedPositionsList_complete s seed p h_seed_mem
            (h_reach.mono (fun _ _ h => Gravity.groundingEdge_of_isUpwardGroundingContact h)))

/-- foldl の接地不変量帰納法（prefix 構造付き版）:
    各ステップで処理済みの prefix を追跡し、obs がその prefix の foldl であることを保証する。
    これにより step 関数で obs の構造的性質（ImmBelow 等）を導出可能にする。 -/
theorem foldl_grounded_induction_prefix
        (s : Shape) (sorted : List Gravity.FallingUnit) (obs0 : List Layer)
        (h_base : AllNonEmptyGrounded obs0)
        (h_step : ∀ (done : List Gravity.FallingUnit) (u : Gravity.FallingUnit)
            (rest : List Gravity.FallingUnit),
            sorted = done ++ u :: rest →
            AllNonEmptyGrounded (done.foldl (fun o fu =>
                Gravity.placeFallingUnit s o fu (Gravity.landingDistance fu o)) obs0) →
            AllNonEmptyGrounded (Gravity.placeFallingUnit s
                (done.foldl (fun o fu =>
                    Gravity.placeFallingUnit s o fu (Gravity.landingDistance fu o)) obs0)
                u (Gravity.landingDistance u
                    (done.foldl (fun o fu =>
                        Gravity.placeFallingUnit s o fu (Gravity.landingDistance fu o)) obs0)))) :
        AllNonEmptyGrounded (sorted.foldl (fun obs u =>
            Gravity.placeFallingUnit s obs u (Gravity.landingDistance u obs)) obs0) := by
    suffices key : ∀ (done rest : List Gravity.FallingUnit),
        sorted = done ++ rest →
        AllNonEmptyGrounded (done.foldl (fun o fu =>
            Gravity.placeFallingUnit s o fu (Gravity.landingDistance fu o)) obs0) →
        AllNonEmptyGrounded ((done ++ rest).foldl (fun o fu =>
            Gravity.placeFallingUnit s o fu (Gravity.landingDistance fu o)) obs0) by
      exact key [] sorted (by simp only [List.nil_append]) h_base
    intro done rest h_eq h_inv
    induction rest generalizing done with
    | nil => rwa [List.append_nil]
    | cons hd tl ih =>
        rw [show done ++ hd :: tl = (done ++ [hd]) ++ tl from by
            simp only [List.append_assoc, List.singleton_append]]
        apply ih (done ++ [hd]) (by rw [h_eq]; simp only [List.append_assoc, List.cons_append, List.nil_append])
        rw [show (done ++ [hd]).foldl (fun o fu =>
            Gravity.placeFallingUnit s o fu (Gravity.landingDistance fu o)) obs0 =
            Gravity.placeFallingUnit s
                (done.foldl (fun o fu =>
                    Gravity.placeFallingUnit s o fu (Gravity.landingDistance fu o)) obs0)
                hd (Gravity.landingDistance hd
                    (done.foldl (fun o fu =>
                        Gravity.placeFallingUnit s o fu (Gravity.landingDistance fu o)) obs0)) from by
            simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]]
        exact h_step done hd tl h_eq h_inv

/-- foldl の接地不変量帰納法: base case + step case から foldl 全体の不変量を導出 -/
theorem foldl_grounded_induction
        (s : Shape) (sorted : List Gravity.FallingUnit) (obs : List Layer)
        (h_base : AllNonEmptyGrounded obs)
        (h_step : ∀ (obs' : List Layer) (u : Gravity.FallingUnit),
            u ∈ sorted → AllNonEmptyGrounded obs' →
            AllNonEmptyGrounded (Gravity.placeFallingUnit s obs' u
                (Gravity.landingDistance u obs'))) :
        AllNonEmptyGrounded (sorted.foldl (fun obs u =>
            Gravity.placeFallingUnit s obs u (Gravity.landingDistance u obs)) obs) := by
    induction sorted generalizing obs with
    | nil => exact h_base
    | cons hd tl ih =>
        rw [List.foldl_cons]
        exact ih
            (Gravity.placeFallingUnit s obs hd (Gravity.landingDistance hd obs))
            (h_step obs hd (.head _) h_base)
            (fun obs' u h_mem h_inv => h_step obs' u (.tail _ h_mem) h_inv)

/-- foldl の接地不変量帰納法（追加不変量 P 付き版）:
    P を foldl の各ステップで追跡し、P を満たす obs に対してのみ ANEG 保存を要求する -/
theorem foldl_grounded_induction_with_inv
        (s : Shape) (sorted : List Gravity.FallingUnit) (obs : List Layer)
        (P : List Layer → Prop)
        (h_base_aneg : AllNonEmptyGrounded obs)
        (h_base_p : P obs)
        (h_step : ∀ (obs' : List Layer) (u : Gravity.FallingUnit),
            u ∈ sorted → AllNonEmptyGrounded obs' → P obs' →
            AllNonEmptyGrounded (Gravity.placeFallingUnit s obs' u
                (Gravity.landingDistance u obs')))
        (h_step_p : ∀ (obs' : List Layer) (u : Gravity.FallingUnit),
            u ∈ sorted → P obs' →
            P (Gravity.placeFallingUnit s obs' u
                (Gravity.landingDistance u obs'))) :
        AllNonEmptyGrounded (sorted.foldl (fun obs u =>
            Gravity.placeFallingUnit s obs u (Gravity.landingDistance u obs)) obs) := by
    induction sorted generalizing obs with
    | nil => exact h_base_aneg
    | cons hd tl ih =>
        rw [List.foldl_cons]
        exact ih
            (Gravity.placeFallingUnit s obs hd (Gravity.landingDistance hd obs))
            (h_step obs hd (.head _) h_base_aneg h_base_p)
            (h_step_p obs hd (.head _) h_base_p)
            (fun obs' u h_mem h_inv h_p => h_step obs' u (.tail _ h_mem) h_inv h_p)
            (fun obs' u h_mem h_p => h_step_p obs' u (.tail _ h_mem) h_p)

end Shape

