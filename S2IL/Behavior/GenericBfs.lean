-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

/-!
# 汎用 BFS 完全性

任意のエッジ述語に対する BFS の健全性・完全性のインフラストラクチャ。
`CrystalBond.lean` と `Gravity.lean` で共通に使用される。
-/

/-- 汎用 BFS: エッジ述語をパラメータとして受け取る -/
def genericBfs [BEq α] (edge : α → α → Bool)
        (allNodes visited queue : List α) : (fuel : Nat) → List α
    | 0 => visited
    | fuel + 1 =>
        match queue with
        | [] => visited
        | pos :: rest =>
            if visited.any (· == pos) then
                genericBfs edge allNodes visited rest fuel
            else
                let newVisited := pos :: visited
                let neighbors := allNodes.filter fun p =>
                    edge pos p && !(newVisited.any (· == p))
                genericBfs edge allNodes newVisited (rest ++ neighbors) fuel

-- ============================================================
-- 到達可能性の帰納的定義
-- ============================================================

/-- 汎用 BFS による到達可能性 -/
inductive GenericReachable (edge : α → α → Bool) : α → α → Prop where
    | refl : GenericReachable edge p p
    | step : edge p q = true → GenericReachable edge q r → GenericReachable edge p r

/-- 到達可能性の推移性 -/
theorem GenericReachable.trans {edge : α → α → Bool}
        (h1 : GenericReachable edge p q) (h2 : GenericReachable edge q r) :
        GenericReachable edge p r := by
    induction h1 with
    | refl => exact h2
    | step h_edge _ ih => exact .step h_edge (ih h2)

/-- 辺が対称ならば到達可能性も対称 -/
theorem GenericReachable.symm {edge : α → α → Bool}
        (h_symm : ∀ a b, edge a b = edge b a)
        (h : GenericReachable edge p q) :
        GenericReachable edge q p := by
    induction h with
    | refl => exact .refl
    | step h_edge _ ih =>
        exact ih.trans (.step (h_symm _ _ ▸ h_edge) .refl)

/-- エッジの単調性: edge1 が成立するなら edge2 も成立する場合、到達可能性を転送 -/
theorem GenericReachable.mono {edge1 edge2 : α → α → Bool}
        (h_imp : ∀ a b, edge1 a b = true → edge2 a b = true)
        (hr : GenericReachable edge1 seed p) :
        GenericReachable edge2 seed p := by
    induction hr with
    | refl => exact .refl
    | step h_edge _ ih => exact .step (h_imp _ _ h_edge) ih

/-- 関数 f を通じて到達可能性をマッピングする -/
theorem GenericReachable.map_step
        {edge1 : α → α → Bool} {edge2 : β → β → Bool} {f : α → β}
        (h_step : ∀ a b, edge1 a b = true → edge2 (f a) (f b) = true)
        {x y : α}
        (h_reach : GenericReachable edge1 x y) :
        GenericReachable edge2 (f x) (f y) := by
    induction h_reach with
    | refl => exact .refl
    | step h_edge _ ih => exact .step (h_step _ _ h_edge) ih

/-- 不変量付きの到達可能性マッピング: 各ステップで P を保存しつつ edge2 へ変換する -/
theorem GenericReachable.map_step_inv
        {edge1 : α → α → Bool} {edge2 : β → β → Bool}
        {f : α → β} {P : α → Prop}
        (h_step : ∀ a b, P a → edge1 a b = true →
            P b ∧ edge2 (f a) (f b) = true)
        {x y : α} (hx : P x)
        (h_reach : GenericReachable edge1 x y) :
        P y ∧ GenericReachable edge2 (f x) (f y) := by
    induction h_reach with
    | refl => exact ⟨hx, .refl⟩
    | step h_edge _ ih =>
        have ⟨hb, h_gc⟩ := h_step _ _ hx h_edge
        have ⟨hc, h_reach'⟩ := ih hb
        exact ⟨hc, .step h_gc h_reach'⟩

/-- 非ブリッジ辺の除去: 削除された辺の両端が edge2 で互いに到達可能なら、
edge1 での到達可能性は edge2 でも保存される -/
theorem GenericReachable.non_bridge_removal
        {edge1 edge2 : α → α → Bool}
        (h_reach : GenericReachable edge1 s x)
        (h_cycle : ∀ a b, edge1 a b = true → edge2 a b = false →
            GenericReachable edge2 a b) :
        GenericReachable edge2 s x := by
    induction h_reach with
    | refl => exact .refl
    | step h_edge _ ih =>
        cases h2 : edge2 _ _
        · exact (h_cycle _ _ h_edge h2).trans ih
        · exact .step h2 ih

-- ============================================================
-- BFS エッジ合同
-- ============================================================

/-- エッジ述語が等しければ genericBfs の結果も等しい -/
theorem genericBfs_edge_congr [BEq α] [LawfulBEq α]
        (edge1 edge2 : α → α → Bool)
        (h_eq : ∀ a b, edge1 a b = edge2 a b)
        (allNodes vis queue : List α) (fuel : Nat) :
        genericBfs edge1 allNodes vis queue fuel =
        genericBfs edge2 allNodes vis queue fuel := by
    induction fuel generalizing vis queue with
    | zero => rfl
    | succ n ih =>
        cases queue with
        | nil => simp only [genericBfs]
        | cons pos rest =>
            simp only [genericBfs]
            split
            · exact ih vis rest
            · have : allNodes.filter (fun p => edge1 pos p && !((pos :: vis).any (· == p))) =
                     allNodes.filter (fun p => edge2 pos p && !((pos :: vis).any (· == p))) := by
                  congr 1; ext p; rw [h_eq]
              rw [this]
              exact ih (pos :: vis) (rest ++ _)

-- ============================================================
-- BFS 基本補題
-- ============================================================

/-- BFS は初期訪問済み集合を保持する -/
theorem genericBfs_vis_subset [BEq α] (edge : α → α → Bool)
        (allNodes vis queue : List α) (fuel : Nat) (p : α) :
        vis.any (· == p) = true →
        (genericBfs edge allNodes vis queue fuel).any (· == p) = true := by
    intro h
    induction fuel generalizing vis queue with
    | zero => exact h
    | succ n ih =>
        cases queue with
        | nil => exact h
        | cons pos rest =>
            simp only [genericBfs]
            split
            · exact ih vis rest h
            · exact ih (pos :: vis) (rest ++ _) (by rw [List.any_cons]; simp only [h, Bool.or_true])

/-- BFS は fuel > 0 なら start を結果に含む -/
theorem genericBfs_contains_start [BEq α] [LawfulBEq α]
        (edge : α → α → Bool) (allNodes : List α)
        (start : α) (fuel : Nat) (h_fuel : fuel > 0) :
        (genericBfs edge allNodes [] [start] fuel).any (· == start) = true := by
    cases fuel with
    | zero => omega
    | succ n =>
        simp only [genericBfs, List.any]
        exact genericBfs_vis_subset edge allNodes [start] _ n start
            (by rw [List.any_cons]; simp only [BEq.rfl, Bool.true_or])

/-- BFS 結果の各要素は初期 vis に含まれるか、初期 queue のある要素から到達可能 -/
theorem genericBfs_sound [BEq α] [LawfulBEq α] (edge : α → α → Bool)
        (allNodes vis queue : List α) (fuel : Nat) (p : α) :
        (genericBfs edge allNodes vis queue fuel).any (· == p) = true →
        vis.any (· == p) = true ∨
        ∃ q, queue.any (· == q) = true ∧ GenericReachable edge q p := by
    induction fuel generalizing vis queue with
    | zero => intro h; exact .inl h
    | succ n ih =>
        cases queue with
        | nil => intro h; exact .inl h
        | cons pos rest =>
            simp only [genericBfs]
            split
            · intro h
              match ih vis rest h with
              | .inl h_vis => exact .inl h_vis
              | .inr ⟨q, h_q, h_reach⟩ =>
                  exact .inr ⟨q, by rw [List.any_cons]; simp only [h_q, Bool.or_true], h_reach⟩
            · intro h
              match ih (pos :: vis) (rest ++ _) h with
              | .inl h' =>
                  rw [List.any_cons] at h'
                  cases h_eq : (pos == p) with
                  | true =>
                      exact .inr ⟨pos, by rw [List.any_cons]; simp only [BEq.rfl, Bool.true_or],
                          eq_of_beq h_eq ▸ GenericReachable.refl⟩
                  | false =>
                      rw [h_eq, Bool.false_or] at h'
                      exact .inl h'
              | .inr ⟨q, h_q_mem, h_reach⟩ =>
                  rw [List.any_append] at h_q_mem
                  cases Bool.or_eq_true_iff.mp h_q_mem with
                  | inl h_rest =>
                      exact .inr ⟨q, by rw [List.any_cons]; simp only [h_rest, Bool.or_true], h_reach⟩
                  | inr h_neigh =>
                      rw [List.any_filter, List.any_eq_true] at h_neigh
                      obtain ⟨a, _, h_pred⟩ := h_neigh
                      simp only [Bool.and_eq_true] at h_pred
                      obtain ⟨⟨h_edge, _⟩, h_aeq⟩ := h_pred
                      have := eq_of_beq h_aeq; subst this
                      exact .inr ⟨pos, by rw [List.any_cons]; simp only [BEq.rfl, Bool.true_or],
                          .step h_edge h_reach⟩

-- ============================================================
-- BFS 不変条件
-- ============================================================

/-- BFS の不変条件: vis 内の全ノードの allNodes 内エッジ隣接先は vis ∪ queue に含まれる -/
def GenericBfsInv [BEq α] (edge : α → α → Bool)
        (allNodes vis queue : List α) : Prop :=
    ∀ v, vis.any (· == v) = true →
      ∀ n, allNodes.any (· == n) = true →
        edge v n = true →
        vis.any (· == n) = true ∨ queue.any (· == n) = true

/-- BFS 初期不変条件: 空の visited と [start] の queue で不変条件が成立する。
    visited が空のため前提 `vis.any (· == v) = true` が偽となり自明に成立。 -/
theorem GenericBfsInv_initial [BEq α] (edge : α → α → Bool)
        (allNodes : List α) (start : α) :
        GenericBfsInv edge allNodes [] [start] := by
    intro v hv; simp only [List.any, Bool.false_eq_true] at hv

/-- 重複スキップで不変条件が保存される -/
theorem GenericBfsInv_skip [BEq α] [LawfulBEq α]
        (edge : α → α → Bool) (allNodes vis : List α)
        (pos : α) (rest : List α)
        (h_inv : GenericBfsInv edge allNodes vis (pos :: rest))
        (h_vis : vis.any (· == pos) = true) :
        GenericBfsInv edge allNodes vis rest := by
    intro v hv n hn hb
    match h_inv v hv n hn hb with
    | .inl h => exact .inl h
    | .inr h =>
        rw [List.any_cons] at h
        cases h_eq : (pos == n) with
        | true => exact .inl (by rw [show pos = n from eq_of_beq h_eq] at h_vis; exact h_vis)
        | false => rw [h_eq, Bool.false_or] at h; exact .inr h

/-- 新ノード処理で不変条件が保存される -/
theorem GenericBfsInv_process [BEq α] [LawfulBEq α]
        (edge : α → α → Bool) (allNodes vis : List α)
        (pos : α) (rest : List α)
        (h_inv : GenericBfsInv edge allNodes vis (pos :: rest))
        (_h_not_vis : ¬(vis.any (· == pos) = true)) :
        GenericBfsInv edge allNodes (pos :: vis)
            (rest ++ allNodes.filter fun p =>
                edge pos p && !((pos :: vis).any (· == p))) := by
    intro v hv n hn hb
    rw [List.any_cons] at hv
    cases h_vp : (pos == v) with
    | true =>
        have := eq_of_beq h_vp; subst this
        by_cases h_nv : ((pos :: vis).any (· == n)) = true
        · exact .inl h_nv
        · right; rw [List.any_append, Bool.or_eq_true_iff]
          right; rw [List.any_eq_true]
          have h_n_mem : n ∈ allNodes := by
              rw [List.any_eq_true] at hn
              obtain ⟨x, h_x_mem, h_x_eq⟩ := hn
              exact eq_of_beq h_x_eq ▸ h_x_mem
          exact ⟨n, List.mem_filter.mpr ⟨h_n_mem, by simp only [hb, h_nv, Bool.not_false, Bool.and_self]⟩, BEq.rfl⟩
    | false =>
        rw [h_vp, Bool.false_or] at hv
        match h_inv v hv n hn hb with
        | .inl h => exact .inl (by rw [List.any_cons]; simp only [h, Bool.or_true])
        | .inr h =>
            rw [List.any_cons] at h
            cases h_pn : (pos == n) with
            | true => exact .inl (by rw [List.any_cons]; simp only [h_pn, Bool.true_or])
            | false =>
                rw [h_pn, Bool.false_or] at h
                exact .inr (by rw [List.any_append, Bool.or_eq_true_iff]; left; exact h)

-- ============================================================
-- 燃料充足性ヘルパー
-- ============================================================

private theorem filter_length_lt_of_mem_of_not' [BEq α]
        (l : List α) (pred : α → Bool) (x : α)
        (h_mem : x ∈ l) (h_not : pred x = false) :
        (l.filter pred).length < l.length := by
    induction l with
    | nil => nomatch h_mem
    | cons a as ih =>
        simp only [List.filter, List.length]
        cases h_mem with
        | head => simp only [h_not]; have := List.length_filter_le (p := pred) as; omega
        | tail _ h_as =>
            cases pred a <;> simp only [List.length] <;> (have := ih h_as; omega)

private theorem filter_and_length_le' [BEq α]
        (l : List α) (p q : α → Bool) :
        (l.filter fun x => p x && q x).length ≤ (l.filter q).length := by
    induction l with
    | nil => simp only [List.filter, List.length_nil, Std.le_refl]
    | cons a as ih =>
        simp only [List.filter]
        cases h_q : q a <;> cases p a <;> simp only [Bool.and_true, Bool.and_false, List.length] <;> omega

private theorem add_sq_le_sq_of_lt' (nb u' u : Nat)
        (h_nb : nb ≤ u') (h_lt : u' < u) :
        nb + u' * u' ≤ u * u := by
    have h1 : u' ≤ u := by omega
    have h3 : u' * (u' + 1) ≤ u * u := Nat.mul_le_mul h1 h_lt
    have h4 : u' + u' * u' = u' * (u' + 1) := by rw [Nat.mul_succ]; omega
    omega

/-- pos を vis に追加したとき、新エッジ + 未訪問²  ≤ 旧未訪問² -/
private theorem fuel_key_estimate [BEq α] [LawfulBEq α]
        (edge : α → α → Bool) (allNodes vis : List α) (pos : α)
        (h_nv : ¬(vis.any (· == pos) = true))
        (h_edge_valid : ∀ p q, edge p q = true → allNodes.any (· == p) = true) :
        (allNodes.filter fun p => edge pos p && !((pos :: vis).any (· == p))).length +
        (allNodes.filter fun p => !((pos :: vis).any (· == p))).length *
        (allNodes.filter fun p => !((pos :: vis).any (· == p))).length ≤
        (allNodes.filter fun p => !(vis.any (· == p))).length *
        (allNodes.filter fun p => !(vis.any (· == p))).length := by
    have h_nb_le := filter_and_length_le' allNodes
        (fun p => edge pos p) (fun p => !((pos :: vis).any (· == p)))
    cases h_pos : allNodes.any (· == pos) with
    | false =>
        have h_no_edge : ∀ x, edge pos x = false := by
            intro x; cases h_e : edge pos x with
            | false => rfl
            | true => exact absurd (h_edge_valid pos x h_e) (by simp only [h_pos, Bool.false_eq_true, not_false_eq_true])
        have h_nb_zero : (allNodes.filter fun p =>
                edge pos p && !((pos :: vis).any (· == p))).length = 0 := by
            suffices h : ∀ l : List α,
                (l.filter fun p => edge pos p && !((pos :: vis).any (· == p))).length = 0 from h allNodes
            intro l; induction l with
            | nil => rfl
            | cons a as ih_l =>
                simp only [List.filter, h_no_edge a, Bool.false_and]; exact ih_l
        have h_u_eq :
            (allNodes.filter fun p => !((pos :: vis).any (· == p))).length =
            (allNodes.filter fun p => !(vis.any (· == p))).length := by
            congr 1; apply List.filter_congr; intro x hx
            simp only [List.any_cons]
            cases h_eq : (pos == x) with
            | false => simp only [Bool.false_or]
            | true =>
                exfalso
                have := eq_of_beq h_eq; subst this
                have h_mem : allNodes.any (· == pos) = true := by
                    rw [List.any_eq_true]; exact ⟨pos, hx, BEq.rfl⟩
                simp only [h_pos, Bool.false_eq_true] at h_mem
        rw [h_nb_zero, h_u_eq]; omega
    | true =>
        have h_pos_mem : pos ∈ allNodes := by
            rw [List.any_eq_true] at h_pos
            obtain ⟨x, hx, he⟩ := h_pos; exact eq_of_beq he ▸ hx
        have h_vis_false : vis.any (· == pos) = false :=
            Bool.eq_false_iff.mpr h_nv
        have h_pos_in_u : pos ∈ allNodes.filter (fun p => !(vis.any (· == p))) :=
            List.mem_filter.mpr ⟨h_pos_mem, by simp only [h_vis_false, Bool.not_false]⟩
        have h_u'_lt_u :
            (allNodes.filter fun p => !((pos :: vis).any (· == p))).length <
            (allNodes.filter fun p => !(vis.any (· == p))).length := by
            have h_eq :
                (allNodes.filter fun p => !((pos :: vis).any (· == p))) =
                (allNodes.filter (fun p => !(vis.any (· == p)))).filter
                    (fun p => !(pos == p)) := by
                rw [List.filter_filter]; apply List.filter_congr
                intro x _; simp only [List.any_cons, Bool.not_or]
            rw [h_eq]
            exact filter_length_lt_of_mem_of_not'
                (allNodes.filter (fun p => !(vis.any (· == p))))
                (fun p => !(pos == p)) pos h_pos_in_u (by simp only [BEq.rfl, Bool.not_true])
        exact add_sq_le_sq_of_lt' _ _ _ h_nb_le h_u'_lt_u

-- ============================================================
-- BFS 不変条件保存 (メイン定理)
-- ============================================================

/-- BFS が不変条件を保存する。
    BFS 実行後の結果 visited リストが閉包（queue = []）になることを示す。
    前提: (1) 初期状態が不変条件を満たす、(2) 燃料が十分
    （fuel + 1 ≥ |queue| + |未訪問|²）、(3) edge が allNodes 内のノードのみ返す -/
theorem genericBfs_invariant_preserved [BEq α] [LawfulBEq α]
        (edge : α → α → Bool) (allNodes vis queue : List α) (fuel : Nat)
        (h_inv : GenericBfsInv edge allNodes vis queue)
        (h_fuel : fuel + 1 ≥ queue.length +
            (allNodes.filter fun p => !(vis.any (· == p))).length *
            (allNodes.filter fun p => !(vis.any (· == p))).length)
        (h_edge_valid : ∀ p q, edge p q = true → allNodes.any (· == p) = true) :
        GenericBfsInv edge allNodes (genericBfs edge allNodes vis queue fuel) [] := by
    induction fuel generalizing vis queue with
    | zero =>
        simp only [genericBfs]
        intro v hv n hn hb; left
        cases h_inv v hv n hn hb with
        | inl h => exact h
        | inr h_q =>
            have h_qlen : queue.length ≥ 1 := by
                cases queue with | nil => simp only [List.any, Bool.false_eq_true] at h_q | cons _ _ => simp only [List.length_cons, ge_iff_le, Nat.le_add_left]
            have h_u_zero : (allNodes.filter fun p => !(vis.any (· == p))).length = 0 := by
                cases hu : (allNodes.filter fun p => !(vis.any (· == p))).length with
                | zero => rfl
                | succ m =>
                    have h_sq : (m + 1) * (m + 1) ≥ 1 :=
                        Nat.mul_le_mul (Nat.succ_le_succ (Nat.zero_le m))
                            (Nat.succ_le_succ (Nat.zero_le m))
                    have h_flat := hu ▸ h_sq
                    omega
            rw [List.any_eq_true] at hn
            obtain ⟨x, hx_mem, hx_eq⟩ := hn
            have := eq_of_beq hx_eq; subst this
            cases h_vis_x : vis.any (· == x) with
            | true => rfl
            | false =>
                have h_x_in : x ∈ allNodes.filter (fun p => !(vis.any (· == p))) :=
                    List.mem_filter.mpr ⟨hx_mem, by simp only [h_vis_x, Bool.not_false]⟩
                have h_nil := List.eq_nil_of_length_eq_zero h_u_zero
                rw [h_nil] at h_x_in; nomatch h_x_in
    | succ n ih =>
        cases queue with
        | nil => exact h_inv
        | cons pos rest =>
            simp only [genericBfs]
            split
            · rename_i h_vis
              apply ih vis rest (GenericBfsInv_skip edge allNodes vis pos rest h_inv h_vis)
              have : (pos :: rest).length = rest.length + 1 := rfl
              rw [this] at h_fuel; omega
            · rename_i h_not_vis
              have h_nv : ¬(vis.any (· == pos) = true) := by
                  intro h; rw [h] at h_not_vis; exact h_not_vis rfl
              apply ih (pos :: vis) (rest ++ _)
                  (GenericBfsInv_process edge allNodes vis pos rest h_inv h_nv)
              · simp only [List.length_append]
                have h_len : (pos :: rest).length = rest.length + 1 := rfl
                rw [h_len] at h_fuel
                have h_key := fuel_key_estimate edge allNodes vis pos h_nv h_edge_valid
                omega

/-- BFS の初期 vis ∪ queue 内の allNodes メンバーは、十分な fuel のとき結果に含まれる -/
theorem genericBfs_queue_in_result [BEq α] [LawfulBEq α]
        (edge : α → α → Bool) (allNodes vis queue : List α) (fuel : Nat) (p : α)
        (h_mem : vis.any (· == p) = true ∨ queue.any (· == p) = true)
        (h_in : allNodes.any (· == p) = true)
        (h_fuel : fuel + 1 ≥ queue.length +
            (allNodes.filter fun q => !(vis.any (· == q))).length *
            (allNodes.filter fun q => !(vis.any (· == q))).length)
        (h_edge_valid : ∀ a b, edge a b = true → allNodes.any (· == a) = true) :
        (genericBfs edge allNodes vis queue fuel).any (· == p) = true := by
    cases h_mem with
    | inl h => exact genericBfs_vis_subset edge allNodes vis queue fuel p h
    | inr h_q =>
        induction fuel generalizing vis queue with
        | zero =>
            simp only [genericBfs]
            have h_qlen : queue.length ≥ 1 := by
                cases queue with | nil => simp only [List.any, Bool.false_eq_true] at h_q | cons _ _ => simp only [List.length_cons, ge_iff_le, Nat.le_add_left]
            have h_u_zero : (allNodes.filter fun q => !(vis.any (· == q))).length = 0 := by
                cases hu : (allNodes.filter fun q => !(vis.any (· == q))).length with
                | zero => rfl
                | succ m =>
                    have h_sq : (m + 1) * (m + 1) ≥ 1 :=
                        Nat.mul_le_mul (Nat.succ_le_succ (Nat.zero_le m))
                            (Nat.succ_le_succ (Nat.zero_le m))
                    have h_flat := hu ▸ h_sq
                    omega
            have h_p_mem : p ∈ allNodes := by
                rw [List.any_eq_true] at h_in
                obtain ⟨x, hx, he⟩ := h_in; exact eq_of_beq he ▸ hx
            cases hv : vis.any (· == p) with
            | true => rfl
            | false =>
                exfalso
                have h_in_filter : p ∈ allNodes.filter (fun q => !(vis.any (· == q))) :=
                    List.mem_filter.mpr ⟨h_p_mem, by simp only [hv, Bool.not_false]⟩
                have h_nil : allNodes.filter (fun q => !(vis.any (· == q))) = [] := by
                    cases hf : allNodes.filter (fun q => !(vis.any (· == q))) with
                    | nil => rfl
                    | cons _ _ => simp only [hf, List.length_cons, Nat.add_eq_zero_iff, List.length_eq_zero_iff, Nat.succ_ne_self, and_false] at h_u_zero
                rw [h_nil] at h_in_filter; nomatch h_in_filter
        | succ n ih =>
            cases queue with
            | nil => simp only [List.any, Bool.false_eq_true] at h_q
            | cons pos rest =>
                simp only [genericBfs]
                rw [List.any_cons] at h_q
                split
                · -- skip: vis.any (· == pos) = true
                  rename_i h_vis_pos
                  cases h_eq : (pos == p) with
                  | true =>
                      exact genericBfs_vis_subset edge allNodes vis rest n p
                          (show vis.any (· == p) = true by
                              have := eq_of_beq h_eq; rw [← this]; exact h_vis_pos)
                  | false =>
                      rw [h_eq, Bool.false_or] at h_q
                      exact ih vis rest (by
                          have : (pos :: rest).length = rest.length + 1 := rfl
                          rw [this] at h_fuel; omega) h_q
                · -- process: ¬ vis.any (· == pos)
                  rename_i h_not_vis
                  cases h_eq : (pos == p) with
                  | true =>
                      have h_p_in_vis' : (pos :: vis).any (· == p) = true := by
                          rw [List.any_cons]; simp only [h_eq, Bool.true_or]
                      exact genericBfs_vis_subset edge allNodes (pos :: vis) _ n p h_p_in_vis'
                  | false =>
                      rw [h_eq, Bool.false_or] at h_q
                      have h_q' : (rest ++ allNodes.filter fun q =>
                              edge pos q && !((pos :: vis).any (· == q))).any (· == p) = true := by
                          rw [List.any_append, Bool.or_eq_true_iff]; exact .inl h_q
                      exact ih (pos :: vis) _ (by
                          have h_nv : ¬(vis.any (· == pos) = true) := by
                              intro h; rw [h] at h_not_vis; exact h_not_vis rfl
                          simp only [List.length_append]
                          have h_len : (pos :: rest).length = rest.length + 1 := rfl
                          rw [h_len] at h_fuel
                          have h_key := fuel_key_estimate edge allNodes vis pos h_nv h_edge_valid
                          omega) h_q'

-- ============================================================
-- 閉包→到達可能性
-- ============================================================

/-- 閉じた集合（queue = [] の不変条件）は start から到達可能な全ノードを含む。
    edge の妥当性（結果が allNodes に含まれる）と、start が vis に含まれることを前提とする。
    GenericReachable の帰納法で証明し、各ステップで不変条件の閉包性を適用する -/
theorem genericBfs_closed_contains_reachable [BEq α] [LawfulBEq α]
        (edge : α → α → Bool) (allNodes vis : List α)
        (h_closed : GenericBfsInv edge allNodes vis [])
        (start p : α)
        (h_start : vis.any (· == start) = true)
        (h_reach : GenericReachable edge start p)
        (h_valid : ∀ q r, edge q r = true → allNodes.any (· == r) = true) :
        vis.any (· == p) = true := by
    induction h_reach with
    | refl => exact h_start
    | step h_edge _ ih =>
        match h_closed _ h_start _ (h_valid _ _ h_edge) h_edge with
        | .inl h => exact ih h
        | .inr h => simp only [List.any, Bool.false_eq_true] at h

-- ============================================================
-- 置換下の等変性
-- ============================================================

private theorem any_map_eq [BEq α]
        (σ : α → α) (h_beq : ∀ a b, (σ a == σ b) = (a == b))
        (l : List α) (p : α) :
        (l.map σ).any (· == σ p) = l.any (· == p) := by
    rw [List.any_map]; congr 1; ext x; exact h_beq x p

private theorem any_cons_map_eq [BEq α]
        (σ : α → α) (h_beq : ∀ a b, (σ a == σ b) = (a == b))
        (x : α) (l : List α) (p : α) :
        (σ x :: l.map σ).any (· == σ p) = (x :: l).any (· == p) := by
    simp only [List.any_cons, h_beq, any_map_eq σ h_beq]

private theorem filter_map_comm [BEq α]
        (edge edge' : α → α → Bool) (σ : α → α)
        (h_edge : ∀ a b, edge' (σ a) (σ b) = edge a b)
        (h_beq : ∀ a b, (σ a == σ b) = (a == b))
        (allNodes : List α) (pos : α) (vis : List α) :
        (allNodes.map σ).filter (fun p =>
            edge' (σ pos) p && !((σ pos :: vis.map σ).any (· == p))) =
        (allNodes.filter (fun p =>
            edge pos p && !((pos :: vis).any (· == p)))).map σ := by
    induction allNodes with
    | nil => rfl
    | cons a as ih =>
        simp only [List.map, List.filter]
        rw [h_edge, any_cons_map_eq σ h_beq]
        cases edge pos a && !((pos :: vis).any (· == a)) with
        | true => simp only [List.map]; exact congrArg _ ih
        | false => exact ih

/-- genericBfs は置換 σ の下で等変:
    edge' (σ a) (σ b) = edge a b かつ (σ a == σ b) = (a == b) のとき、
    allNodes/vis/queue を σ でマップした結果は、元の結果を σ でマップしたものに等しい -/
theorem genericBfs_map_comm [BEq α] [LawfulBEq α]
        (edge edge' : α → α → Bool) (σ : α → α)
        (h_edge : ∀ a b, edge' (σ a) (σ b) = edge a b)
        (h_beq : ∀ a b, (σ a == σ b) = (a == b))
        (allNodes vis queue : List α) (fuel : Nat) :
        genericBfs edge' (allNodes.map σ) (vis.map σ) (queue.map σ) fuel =
        (genericBfs edge allNodes vis queue fuel).map σ := by
    induction fuel generalizing vis queue with
    | zero => rfl
    | succ n ih =>
        cases queue with
        | nil => simp only [genericBfs, List.map_nil]
        | cons pos rest =>
            show genericBfs edge' (allNodes.map σ) (vis.map σ)
                (σ pos :: rest.map σ) (n + 1) =
                (genericBfs edge allNodes vis (pos :: rest) (n + 1)).map σ
            simp only [genericBfs]
            rw [any_map_eq σ h_beq]
            split
            · exact ih vis rest
            · rw [filter_map_comm edge edge' σ h_edge h_beq, ← List.map_append]
              exact ih (pos :: vis) (rest ++ allNodes.filter fun p =>
                  edge pos p && !((pos :: vis).any (· == p)))
