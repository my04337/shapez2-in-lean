-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity.CommExt.CommNe

namespace Gravity

open _root_.QuarterPos (getQuarter_rotate180)

-- ============================================================
-- tied 要素の方角非共有性と foldl 可換性
-- ============================================================

/-- foldl-min-option の補助関数（定義の一致問題を回避するため独立定義） -/
def foldMinOption : Option Nat → Nat → Option Nat :=
    fun acc l => some (match acc with | some a => min a l | none => l)

/-- foldMinOption (some init) rest = some v → v = init ∨ v ∈ rest -/
theorem foldMinOption_some_mem (rest : List Nat) (init v : Nat)
        (h : rest.foldl foldMinOption (some init) = some v) :
        v = init ∨ v ∈ rest := by
    induction rest generalizing init with
    | nil => simp only [List.foldl, Option.some.injEq] at h; exact .inl h.symm
    | cons b tail ih =>
        simp only [List.foldl_cons, foldMinOption] at h
        cases ih (min init b) h with
        | inl heq =>
            cases Nat.le_total init b with
            | inl hle => rw [Nat.min_eq_left hle] at heq; exact .inl heq
            | inr hle => rw [Nat.min_eq_right hle] at heq; exact .inr (heq ▸ .head tail)
        | inr hmem => exact .inr (.tail b hmem)

/-- foldMinOption none layers = some v → v ∈ layers -/
theorem foldMinOption_none_mem (layers : List Nat) (v : Nat)
        (h : layers.foldl foldMinOption none = some v) :
        v ∈ layers := by
    cases layers with
    | nil => simp only [List.foldl, reduceCtorEq] at h
    | cons a rest =>
        simp only [List.foldl_cons, foldMinOption] at h
        cases foldMinOption_some_mem rest a v h with
        | inl heq => exact heq ▸ .head rest
        | inr hmem => exact .tail a hmem

/-- foldMinOption (some init) rest は常に some を返す -/
theorem foldMinOption_some_isSome (rest : List Nat) (init : Nat) :
        ∃ v, rest.foldl foldMinOption (some init) = some v := by
    induction rest generalizing init with
    | nil => exact ⟨init, rfl⟩
    | cons y ys ih => simp only [List.foldl_cons, foldMinOption]; exact ih (min init y)

/-- foldMinOption (some init) rest = some v → v ≤ init -/
theorem foldMinOption_some_le_init (rest : List Nat) (init v : Nat)
        (h : rest.foldl foldMinOption (some init) = some v) :
        v ≤ init := by
    induction rest generalizing init with
    | nil =>
        simp only [List.foldl, Option.some.injEq] at h
        omega
    | cons y ys ih =>
        simp only [List.foldl_cons, foldMinOption] at h
        exact Nat.le_trans (ih (min init y) h) (Nat.min_le_left init y)

/-- foldMinOption (some init) rest = some v → 任意の m ∈ rest に対して v ≤ m -/
theorem foldMinOption_some_le_mem (rest : List Nat) (init v : Nat)
        (h : rest.foldl foldMinOption (some init) = some v) (m : Nat) (hm : m ∈ rest) :
        v ≤ m := by
    induction rest generalizing init with
    | nil => nomatch hm
    | cons y ys ih =>
        simp only [List.foldl_cons, foldMinOption] at h
        cases hm with
        | head _ =>
            exact Nat.le_trans (foldMinOption_some_le_init ys (min init m) v h)
                (Nat.min_le_right init m)
        | tail _ hm_ys =>
            exact ih (min init y) h hm_ys

/-- foldMinOption none layers = some v → 任意の m ∈ layers に対して v ≤ m -/
theorem foldMinOption_none_le (layers : List Nat) (v : Nat)
        (h : layers.foldl foldMinOption none = some v) (m : Nat) (hm : m ∈ layers) :
        v ≤ m := by
    cases layers with
    | nil => nomatch hm
    | cons y ys =>
        simp only [List.foldl_cons, foldMinOption] at h
        cases hm with
        | head _ => exact foldMinOption_some_le_init ys m v h
        | tail _ hm_ys => exact foldMinOption_some_le_mem ys y v h m hm_ys

/-- minLayerAtDir が some を返すなら、その方角・レイヤの位置が実在する -/
theorem minLayerAtDir_some_witness (u : FallingUnit) (dir : Direction) (l : Nat)
        (h : u.minLayerAtDir dir = some l) :
        ∃ p, p ∈ u.positions ∧ p.dir = dir ∧ p.layer = l := by
    simp only [FallingUnit.minLayerAtDir] at h
    change (u.positions.filterMap fun p =>
        if p.dir == dir then some p.layer else none).foldl foldMinOption none = some l at h
    have h_layers := foldMinOption_none_mem _ l h
    rw [List.mem_filterMap] at h_layers
    obtain ⟨p, hp_mem, hp_eq⟩ := h_layers
    by_cases hd : (p.dir == dir) = true
    · simp only [hd, ite_true] at hp_eq
      exact ⟨p, hp_mem, eq_of_beq hd, Option.some.inj hp_eq⟩
    · simp only [hd, ite_false, reduceCtorEq] at hp_eq

/-- 指定方角の位置が存在するなら minLayerAtDir は some -/
theorem minLayerAtDir_some_of_mem (u : FallingUnit) (dir : Direction) (p : QuarterPos)
        (hp : p ∈ u.positions) (hd : p.dir = dir) :
        ∃ l, u.minLayerAtDir dir = some l := by
    simp only [FallingUnit.minLayerAtDir]
    change ∃ l, (u.positions.filterMap fun q =>
        if q.dir == dir then some q.layer else none).foldl foldMinOption none = some l
    have h_ne : (u.positions.filterMap fun q =>
            if q.dir == dir then some q.layer else none) ≠ [] := by
        intro h_empty
        have : p.layer ∈ (u.positions.filterMap fun q =>
                if q.dir == dir then some q.layer else none) :=
            List.mem_filterMap.mpr ⟨p, hp, by simp only [hd, BEq.rfl, ↓reduceIte]⟩
        rw [h_empty] at this; exact absurd this List.not_mem_nil
    -- 非空リスト: 先頭を取得して foldl が some を返すことを示す
    have ⟨a, rest, hl⟩ : ∃ a rest, (u.positions.filterMap fun q =>
            if q.dir == dir then some q.layer else none) = a :: rest := by
        cases h_list : (u.positions.filterMap fun q =>
            if q.dir == dir then some q.layer else none) with
        | nil => exact absurd h_list h_ne
        | cons a rest => exact ⟨a, rest, rfl⟩
    rw [hl]
    simp only [List.foldl_cons]
    change ∃ l, rest.foldl foldMinOption (foldMinOption none a) = some l
    simp only [foldMinOption]
    exact foldMinOption_some_isSome rest a

/-- shouldProcessBefore u v = false のとき、共有方角の minLayerAtDir で u ≥ v -/
theorem shouldProcessBefore_false_minLayerAtDir_ge (u v : FallingUnit) (dir : Direction)
        (h : shouldProcessBefore u v = false)
        (lu lv : Nat)
        (hu : u.minLayerAtDir dir = some lu)
        (hv : v.minLayerAtDir dir = some lv) :
        lu ≥ lv := by
    -- shouldProcessBefore u v = false → Direction.all.any (fun dir => ...) = false
    -- 展開して dir ケース分析
    simp only [shouldProcessBefore, Direction.all, List.any_cons, List.any_nil, Bool.or_false] at h
    -- h は4方角の or = false。各方角でケース分け。
    rcases dir with _ | _ | _ | _ <;> simp_all only [FallingUnit.minLayerAtDir, beq_iff_eq, Bool.or_eq_false_iff, ge_iff_le, decide_eq_false_iff_not, not_lt]

/-- shouldProcessBefore 双方向 false + 位置非共有 → 方角列非共有
    （tied 要素は列を共有しない） -/
theorem tied_no_shared_dir (u v : FallingUnit)
        (h_tied_uv : shouldProcessBefore u v = false)
        (h_tied_vu : shouldProcessBefore v u = false)
        (h_disj : ∀ p, p ∈ u.positions → v.positions.any (· == p) = false) :
        ∀ p, p ∈ u.positions → v.positions.any (fun q => q.dir == p.dir) = false := by
    intro p hp
    -- v.positions.any (dir == p.dir) が true だと仮定して矛盾を導く
    -- Bool は Decidable なので cases で分場合分け
    cases h_any : v.positions.any (fun q => q.dir == p.dir) with
    | false => rfl
    | true =>
        -- v に p.dir を持つ位置 q が存在する
        obtain ⟨q, hq_mem, hq_dir⟩ := List.any_eq_true.mp h_any
        have hd : q.dir = p.dir := eq_of_beq hq_dir
        -- minLayerAtDir が some であることを示す
        obtain ⟨lu, hlu⟩ := minLayerAtDir_some_of_mem u p.dir p hp rfl
        obtain ⟨lv, hlv⟩ := minLayerAtDir_some_of_mem v p.dir q hq_mem hd
        -- shouldProcessBefore 双方 false → lu ≥ lv ∧ lv ≥ lu → lu = lv
        have h_ge := shouldProcessBefore_false_minLayerAtDir_ge u v p.dir h_tied_uv lu lv hlu hlv
        have h_le := shouldProcessBefore_false_minLayerAtDir_ge v u p.dir h_tied_vu lv lu hlv hlu
        have h_eq : lu = lv := by omega
        -- minLayerAtDir_some_witness: v に (lv, p.dir) の位置が存在
        obtain ⟨q', hq'_mem, hq'_dir, hq'_layer⟩ := minLayerAtDir_some_witness v p.dir lv hlv
        -- u に (lu, p.dir) の位置が存在
        obtain ⟨p', hp'_mem, hp'_dir, hp'_layer⟩ := minLayerAtDir_some_witness u p.dir lu hlu
        -- p' と q' は同じ (layer, dir) → q' = p'
        have h_qp : q' = p' := by
            have hl : q'.layer = p'.layer := by rw [hq'_layer, hp'_layer, h_eq]
            have hd' : q'.dir = p'.dir := by rw [hq'_dir, hp'_dir]
            exact match q', p', hl, hd' with
            | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl
        -- h_disj p' hp'_mem : v.positions.any (· == p') = false
        have h_p'_disj := h_disj p' hp'_mem
        -- だが q' ∈ v.positions で q' = p' → v.positions.any (· == p') = true
        have : v.positions.any (· == p') = true := by
            apply List.any_eq_true.mpr
            exact ⟨q', hq'_mem, h_qp ▸ beq_self_eq_true q'⟩
        rw [this] at h_p'_disj
        exact absurd h_p'_disj (by decide)

/-- tied + 位置非共有の逆方向版 -/
theorem tied_no_shared_dir_rev (u v : FallingUnit)
        (h_tied_uv : shouldProcessBefore u v = false)
        (h_tied_vu : shouldProcessBefore v u = false)
        (h_disj : ∀ p, p ∈ v.positions → u.positions.any (· == p) = false) :
        ∀ p, p ∈ v.positions → u.positions.any (fun q => q.dir == p.dir) = false :=
    tied_no_shared_dir v u h_tied_vu h_tied_uv h_disj

/-- 先頭 2 要素が方角素なら foldl 結果はスワップで不変 -/
theorem foldl_settle_head_swap (s : Shape) (u v : FallingUnit)
        (rest : List FallingUnit) (obs : List Layer)
        (h_uv : ∀ p, p ∈ u.positions → v.positions.any (fun q => q.dir == p.dir) = false)
        (h_vu : ∀ p, p ∈ v.positions → u.positions.any (fun q => q.dir == p.dir) = false) :
        (u :: v :: rest).foldl (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs =
        (v :: u :: rest).foldl (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs := by
    simp only [List.foldl_cons]
    congr 1
    exact settleStep_comm_ne_dir s obs u v h_uv h_vu

-- ============================================================
-- positions .any 拡張性（ext）補題群
-- ============================================================

/-- minLayerAtDir は positions .any にのみ依存する -/
theorem minLayerAtDir_ext {u1 u2 : FallingUnit}
        (h : ∀ p, u1.positions.any (· == p) = u2.positions.any (· == p))
        (dir : Direction) :
        u1.minLayerAtDir dir = u2.minLayerAtDir dir := by
    cases h1 : u1.minLayerAtDir dir with
    | none =>
        -- u1 に dir 方角の位置がない → u2 にもない
        cases h2 : u2.minLayerAtDir dir with
        | none => rfl
        | some l2 =>
            exfalso
            obtain ⟨p2, hp2_mem, hp2_dir, _⟩ := minLayerAtDir_some_witness u2 dir l2 h2
            -- p2 ∈ u2.positions → p2 ∈ u1.positions (by .any 等価)
            have hp2_in_u1 : p2 ∈ u1.positions :=
                mem_of_any_beq_eq h hp2_mem
            -- u1 に dir を持つ位置が存在 → minLayerAtDir ≠ none
            obtain ⟨l, hl⟩ := minLayerAtDir_some_of_mem u1 dir p2 hp2_in_u1 hp2_dir
            rw [hl] at h1; exact absurd h1 (by simp only [reduceCtorEq, not_false_eq_true])
    | some l1 =>
        cases h2 : u2.minLayerAtDir dir with
        | none =>
            exfalso
            obtain ⟨p1, hp1_mem, hp1_dir, _⟩ := minLayerAtDir_some_witness u1 dir l1 h1
            have hp1_in_u2 : p1 ∈ u2.positions :=
                mem_of_any_beq_eq (fun p => (h p).symm) hp1_mem
            obtain ⟨l, hl⟩ := minLayerAtDir_some_of_mem u2 dir p1 hp1_in_u2 hp1_dir
            rw [hl] at h2; exact absurd h2 (by simp only [reduceCtorEq, not_false_eq_true])
        | some l2 =>
            -- 両方 some → l1 = l2
            congr 1
            apply Nat.le_antisymm
            · -- l1 ≤ l2: l2 の witness p2 が u1 にも属し、l1 ≤ p2.layer
              obtain ⟨p2, hp2_mem, hp2_dir, hp2_layer⟩ :=
                  minLayerAtDir_some_witness u2 dir l2 h2
              have hp2_in_u1 : p2 ∈ u1.positions :=
                  mem_of_any_beq_eq h hp2_mem
              -- minLayerAtDir は dir フィルタ後の最小値 → l1 ≤ p2.layer
              -- p2 ∈ u1.positions ∧ p2.dir = dir → u1.minLayerAtDir dir ≤ p2.layer
              simp only [FallingUnit.minLayerAtDir] at h1
              change (u1.positions.filterMap fun p =>
                  if p.dir == dir then some p.layer else none).foldl
                  foldMinOption none = some l1 at h1
              have : p2.layer ∈ (u1.positions.filterMap fun p =>
                  if p.dir == dir then some p.layer else none) := by
                  rw [List.mem_filterMap]
                  exact ⟨p2, hp2_in_u1, by simp only [show (p2.dir == dir) = true from by
                      rw [hp2_dir]; exact BEq.rfl, ↓reduceIte]⟩
              rw [← hp2_layer]
              exact foldMinOption_none_le _ l1 h1 p2.layer this
            · obtain ⟨p1, hp1_mem, hp1_dir, hp1_layer⟩ :=
                  minLayerAtDir_some_witness u1 dir l1 h1
              have hp1_in_u2 : p1 ∈ u2.positions :=
                  mem_of_any_beq_eq (fun p => (h p).symm) hp1_mem
              simp only [FallingUnit.minLayerAtDir] at h2
              change (u2.positions.filterMap fun p =>
                  if p.dir == dir then some p.layer else none).foldl
                  foldMinOption none = some l2 at h2
              have : p1.layer ∈ (u2.positions.filterMap fun p =>
                  if p.dir == dir then some p.layer else none) := by
                  rw [List.mem_filterMap]
                  exact ⟨p1, hp1_in_u2, by simp only [show (p1.dir == dir) = true from by
                      rw [hp1_dir]; exact BEq.rfl, ↓reduceIte]⟩
              rw [← hp1_layer]
              exact foldMinOption_none_le _ l2 h2 p1.layer this

/-- shouldProcessBefore は positions .any にのみ依存する -/
theorem shouldProcessBefore_ext {u1 u2 v1 v2 : FallingUnit}
        (hu : ∀ p, u1.positions.any (· == p) = u2.positions.any (· == p))
        (hv : ∀ p, v1.positions.any (· == p) = v2.positions.any (· == p)) :
        shouldProcessBefore u1 v1 = shouldProcessBefore u2 v2 := by
    simp only [shouldProcessBefore]
    congr 1
    funext dir
    rw [minLayerAtDir_ext hu dir, minLayerAtDir_ext hv dir]

-- ============================================================
-- insertSorted / sortFallingUnits の pointwise .any 等価保存
-- ============================================================

/-- insertSorted の結果の長さ -/
theorem insertSorted_length (u : FallingUnit) (sorted : List FallingUnit) (fuel : Nat) :
        (insertSorted u sorted fuel).length = sorted.length + 1 := by
    induction fuel generalizing sorted with
    | zero => simp only [insertSorted, List.length_cons]
    | succ n ih =>
        cases sorted with
        | nil => simp only [insertSorted, List.length_cons, List.length_nil, Nat.zero_add]
        | cons v rest =>
            simp only [insertSorted]
            split
            · simp only [List.length_cons]
            · simp only [List.length_cons, ih rest]

/-- sortFallingUnits の結果の長さ -/
theorem sortFallingUnits_length (units : List FallingUnit) :
        (sortFallingUnits units).length = units.length := by
    exact (sortFallingUnits_perm units).length_eq

/-- positions .any 等価な要素を pointwise .any 等価なソート済みリストに挿入すると、
    結果も pointwise .any 等価になる -/
theorem insertSorted_pointwise_ext
        {u1 u2 : FallingUnit}
        (hu : ∀ p, u1.positions.any (· == p) = u2.positions.any (· == p))
        {sorted1 sorted2 : List FallingUnit}
        (h_len : sorted1.length = sorted2.length)
        (h_pw : ∀ (i : Nat) (hi : i < sorted1.length) (p : QuarterPos),
            (sorted1[i]'hi).positions.any (· == p) =
            (sorted2[i]'(h_len ▸ hi)).positions.any (· == p))
        (fuel : Nat) :
        (insertSorted u1 sorted1 fuel).length = (insertSorted u2 sorted2 fuel).length ∧
        ∀ (i : Nat) (hi : i < (insertSorted u1 sorted1 fuel).length) (p : QuarterPos),
            ((insertSorted u1 sorted1 fuel)[i]'hi).positions.any (· == p) =
            ((insertSorted u2 sorted2 fuel)[i]'(by
                rw [insertSorted_length] at hi ⊢
                rw [h_len] at hi; exact hi)).positions.any (· == p) := by
    induction fuel generalizing sorted1 sorted2 with
    | zero =>
        -- fuel = 0: insertSorted u sorted 0 = u :: sorted
        simp only [insertSorted]
        constructor
        · simp only [List.length_cons, h_len]
        · intro i hi p
          cases i with
          | zero => exact hu p
          | succ j => exact h_pw j (by simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi; omega) p
    | succ n ih =>
        cases sorted1 with
        | nil =>
            -- sorted1 = [] → sorted2 = []
            have : sorted2 = [] := by
                cases sorted2 with
                | nil => rfl
                | cons _ _ => simp only [List.length_nil, List.length_cons, Nat.right_eq_add, Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero, and_false] at h_len
            subst this
            simp only [insertSorted]
            exact ⟨rfl, fun i hi p => by cases i with | zero => exact hu p | succ j => simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_one_iff, Nat.add_eq_zero_iff, one_ne_zero, and_false] at hi⟩
        | cons v1 rest1 =>
            -- sorted1 = v1 :: rest1 → sorted2 = v2 :: rest2
            cases sorted2 with
            | nil => simp only [List.length_cons, List.length_nil, Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero, and_false] at h_len
            | cons v2 rest2 =>
                -- v1 と v2 は .any 等価 (i=0)
                have h_v : ∀ p, v1.positions.any (· == p) = v2.positions.any (· == p) :=
                    fun p => h_pw 0 (by simp only [List.length_cons, Nat.zero_lt_succ]) p
                -- rest1 と rest2 は pointwise .any 等価
                have h_rest_len : rest1.length = rest2.length := by simp only [List.length_cons, Nat.add_right_cancel_iff] at h_len; exact h_len
                have h_rest_pw : ∀ (i : Nat) (hi : i < rest1.length) (p : QuarterPos),
                        (rest1[i]'hi).positions.any (· == p) =
                        (rest2[i]'(h_rest_len ▸ hi)).positions.any (· == p) :=
                    fun i hi p => h_pw (i + 1) (by simp only [List.length_cons, Nat.add_lt_add_iff_right]; omega) p
                -- shouldProcessBefore の等価性
                have h_spb_uv : shouldProcessBefore u1 v1 = shouldProcessBefore u2 v2 :=
                    shouldProcessBefore_ext hu h_v
                -- 条件分岐: by_cases で分岐
                by_cases h1 : shouldProcessBefore u1 v1
                · -- shouldProcessBefore u1 v1 = true → shouldProcessBefore u2 v2 = true
                  have h1' : shouldProcessBefore u2 v2 = true := h_spb_uv ▸ h1
                  have lhs : insertSorted u1 (v1 :: rest1) (n + 1) = u1 :: v1 :: rest1 := by
                      show (if shouldProcessBefore u1 v1 then u1 :: v1 :: rest1
                          else v1 :: insertSorted u1 rest1 n) = _
                      simp only [h1, ↓reduceIte]
                  have rhs : insertSorted u2 (v2 :: rest2) (n + 1) = u2 :: v2 :: rest2 := by
                      show (if shouldProcessBefore u2 v2 then u2 :: v2 :: rest2
                          else _) = _
                      simp only [h1', ↓reduceIte]
                  simp only [lhs, rhs]
                  constructor
                  · simp only [List.length_cons, h_len]
                  · intro i hi p
                    cases i with
                    | zero => exact hu p
                    | succ j =>
                        cases j with
                        | zero => exact h_v p
                        | succ k =>
                            simp only [List.getElem_cons_succ]
                            exact h_pw (k + 1) (by simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi ⊢ ⊢; omega) p
                · -- shouldProcessBefore u1 v1 = false → スキップして再帰
                  simp only [Bool.not_eq_true] at h1
                  have h1' : shouldProcessBefore u2 v2 = false := h_spb_uv ▸ h1
                  have lhs : insertSorted u1 (v1 :: rest1) (n + 1) =
                      v1 :: insertSorted u1 rest1 n := by
                      show (if shouldProcessBefore u1 v1 then u1 :: v1 :: rest1
                          else v1 :: insertSorted u1 rest1 n) = _
                      simp only [h1, Bool.false_eq_true, ↓reduceIte]
                  have rhs : insertSorted u2 (v2 :: rest2) (n + 1) =
                      v2 :: insertSorted u2 rest2 n := by
                      show (if shouldProcessBefore u2 v2 then _
                          else v2 :: insertSorted u2 rest2 n) = _
                      simp only [h1', Bool.false_eq_true, ↓reduceIte]
                  simp only [lhs, rhs]
                  have ih_result := ih h_rest_len h_rest_pw
                  constructor
                  · simp only [List.length_cons, ih_result.1]
                  · intro i hi p
                    cases i with
                    | zero => exact h_v p
                    | succ j => exact ih_result.2 j (by simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi; exact hi) p

/-- sortFallingUnits は pointwise .any 等価な入力に対して pointwise .any 等価な出力を生む -/
theorem sortFallingUnits_pointwise_ext
        {l1 l2 : List FallingUnit}
        (h_len : l1.length = l2.length)
        (h_pw : ∀ (i : Nat) (hi : i < l1.length) (p : QuarterPos),
            (l1[i]'hi).positions.any (· == p) =
            (l2[i]'(h_len ▸ hi)).positions.any (· == p)) :
        (sortFallingUnits l1).length = (sortFallingUnits l2).length ∧
        ∀ (i : Nat) (hi : i < (sortFallingUnits l1).length) (p : QuarterPos),
            ((sortFallingUnits l1)[i]'hi).positions.any (· == p) =
            ((sortFallingUnits l2)[i]'(by
                rw [sortFallingUnits_length] at hi ⊢
                rw [h_len] at hi; exact hi)).positions.any (· == p) := by
    -- foldl の帰納法で pointwise 等価を保存する補助定理
    -- sortFallingUnits = foldl (fun sorted u => insertSorted u sorted (sorted.length + 1)) []
    -- l1, l2 に対する帰納法で acc1, acc2 を保持
    have key : ∀ (l1' l2' : List FallingUnit)
        (h_len' : l1'.length = l2'.length)
        (h_pw' : ∀ (i : Nat) (hi : i < l1'.length) (p : QuarterPos),
            (l1'[i]'hi).positions.any (· == p) =
            (l2'[i]'(h_len' ▸ hi)).positions.any (· == p))
        (acc1 acc2 : List FallingUnit)
        (ha_len : acc1.length = acc2.length)
        (ha_pw : ∀ (i : Nat) (hi : i < acc1.length) (p : QuarterPos),
            (acc1[i]'hi).positions.any (· == p) =
            (acc2[i]'(ha_len ▸ hi)).positions.any (· == p)),
        let res1 := l1'.foldl (fun sorted u => insertSorted u sorted (sorted.length + 1)) acc1
        let res2 := l2'.foldl (fun sorted u => insertSorted u sorted (sorted.length + 1)) acc2
        res1.length = res2.length ∧
        ∀ (i : Nat) (hi1 : i < res1.length) (hi2 : i < res2.length) (p : QuarterPos),
            (res1[i]'hi1).positions.any (· == p) =
            (res2[i]'hi2).positions.any (· == p) := by
      intro l1' l2' h_len' h_pw'
      induction l1' generalizing l2' with
      | nil =>
          have : l2' = [] := by cases l2' with | nil => rfl | cons _ _ => simp only [List.length_nil, List.length_cons, Nat.right_eq_add, Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero, and_false] at h_len'
          subst this
          intro acc1 acc2 ha_len ha_pw
          simp only [List.foldl]
          exact ⟨ha_len, fun i hi1 _hi2 p => ha_pw i hi1 p⟩
      | cons u1 rest1 ih =>
          cases l2' with
          | nil => simp only [List.length_cons, List.length_nil, Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero, and_false] at h_len'
          | cons u2 rest2 =>
              have h_rest_len : rest1.length = rest2.length := by simp only [List.length_cons, Nat.add_right_cancel_iff] at h_len'; exact h_len'
              have h_u : ∀ p, u1.positions.any (· == p) = u2.positions.any (· == p) :=
                  fun p => h_pw' 0 (by simp only [List.length_cons, Nat.zero_lt_succ]) p
              have h_rest_pw : ∀ (i : Nat) (hi : i < rest1.length) (p : QuarterPos),
                      (rest1[i]'hi).positions.any (· == p) =
                      (rest2[i]'(h_rest_len ▸ hi)).positions.any (· == p) :=
                  fun i hi p => h_pw' (i + 1) (by simp only [List.length_cons, Nat.add_lt_add_iff_right]; omega) p
              intro acc1 acc2 ha_len ha_pw
              simp only [List.foldl]
              have h_ins := insertSorted_pointwise_ext h_u ha_len ha_pw (acc1.length + 1)
              -- fuel の正規化: acc2.length + 1 = acc1.length + 1
              have h_rw : insertSorted u2 acc2 (acc2.length + 1) = insertSorted u2 acc2 (acc1.length + 1) :=
                  congrArg (insertSorted u2 acc2) (by omega)
              simp only [h_rw]
              exact ih rest2 h_rest_len h_rest_pw
                  (insertSorted u1 acc1 (acc1.length + 1))
                  (insertSorted u2 acc2 (acc1.length + 1))
                  h_ins.1 h_ins.2
    -- key を sortFallingUnits に適用
    simp only [sortFallingUnits]
    have result := key l1 l2 h_len h_pw [] [] rfl (fun _ hi => absurd hi (by simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true]))
    constructor
    · exact result.1
    · intro i hi p
      exact result.2 i hi _ p

-- ============================================================
-- placeLDGroups の pointwise .any 拡張性
-- ============================================================

/-- takeWhile の述語が同一なら結果長が一致（.any 等価 FU リスト上） -/
private theorem takeWhile_ld_length_eq (l1 l2 : List FallingUnit) (obs : List Layer) (d : Nat)
        (h_len : l1.length = l2.length)
        (h_any : ∀ (i : Nat) (hi : i < l1.length) (p : QuarterPos),
            (l1[i]'hi).positions.any (· == p) = (l2[i]'(h_len ▸ hi)).positions.any (· == p)) :
        (l1.takeWhile (fun u => landingDistance u obs == d)).length =
        (l2.takeWhile (fun u => landingDistance u obs == d)).length := by
    induction l1 generalizing l2 with
    | nil => match l2, h_len with | [], _ => rfl
    | cons u1 r1 ih =>
        match l2, h_len with
        | u2 :: r2, h_len =>
            have h_ld : landingDistance u1 obs = landingDistance u2 obs :=
                landingDistance_ext (fun p => h_any 0 (Nat.zero_lt_succ _) p) obs
            simp only [List.takeWhile_cons]
            rw [show (landingDistance u2 obs == d) = (landingDistance u1 obs == d) from by rw [h_ld]]
            split
            · exact congrArg (· + 1) (ih r2 (Nat.succ_injective h_len)
                  (fun i hi p => h_any (i + 1) (Nat.succ_lt_succ hi) p))
            · rfl

/-- dropWhile の述語が同一なら結果長が一致（.any 等価 FU リスト上） -/
private theorem dropWhile_ld_length_eq (l1 l2 : List FallingUnit) (obs : List Layer) (d : Nat)
        (h_len : l1.length = l2.length)
        (h_any : ∀ (i : Nat) (hi : i < l1.length) (p : QuarterPos),
            (l1[i]'hi).positions.any (· == p) = (l2[i]'(h_len ▸ hi)).positions.any (· == p)) :
        (l1.dropWhile (fun u => landingDistance u obs == d)).length =
        (l2.dropWhile (fun u => landingDistance u obs == d)).length := by
    induction l1 generalizing l2 with
    | nil => match l2, h_len with | [], _ => rfl
    | cons u1 r1 ih =>
        match l2, h_len with
        | u2 :: r2, h_len =>
            have h_ld : landingDistance u1 obs = landingDistance u2 obs :=
                landingDistance_ext (fun p => h_any 0 (Nat.zero_lt_succ _) p) obs
            simp only [List.dropWhile_cons]
            rw [show (landingDistance u2 obs == d) = (landingDistance u1 obs == d) from by rw [h_ld]]
            split
            · exact ih r2 (Nat.succ_injective h_len)
                  (fun i hi p => h_any (i + 1) (Nat.succ_lt_succ hi) p)
            · exact h_len

/-- foldl + placeFallingUnit の pointwise .any 拡張性（固定 d） -/
private theorem foldl_pfu_fixed_d_pointwise_ext (s : Shape)
        (l1 l2 : List FallingUnit) (obs : List Layer) (d : Nat)
        (h_len : l1.length = l2.length)
        (h_any : ∀ (i : Nat) (hi : i < l1.length) (p : QuarterPos),
            (l1[i]'hi).positions.any (· == p) = (l2[i]'(h_len ▸ hi)).positions.any (· == p))
        (hd : ∀ u ∈ l1, d ≤ u.minLayer) :
        l1.foldl (fun acc fu => placeFallingUnit s acc fu d) obs =
        l2.foldl (fun acc fu => placeFallingUnit s acc fu d) obs := by
    induction l1 generalizing l2 obs with
    | nil => match l2, h_len with | [], _ => rfl
    | cons u1 r1 ih =>
        match l2, h_len with
        | u2 :: r2, h_len =>
            simp only [List.foldl_cons]
            have h_head : ∀ p, u1.positions.any (· == p) = u2.positions.any (· == p) :=
                fun p => h_any 0 (Nat.zero_lt_succ _) p
            rw [placeFallingUnit_ext h_head s obs d (hd u1 (.head _))]
            exact ih r2 (placeFallingUnit s obs u2 d) (Nat.succ_injective h_len)
                (fun i hi p => h_any (i + 1) (Nat.succ_lt_succ hi) p)
                (fun u hu => hd u (.tail _ hu))

/-- placeLDGroups の pointwise .any 拡張性:
    同じ長さで位置ごとの .any が一致する 2 つの FU リストは、
    同じ obs に対して同じ placeLDGroups 結果を与える -/
theorem placeLDGroups_ext (s : Shape) (l1 l2 : List FallingUnit)
        (obs : List Layer)
        (h_len : l1.length = l2.length)
        (h_any : ∀ (i : Nat) (hi : i < l1.length) (p : QuarterPos),
            (l1[i]'hi).positions.any (· == p) = (l2[i]'(h_len ▸ hi)).positions.any (· == p))
        (hd1 : ∀ u ∈ l1, 1 ≤ u.minLayer)
        (hd2 : ∀ u ∈ l2, 1 ≤ u.minLayer) :
        placeLDGroups s l1 obs = placeLDGroups s l2 obs :=
    match l1, l2, h_len, h_any, hd1, hd2 with
    | [], [], _, _, _, _ => rfl
    | f1 :: r1, f2 :: r2, h_len, h_any, hd1, hd2 => by
        have h_head : ∀ p, f1.positions.any (· == p) = f2.positions.any (· == p) :=
            fun p => h_any 0 (Nat.zero_lt_succ _) p
        have h_ld : landingDistance f1 obs = landingDistance f2 obs :=
            landingDistance_ext h_head obs
        simp only [placeLDGroups, h_ld]
        let d := landingDistance f2 obs
        let P := fun u => landingDistance u obs == d
        -- takeWhile / dropWhile 長さの一致
        have h_tw_len : ((f1::r1).takeWhile P).length = ((f2::r2).takeWhile P).length :=
            takeWhile_ld_length_eq (f1::r1) (f2::r2) obs d h_len h_any
        have h_dw_len : ((f1::r1).dropWhile P).length = ((f2::r2).dropWhile P).length :=
            dropWhile_ld_length_eq (f1::r1) (f2::r2) obs d h_len h_any
        -- takeWhile の pointwise .any
        have h_tw_any : ∀ (i : Nat) (hi : i < ((f1::r1).takeWhile P).length) (p : QuarterPos),
                (((f1::r1).takeWhile P)[i]'hi).positions.any (· == p) =
                (((f2::r2).takeWhile P)[i]'(h_tw_len ▸ hi)).positions.any (· == p) := by
            intro i hi p
            rw [List.IsPrefix.getElem (List.takeWhile_prefix P) hi,
                List.IsPrefix.getElem (List.takeWhile_prefix P) (h_tw_len ▸ hi)]
            exact h_any i (Nat.lt_of_lt_of_le hi (List.takeWhile_prefix P).length_le) p
        -- takeWhile グループ: d ≤ u.minLayer
        have h_tw_d : ∀ u ∈ (f1::r1).takeWhile P, d ≤ u.minLayer := by
            intro u hu
            have h_pu : P u = true := by
                generalize f1 :: r1 = l at hu
                induction l with
                | nil => simp at hu
                | cons x xs ih =>
                    simp only [List.takeWhile_cons] at hu
                    split at hu
                    · simp only [List.mem_cons] at hu
                      rcases hu with rfl | h <;> [assumption; exact ih h]
                    · simp at hu
            have h_eq : landingDistance u obs = d := beq_iff_eq.mp h_pu
            calc d = landingDistance u obs := h_eq.symm
                _ ≤ u.minLayer := landingDistance_le_minLayer u obs
        -- foldl の等価性
        rw [foldl_pfu_fixed_d_pointwise_ext s
            ((f1::r1).takeWhile P) ((f2::r2).takeWhile P)
            obs d h_tw_len h_tw_any h_tw_d]
        -- dropWhile 再帰
        let k := ((f1::r1).takeWhile P).length
        have h_sum : k + ((f1::r1).dropWhile P).length = (f1::r1).length := by
            have := congrArg List.length (@List.takeWhile_append_dropWhile _ P (f1::r1))
            simp only [List.length_append] at this; omega
        have h_dw_any : ∀ (i : Nat) (hi : i < ((f1::r1).dropWhile P).length) (p : QuarterPos),
                (((f1::r1).dropWhile P)[i]'hi).positions.any (· == p) =
                (((f2::r2).dropWhile P)[i]'(h_dw_len ▸ hi)).positions.any (· == p) := by
            intro i hi p
            have h1 : ((f1::r1).dropWhile P)[i] =
                    (f1::r1)[(f1::r1).length - ((f1::r1).dropWhile P).length + i] :=
                List.IsSuffix.getElem (List.dropWhile_suffix P) hi
            have h2 : ((f2::r2).dropWhile P)[i]'(h_dw_len ▸ hi) =
                    (f2::r2)[(f2::r2).length - ((f2::r2).dropWhile P).length + i]'(by
                        have := (List.dropWhile_suffix (p := P) (l := f2::r2)).length_le; omega) :=
                List.IsSuffix.getElem (List.dropWhile_suffix P) (h_dw_len ▸ hi)
            rw [h1, h2]
            -- 両方のオフセットは k に等しい
            have h_off1 : (f1::r1).length - ((f1::r1).dropWhile P).length = k := by omega
            have h_off2 : (f2::r2).length - ((f2::r2).dropWhile P).length = k := by
                have h_sum2 := congrArg List.length (@List.takeWhile_append_dropWhile _ P (f2::r2))
                simp only [List.length_append] at h_sum2; omega
            simp only [h_off1, h_off2]
            exact h_any (k + i) (by omega) p
        exact placeLDGroups_ext s _ _ _ h_dw_len h_dw_any
            (fun u hu => hd1 u ((List.dropWhile_suffix P).subset hu))
            (fun u hu => hd2 u ((List.dropWhile_suffix P).subset hu))
    termination_by l1.length
    decreasing_by
        show ((f1 :: r1).dropWhile P).length < (f1 :: r1).length
        have h_Pf1 : P f1 = true := show (landingDistance f1 obs == d) = true from
            beq_iff_eq.mpr h_ld
        simp only [List.dropWhile_cons, h_Pf1, ↓reduceIte, List.length_cons]
        exact Nat.lt_succ_of_le (List.dropWhile_suffix _).length_le

/-! ## Length preservation of placeFallingUnit / placeLDGroups -/

/-- `placeFallingUnit` は obstacle list の長さを保存する。
    前提: landing lay = p.layer - d が obs の範囲内（p.layer < obs.length, d ≤ p.layer）。-/
private theorem placeFallingUnit_length (s : Shape) (obs : List Layer) (u : FallingUnit) (d : Nat)
    (h_d : ∀ p ∈ u.positions, p.layer < obs.length) (h_le : ∀ p ∈ u.positions, d ≤ p.layer) :
    (placeFallingUnit s obs u d).length = obs.length := by
  simp only [placeFallingUnit]
  suffices h : ∀ (ps : List QuarterPos) (acc : List Layer),
      (∀ p ∈ ps, p.layer < obs.length) → (∀ p ∈ ps, d ≤ p.layer) → acc.length = obs.length →
      (ps.foldl (fun acc p => match QuarterPos.getQuarter s p with
          | some q => placeQuarter acc (p.layer - d) p.dir q | none => acc) acc).length = obs.length from
    h u.positions obs h_d h_le rfl
  intro ps; induction ps with
  | nil => intros; simpa
  | cons p ps ih =>
    intro acc hl_ps hle_ps hacc; simp only [List.foldl_cons]; apply ih
    · intro q hq; exact hl_ps q (List.mem_cons_of_mem _ hq)
    · intro q hq; exact hle_ps q (List.mem_cons_of_mem _ hq)
    · split
      · rename_i q _
        rw [placeQuarter_length, hacc]
        have hp_lt := hl_ps p (List.mem_cons.mpr (Or.inl rfl))
        have hp_le := hle_ps p (List.mem_cons.mpr (Or.inl rfl))
        simp [Nat.max_eq_left (by omega : p.layer - d + 1 ≤ obs.length)]
      · exact hacc

/-- `placeFallingUnit` の foldl も長さを保存する。-/
private theorem foldl_placeFallingUnit_length (s : Shape) (d : Nat) (fus : List FallingUnit)
    (obs : List Layer)
    (h_d : ∀ u ∈ fus, ∀ p ∈ u.positions, p.layer < obs.length)
    (h_le : ∀ u ∈ fus, ∀ p ∈ u.positions, d ≤ p.layer) :
    (fus.foldl (fun acc fu => placeFallingUnit s acc fu d) obs).length = obs.length := by
  suffices h : ∀ (fus : List FallingUnit) (acc : List Layer),
      (∀ u ∈ fus, ∀ p ∈ u.positions, p.layer < obs.length) →
      (∀ u ∈ fus, ∀ p ∈ u.positions, d ≤ p.layer) → acc.length = obs.length →
      (fus.foldl (fun acc fu => placeFallingUnit s acc fu d) acc).length = obs.length from
    h fus obs h_d h_le rfl
  intro fus; induction fus with
  | nil => intros; simpa
  | cons u fus ih =>
    intro acc hu_d hu_le hacc; simp only [List.foldl_cons]; apply ih
    · intro v hv p hp; exact hu_d v (List.mem_cons_of_mem _ hv) p hp
    · intro v hv p hp; exact hu_le v (List.mem_cons_of_mem _ hv) p hp
    · rw [← hacc]; apply placeFallingUnit_length
      · intro p hp; rw [hacc]; exact hu_d u (List.mem_cons.mpr (Or.inl rfl)) p hp
      · intro p hp; exact hu_le u (List.mem_cons.mpr (Or.inl rfl)) p hp

private theorem mem_takeWhile_pred {α : Type*} (p : α → Bool) (l : List α) (x : α)
    (h : x ∈ l.takeWhile p) : p x = true := by
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    simp only [List.takeWhile] at h
    split at h
    · simp at h; rcases h with rfl | htl
      · rename_i hp; exact hp
      · exact ih htl
    · simp at h

/-- `placeLDGroups` は obstacle list の長さを保存する。-/
theorem placeLDGroups_length (s : Shape) (sorted : List FallingUnit) (obs : List Layer)
    (h_lt : ∀ u ∈ sorted, ∀ p ∈ u.positions, p.layer < obs.length)
    (h_le : ∀ u ∈ sorted, ∀ p ∈ u.positions, landingDistance u obs ≤ p.layer) :
    (placeLDGroups s sorted obs).length = obs.length := by
  induction sorted, obs using placeLDGroups.induct s with
  | case1 obs => simp [placeLDGroups]
  | case2 obs v rest d group remaining obs' ih =>
    rw [placeLDGroups]
    have h_obs'_len : obs'.length = obs.length := by
      apply foldl_placeFallingUnit_length
      · intro u hu p hp
        exact h_lt u (List.Sublist.subset (List.takeWhile_sublist _) hu) p hp
      · intro u hu p hp
        have hd_eq : landingDistance u obs = d := by
          have hpred := mem_takeWhile_pred (fun u => landingDistance u obs == d) (v :: rest) u hu
          exact beq_iff_eq.mp hpred
        rw [← hd_eq]
        exact le_trans (landingDistance_le_minLayer u obs) (minLayer_le_layer hp u.minLayer le_rfl)
    rw [← h_obs'_len]; apply ih
    · intro u hu p hp; rw [h_obs'_len]; exact h_lt u (List.Sublist.subset (List.dropWhile_sublist _) hu) p hp
    · intro u hu p hp
      exact le_trans (landingDistance_le_minLayer u obs') (minLayer_le_layer hp u.minLayer le_rfl)

open Gravity in
private theorem landing_sum_eq_gls (group : List FallingUnit) (d : Nat) :
    (List.map (fun ld => ld.1 + 1)
        (List.flatMap (fun u => List.map (fun p => (p.layer - d, p.dir)) u.positions) group)).sum =
        ((group.flatMap FallingUnit.positions).map (fun p => p.layer - d + 1)).sum := by
  simp only [List.map_flatMap, List.map_map]; rfl

private theorem mem_tw_sat {α : Type*} (P : α → Bool) (l : List α) (a : α)
    (h : a ∈ l.takeWhile P) : P a = true := by
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    simp only [List.takeWhile_cons] at h
    split at h
    next hp => simp only [List.mem_cons] at h; rcases h with rfl | htl; exact hp; exact ih htl
    next => simp at h

theorem placeLDGroupsLandings_sum_succ_le (s : Shape) (sorted : List FallingUnit) (obs : List Layer)
    (h_ne : sorted ≠ []) (h_ml : ∀ u ∈ sorted, u.minLayer ≥ 1)
    (h_pne : ∀ u ∈ sorted, u.positions ≠ []) :
    ((placeLDGroupsLandings s sorted obs).map (fun ld => ld.1 + 1)).sum + 1 ≤
      ((sorted.flatMap FallingUnit.positions).map (fun p => p.layer + 1)).sum := by
  induction sorted, obs using placeLDGroups.induct s with
  | case1 obs => exact absurd rfl h_ne
  | case2 obs v rest d group remaining obs' ih =>
    rw [placeLDGroupsLandings.eq_2, List.map_append, List.sum_append]
    simp only [
      show landingDistance v obs = d from rfl,
      show (List.takeWhile (fun u => landingDistance u obs == d) (v :: rest)) = group from rfl,
      show (List.dropWhile (fun u => landingDistance u obs == d) (v :: rest)) = remaining from rfl,
      show (List.foldl (fun acc fu => placeFallingUnit s acc fu d) obs group) = obs' from rfl]
    have h_d_ge : d ≥ 1 := landingDistance_ge_one v obs (h_ml v (List.mem_cons.mpr (Or.inl rfl)))
    have h_rsub : ∀ u ∈ remaining, u ∈ v :: rest := (List.dropWhile_suffix _).subset
    have h_dl : ∀ p ∈ group.flatMap FallingUnit.positions, d ≤ p.layer := by
      intro p hp; obtain ⟨u, hu, hpu⟩ := List.mem_flatMap.mp hp
      have hd_eq := beq_iff_eq.mp (mem_tw_sat (fun u => landingDistance u obs == d) (v :: rest) u hu)
      rw [← hd_eq]
      exact le_trans (landingDistance_le_minLayer u obs) (minLayer_le_layer hpu u.minLayer le_rfl)
    have h_vine : v ∈ group := by
      simp only [group, List.takeWhile_cons,
        show (landingDistance v obs == d) = true from beq_iff_eq.mpr rfl, ↓reduceIte]
      exact List.mem_cons.mpr (Or.inl rfl)
    have h_gpne : group.flatMap FallingUnit.positions ≠ [] := by
      obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil v.positions (h_pne v (List.mem_cons.mpr (Or.inl rfl)))
      exact List.ne_nil_of_mem (List.mem_flatMap.mpr ⟨v, h_vine, hp⟩)
    have h_tele := sum_map_layer_landing_telescope (group.flatMap FallingUnit.positions) d h_dl
    have h_gb : ((group.flatMap FallingUnit.positions).map (fun p => p.layer - d + 1)).sum + 1 ≤
        ((group.flatMap FallingUnit.positions).map (fun p => p.layer + 1)).sum := by
      have h_nd := Nat.mul_pos (List.length_pos_of_ne_nil h_gpne) h_d_ge
      rw [← h_tele]
      exact Nat.add_le_add_left h_nd _
    have h_gr_eq : v :: rest = group ++ remaining := by
      simp [group, remaining, List.takeWhile_append_dropWhile]
    have h_rhs_split : (((v :: rest).flatMap FallingUnit.positions).map (fun p => p.layer + 1)).sum =
        ((group.flatMap FallingUnit.positions).map (fun p => p.layer + 1)).sum +
        ((remaining.flatMap FallingUnit.positions).map (fun p => p.layer + 1)).sum := by
      rw [h_gr_eq, List.flatMap_append, List.map_append, List.sum_append]
    have h_gls := landing_sum_eq_gls group d
    by_cases h_rem : remaining = []
    · simp only [h_rem, List.map_nil, List.sum_nil, add_zero,
        placeLDGroupsLandings.eq_1]
      rw [h_gls, h_rhs_split]
      simp only [h_rem, List.flatMap_nil, List.map_nil, List.sum_nil, add_zero]
      exact h_gb
    · have h_rb := ih h_rem (fun u hu => h_ml u (h_rsub u hu)) (fun u hu => h_pne u (h_rsub u hu))
      rw [h_gls, h_rhs_split]
      omega



end Gravity
