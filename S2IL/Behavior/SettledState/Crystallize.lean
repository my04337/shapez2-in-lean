-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Behavior.Gravity
import S2IL.Behavior.CrystalGenerator

-- Crystallize の安定状態保存
-- ============================================================

namespace Gravity

/-- fillQuarter の結果は isEmpty = false -/
private theorem fillQuarter_not_isEmpty (q : Quarter) (c : Color) :
        (CrystalGenerator.fillQuarter q c).isEmpty = false := by
    cases q <;> rfl

/-- getDir と fillLayer の関係 -/
private theorem getDir_fillLayer (l : Layer) (d : Direction) (c : Color) :
        QuarterPos.getDir (CrystalGenerator.fillLayer l c) d =
        CrystalGenerator.fillQuarter (QuarterPos.getDir l d) c := by
    cases d <;> rfl

/-- crystallize 後の layerCount は不変 -/
private theorem layerCount_crystallize (s : Shape) (c : Color) :
        (s.crystallize c).layerCount = s.layerCount := by
    simp only [Shape.crystallize, Shape.mapLayers, Shape.layerCount, List.length_map]

/-- crystallize 後の getQuarter -/
private theorem getQuarter_crystallize (s : Shape) (pos : QuarterPos) (c : Color)
        (h : pos.layer < s.layerCount) :
        pos.getQuarter (s.crystallize c) =
        some (CrystalGenerator.fillQuarter
            (QuarterPos.getDir s.layers[pos.layer] pos.dir) c) := by
    simp only [QuarterPos.getQuarter, Shape.crystallize, Shape.mapLayers]
    have h' : pos.layer < s.layers.length := h
    rw [show s.layers.map (CrystalGenerator.fillLayer · c) = s.layers.map (fun x => CrystalGenerator.fillLayer x c) from rfl]
    rw [List.getElem?_map]
    simp only [show s.layers[pos.layer]? = some s.layers[pos.layer] from List.getElem?_eq_getElem h']
    exact congrArg some (getDir_fillLayer s.layers[pos.layer] pos.dir c)

/-- crystallize 後の垂直 isGroundingContact -/
private theorem isGroundingContact_crystallize_vertical (s : Shape) (c : Color)
        (d : Direction) (k : Nat) (hk : k + 1 < s.layerCount) :
        isGroundingContact (s.crystallize c) ⟨k, d⟩ ⟨k + 1, d⟩ = true := by
    have hk' : k < s.layerCount := Nat.lt_of_succ_lt hk
    simp only [isGroundingContact]
    rw [getQuarter_crystallize s ⟨k, d⟩ c hk', getQuarter_crystallize s ⟨k + 1, d⟩ c hk]
    simp only [fillQuarter_not_isEmpty, Bool.not_false, Bool.true_and]
    apply Bool.or_eq_true_iff.mpr
    left; apply Bool.and_eq_true_iff.mpr
    exact ⟨BEq.rfl, by
        simp only [LayerIndex.verticallyAdjacent]
        exact Bool.or_eq_true_iff.mpr (Or.inl BEq.rfl)⟩

/-- crystallize 後、⟨0, d⟩ から ⟨i, d⟩ への GenericReachable -/
private theorem reachable_from_zero_crystallize (s : Shape) (c : Color)
        (d : Direction) (i : Nat) (hi : i < s.layerCount) :
        GenericReachable (isUpwardGroundingContact (s.crystallize c)) ⟨0, d⟩ ⟨i, d⟩ := by
    induction i with
    | zero => exact .refl
    | succ n ih =>
        have hn : n < s.layerCount := Nat.lt_of_succ_lt hi
        exact (ih hn).trans
            (.step (isGroundingContact_to_isUpwardGroundingContact
                (isGroundingContact_crystallize_vertical s c d n hi)
                (Nat.le_succ n)) .refl)

/-- crystallize 後、⟨0, d⟩ は有効なシード -/
private theorem seed_valid_crystallize (s : Shape) (c : Color) (d : Direction)
        (h : 0 < s.layerCount) :
        ⟨0, d⟩ ∈ (QuarterPos.allValid (s.crystallize c)).filter (fun q =>
            q.layer == 0 && match q.getQuarter (s.crystallize c) with
            | some q => !q.isEmpty | none => false) := by
    rw [List.mem_filter]
    constructor
    · have h_any := (allValid_any_iff_layer' (s.crystallize c) ⟨0, d⟩).mpr
          (by rw [layerCount_crystallize]; exact h)
      rw [List.any_eq_true] at h_any
      obtain ⟨y, hy, hye⟩ := h_any; exact eq_of_beq hye ▸ hy
    · simp only [BEq.rfl, Bool.true_and]
      rw [getQuarter_crystallize s ⟨0, d⟩ c h]
      simp only [fillQuarter_not_isEmpty, Bool.not_false]

/-- crystallize 後、全有効位置が grounded -/
private theorem all_grounded_crystallize (s : Shape) (c : Color) (p : QuarterPos)
        (hp : p.layer < s.layerCount) :
        p ∈ groundedPositions (s.crystallize c) := by
    have h0 : 0 < s.layerCount := Nat.lt_of_le_of_lt (Nat.zero_le _) hp
    have h_seed := seed_valid_crystallize s c p.dir h0
    have h_reach := reachable_from_zero_crystallize s c p.dir p.layer hp
    have h_any := groundedPositionsList_complete (s.crystallize c)
        ⟨0, p.dir⟩ p h_seed
        (h_reach.mono (fun _ _ h => Gravity.groundingEdge_of_isUpwardGroundingContact h))
    simp only [groundedPositions, List.mem_toFinset]
    exact (any_beq_iff_mem _ p).mp h_any

/-- crystallize 後は floatingUnits が空 -/
theorem floatingUnits_crystallize_eq (s : Shape) (c : Color) :
        floatingUnits (s.crystallize c) = [] := by
    -- 背理法: floatingUnits が非空なら矛盾を導く
    by_contra h
    have h_ne : (floatingUnits (s.crystallize c)).isEmpty = false := by
        cases hfl : (floatingUnits (s.crystallize c)) with
        | nil => contradiction
        | cons _ _ => rfl
    obtain ⟨p, h_valid, _, h_ug⟩ :=
        floatingUnits_nonempty_implies_exists_ungrounded (s.crystallize c) h_ne
    rw [layerCount_crystallize] at h_valid
    exact h_ug (all_grounded_crystallize s c p h_valid)

end Gravity


namespace Shape

/-- crystallize (結晶化) の結果は、入力の安定状態に関わらず常に安定状態。
    crystallize は全象限を非空にするため、浮遊ユニットが存在しない -/
theorem IsSettled_crystallize (s : Shape) (c : Color) :
        (s.crystallize c).IsSettled := by
    simp only [IsSettled]
    exact Gravity.floatingUnits_crystallize_eq s c


end Shape

