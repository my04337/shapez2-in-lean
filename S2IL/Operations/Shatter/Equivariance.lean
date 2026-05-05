import S2IL.Operations.Shatter.Defs

/-!
# S2IL.Operations.Shatter.Equivariance

砕け散り操作の等変性層。
-/

namespace S2IL

private theorem decide_congr {P Q : Prop} [Decidable P] [Decidable Q]
    (h : P ↔ Q) : decide P = decide Q := by
  by_cases hP : P
  · simp [hP, h.mp hP]
  · have hQ : ¬ Q := fun hQ => hP (h.mpr hQ)
    simp [hP, hQ]

/-- `shatterMask` と CW 回転は、述語の方角 +1 シフトで可換: `P p = P' p.rotateCW`。 -/
theorem Shape.shatterMask.rotateCW_comm (s : Shape) {P P' : QuarterPos → Bool}
    (h : ∀ p, P p = P' p.rotateCW) :
    (s.shatterMask P).rotateCW = s.rotateCW.shatterMask P' := by
  unfold Shape.shatterMask
  exact Shatter.Internal.shatterMaskFrom.rotateCW_eq (fun k d => h (k, d)) 0 s

/-- `shatterMask` と 180° 回転は CW を 2 段重ねた系。 -/
theorem Shape.shatterMask.rotate180_comm (s : Shape) {P P' : QuarterPos → Bool}
    (h : ∀ p, P p = P' p.rotateCW.rotateCW) :
    (s.shatterMask P).rotate180 = s.rotate180.shatterMask P' := by
  show (s.shatterMask P).rotateCW.rotateCW = s.rotateCW.rotateCW.shatterMask P'
  rw [Shape.shatterMask.rotateCW_comm (P' := fun p => P' p.rotateCW) s (fun p => h p),
      Shape.shatterMask.rotateCW_comm (P' := P') s.rotateCW (fun _ => rfl)]

/-- `shatterMask` と CCW 回転は CW を 3 段重ねた系。 -/
theorem Shape.shatterMask.rotateCCW_comm (s : Shape) {P P' : QuarterPos → Bool}
    (h : ∀ p, P p = P' p.rotateCW.rotateCW.rotateCW) :
    (s.shatterMask P).rotateCCW = s.rotateCCW.shatterMask P' := by
  show (s.shatterMask P).rotateCW.rotateCW.rotateCW = s.rotateCW.rotateCW.rotateCW.shatterMask P'
  rw [Shape.shatterMask.rotateCW_comm (P' := fun p => P' p.rotateCW.rotateCW) s (fun p => h p),
      Shape.shatterMask.rotateCW_comm (P' := fun p => P' p.rotateCW) s.rotateCW (fun _ => rfl),
      Shape.shatterMask.rotateCW_comm (P' := P') s.rotateCW.rotateCW (fun _ => rfl)]

/-- `shatterOnFall` と CW 回転は可換（位置リストも CW 回転）。 -/
theorem Shape.shatterOnFall.rotateCW_comm (s : Shape) (ps : List QuarterPos) :
    (s.shatterOnFall ps).rotateCW =
      s.rotateCW.shatterOnFall (ps.map QuarterPos.rotateCW) := by
  unfold Shape.shatterOnFall
  apply Shape.shatterMask.rotateCW_comm
  intro p
  apply decide_congr
  unfold IsShatteredOnFall
  constructor
  · rintro ⟨t, hMem, hFrag, hRel⟩
    refine ⟨t.rotateCW, List.mem_map.mpr ⟨t, hMem, rfl⟩, ?_, ?_⟩
    · rw [QuarterPos.getQuarter_rotateCW]; exact hFrag
    · exact (CrystalBondClusterRel.rotateCW s t p).mpr hRel
  · rintro ⟨t', hMem', hFrag', hRel'⟩
    rcases List.mem_map.mp hMem' with ⟨t, hMem, rfl⟩
    refine ⟨t, hMem, ?_, ?_⟩
    · rw [QuarterPos.getQuarter_rotateCW] at hFrag'; exact hFrag'
    · exact (CrystalBondClusterRel.rotateCW s t p).mp hRel'

/-- `shatterOnFall` と 180° 回転は可換（CW の系）。 -/
theorem Shape.shatterOnFall.rotate180_comm (s : Shape) (ps : List QuarterPos) :
    (s.shatterOnFall ps).rotate180 =
      s.rotate180.shatterOnFall (ps.map (QuarterPos.rotateCW ∘ QuarterPos.rotateCW)) := by
  show (s.shatterOnFall ps).rotateCW.rotateCW = _
  rw [Shape.shatterOnFall.rotateCW_comm, Shape.shatterOnFall.rotateCW_comm,
      List.map_map]
  rfl

/-- `shatterOnFall` と CCW 回転は可換（CW の系）。 -/
theorem Shape.shatterOnFall.rotateCCW_comm (s : Shape) (ps : List QuarterPos) :
    (s.shatterOnFall ps).rotateCCW =
      s.rotateCCW.shatterOnFall
        (ps.map (QuarterPos.rotateCW ∘ QuarterPos.rotateCW ∘ QuarterPos.rotateCW)) := by
  show (s.shatterOnFall ps).rotateCW.rotateCW.rotateCW = _
  rw [Shape.shatterOnFall.rotateCW_comm, Shape.shatterOnFall.rotateCW_comm,
      Shape.shatterOnFall.rotateCW_comm, List.map_map, List.map_map]
  rfl

/-- `shatterTopCrystals` と CW 回転は可換（しきい値は不変）。 -/
theorem Shape.shatterTopCrystals.rotateCW_comm (s : Shape) (threshold : Nat) :
    (s.shatterTopCrystals threshold).rotateCW =
      s.rotateCW.shatterTopCrystals threshold := by
  unfold Shape.shatterTopCrystals
  apply Shape.shatterMask.rotateCW_comm
  intro p
  apply decide_congr
  unfold IsShatteredOnTruncate
  constructor
  · rintro ⟨t, hLayer, hCry, hRel⟩
    refine ⟨t.rotateCW, ?_, ?_, ?_⟩
    · simpa [QuarterPos.rotateCW_fst] using hLayer
    · rw [QuarterPos.getQuarter_rotateCW]; exact hCry
    · exact (CrystalBondClusterRel.rotateCW s t p).mpr hRel
  · rintro ⟨t', hLayer', hCry', hRel'⟩
    refine ⟨t'.rotateCCW, ?_, ?_, ?_⟩
    · simpa [QuarterPos.rotateCCW_fst] using hLayer'
    · rw [show t' = t'.rotateCCW.rotateCW from (QuarterPos.rotateCW_rotateCCW t').symm] at hCry'
      rw [QuarterPos.getQuarter_rotateCW] at hCry'
      exact hCry'
    · have hr : CrystalBondClusterRel s.rotateCW t'.rotateCCW.rotateCW p.rotateCW := by
        rw [QuarterPos.rotateCW_rotateCCW]; exact hRel'
      exact (CrystalBondClusterRel.rotateCW s t'.rotateCCW p).mp hr

/-- `shatterTopCrystals` と 180° 回転は可換（CW の系）。 -/
theorem Shape.shatterTopCrystals.rotate180_comm (s : Shape) (threshold : Nat) :
    (s.shatterTopCrystals threshold).rotate180 =
      s.rotate180.shatterTopCrystals threshold := by
  simp [Shape.rotate180_eq_rotateCW_rotateCW, Shape.shatterTopCrystals.rotateCW_comm]

/-- `shatterTopCrystals` と CCW 回転は可換（CW の系）。 -/
theorem Shape.shatterTopCrystals.rotateCCW_comm (s : Shape) (threshold : Nat) :
    (s.shatterTopCrystals threshold).rotateCCW =
      s.rotateCCW.shatterTopCrystals threshold := by
  simp [Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW,
        Shape.shatterTopCrystals.rotateCW_comm]

/-- `shatterOnCut` と 180° 回転は可換（180° は E↔W を入れ替えるが
    「結晶結合クラスタが E と W の両方を含む」性質は対称的に保存される）。 -/
theorem Shape.shatterOnCut.rotate180_comm (s : Shape) :
    (s.shatterOnCut).rotate180 = s.rotate180.shatterOnCut := by
  unfold Shape.shatterOnCut
  apply Shape.shatterMask.rotate180_comm
  intro p
  apply decide_congr
  show IsShatteredOnCut s p ↔ IsShatteredOnCut s.rotateCW.rotateCW p.rotateCW.rotateCW
  have hEW : ∀ d : Fin 4, Direction.isEast d = true → Direction.isWest (d + 1 + 1) = true :=
    by decide
  have hWE : ∀ d : Fin 4, Direction.isWest d = true → Direction.isEast (d + 1 + 1) = true :=
    by decide
  unfold IsShatteredOnCut
  constructor
  · rintro ⟨t, hCry, hRel, ⟨pE, hRelE, hE⟩, ⟨pW, hRelW, hW⟩⟩
    refine ⟨t.rotateCW.rotateCW, ?_, ?_, ?_, ?_⟩
    · rw [QuarterPos.getQuarter_rotateCW, QuarterPos.getQuarter_rotateCW]; exact hCry
    · exact (CrystalBondClusterRel.rotateCW_two s t p).mpr hRel
    · exact ⟨pW.rotateCW.rotateCW, (CrystalBondClusterRel.rotateCW_two s t pW).mpr hRelW, hWE pW.2 hW⟩
    · exact ⟨pE.rotateCW.rotateCW, (CrystalBondClusterRel.rotateCW_two s t pE).mpr hRelE, hEW pE.2 hE⟩
  · rintro ⟨t', hCry', hRel', ⟨pE', hRelE', hE'⟩, ⟨pW', hRelW', hW'⟩⟩
    refine ⟨t'.rotateCCW.rotateCCW, ?_, ?_, ?_, ?_⟩
    · rw [show t' = t'.rotateCCW.rotateCCW.rotateCW.rotateCW by
            simp [QuarterPos.rotateCW_rotateCCW]] at hCry'
      rw [QuarterPos.getQuarter_rotateCW, QuarterPos.getQuarter_rotateCW] at hCry'
      exact hCry'
    · have hr : CrystalBondClusterRel s.rotateCW.rotateCW
                  t'.rotateCCW.rotateCCW.rotateCW.rotateCW
                  p.rotateCW.rotateCW := by
        simp [QuarterPos.rotateCW_rotateCCW]; exact hRel'
      exact (CrystalBondClusterRel.rotateCW_two s t'.rotateCCW.rotateCCW p).mp hr
    · refine ⟨pW'.rotateCCW.rotateCCW, ?_, ?_⟩
      · have hr : CrystalBondClusterRel s.rotateCW.rotateCW
                  t'.rotateCCW.rotateCCW.rotateCW.rotateCW
                  pW'.rotateCCW.rotateCCW.rotateCW.rotateCW := by
          simp [QuarterPos.rotateCW_rotateCCW]; exact hRelW'
        exact (CrystalBondClusterRel.rotateCW_two s t'.rotateCCW.rotateCCW pW'.rotateCCW.rotateCCW).mp hr
      · show Direction.isEast (pW'.2 - 1 - 1) = true
        rw [Direction.sub_two_eq_add_two]
        exact hWE pW'.2 hW'
    · refine ⟨pE'.rotateCCW.rotateCCW, ?_, ?_⟩
      · have hr : CrystalBondClusterRel s.rotateCW.rotateCW
                  t'.rotateCCW.rotateCCW.rotateCW.rotateCW
                  pE'.rotateCCW.rotateCCW.rotateCW.rotateCW := by
          simp [QuarterPos.rotateCW_rotateCCW]; exact hRelE'
        exact (CrystalBondClusterRel.rotateCW_two s t'.rotateCCW.rotateCCW pE'.rotateCCW.rotateCCW).mp hr
      · show Direction.isWest (pE'.2 - 1 - 1) = true
        rw [Direction.sub_two_eq_add_two]
        exact hEW pE'.2 hE'

end S2IL