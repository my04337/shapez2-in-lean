import S2IL.Operations.Gravity.Internal.FinsetClosure
import S2IL.Operations.Gravity.Internal.GroundingBool

/-!
# Internal: grounding closure enumeration

このファイルは `S2IL.Operations.Gravity` namespace の補助補題を集める。
**外部モジュール（S2IL/Operations/Gravity.lean, S2IL/Operations/Gravity/*.lean 以外）からは import 禁止**。
-/

namespace S2IL

namespace Gravity.Internal

open scoped Finset

/-- layer 0 の非空位置を接地閉包の seed として列挙する。 -/
def groundingSeeds (s : Shape) : List QuarterPos :=
  (QuarterPos.allValid s).filter (fun p => (p.1 == 0) && groundingNonempty s p)

/-- `groundingSeeds` の membership 仕様。 -/
theorem groundingSeeds.mem_iff (s : Shape) (p : QuarterPos) :
    p ∈ groundingSeeds s ↔
      p ∈ QuarterPos.allValid s ∧ p.1 = 0 ∧
        ¬ (QuarterPos.getQuarter s p).isEmpty := by
  simp [groundingSeeds, groundingNonempty]

/-- `groundingSeeds` に含まれる位置は Prop 層で接地している。 -/
theorem groundingSeeds.sound {s : Shape} {p : QuarterPos}
    (h : p ∈ groundingSeeds s) : IsGrounded s p := by
  obtain ⟨_hValid, hLayer, hNonempty⟩ := (groundingSeeds.mem_iff s p).mp h
  exact ⟨p, hLayer, hNonempty, Relation.ReflTransGen.refl⟩

/-- `groundingSeeds` は有効位置のみを列挙する。 -/
theorem groundingSeeds.subset_allValid {s : Shape} {p : QuarterPos}
    (h : p ∈ groundingSeeds s) : p ∈ QuarterPos.allValid s :=
  (groundingSeeds.mem_iff s p).mp h |>.1

/-- 既知の接地位置から 1 step 分だけ接地エッジで閉包を広げる。 -/
def groundingExpand (s : Shape) (known : List QuarterPos) : List QuarterPos :=
  (QuarterPos.allValid s).filter (fun p =>
    known.contains p || known.any (fun q => isGroundingEdgeBool s q p))

/-- `groundingExpand` の membership 仕様。リスト順序には依存しない。 -/
theorem groundingExpand.mem_iff (s : Shape) (known : List QuarterPos) (p : QuarterPos) :
    p ∈ groundingExpand s known ↔
      p ∈ QuarterPos.allValid s ∧
        (p ∈ known ∨ ∃ q : QuarterPos, q ∈ known ∧ IsGroundingEdge s q p) := by
  simp [groundingExpand, isGroundingEdgeBool_iff]

/-- `groundingExpand` の結果は常に有効位置に限られる。 -/
theorem groundingExpand.subset_allValid {s : Shape} {known : List QuarterPos}
    {p : QuarterPos} (h : p ∈ groundingExpand s known) :
    p ∈ QuarterPos.allValid s :=
  (groundingExpand.mem_iff s known p).mp h |>.1

/-- 有効な既知位置は `groundingExpand` 後も含まれる。 -/
theorem groundingExpand.mem_of_known {s : Shape} {known : List QuarterPos}
    {p : QuarterPos} (hValid : p ∈ QuarterPos.allValid s) (hKnown : p ∈ known) :
    p ∈ groundingExpand s known :=
  (groundingExpand.mem_iff s known p).mpr ⟨hValid, Or.inl hKnown⟩

/-- 既知位置から接地エッジで 1 step 到達できる有効位置は `groundingExpand` に含まれる。 -/
theorem groundingExpand.mem_of_edge {s : Shape} {known : List QuarterPos}
    {p q : QuarterPos} (hValid : p ∈ QuarterPos.allValid s) (hKnown : q ∈ known)
    (hEdge : IsGroundingEdge s q p) : p ∈ groundingExpand s known :=
  (groundingExpand.mem_iff s known p).mpr ⟨hValid, Or.inr ⟨q, hKnown, hEdge⟩⟩

/-- `groundingExpand` の Finset 表現。固定点証明専用で、公開仕様には使わない。 -/
noncomputable def groundingExpandFinset (s : Shape)
    (known : Finset QuarterPos) : Finset QuarterPos :=
  (groundingExpand s known.toList).toFinset

/-- `groundingExpand` は membership 上、Finset 表現へ順序非依存に写せる。 -/
theorem groundingExpand.toFinset_eq (s : Shape) (known : List QuarterPos) :
    (groundingExpand s known).toFinset = groundingExpandFinset s known.toFinset := by
  ext p
  simp [groundingExpandFinset, groundingExpand.mem_iff]

/-- 有効範囲内の既知 Finset は `groundingExpandFinset` 後も保持される。 -/
theorem groundingExpandFinset.infl (s : Shape) (known : Finset QuarterPos)
    (hKnown : known ⊆ (QuarterPos.allValid s).toFinset) :
    known ⊆ groundingExpandFinset s known := by
  intro p hp
  have hValid : p ∈ QuarterPos.allValid s := by
    simpa using hKnown hp
  simp [groundingExpandFinset, groundingExpand.mem_iff, hValid, hp]

/-- `groundingExpandFinset` の結果は常に有効範囲内にある。 -/
theorem groundingExpandFinset.subset_allValid (s : Shape) (known : Finset QuarterPos) :
    groundingExpandFinset s known ⊆ (QuarterPos.allValid s).toFinset := by
  intro p hp
  simp [groundingExpandFinset, groundingExpand.mem_iff] at hp ⊢
  exact hp.1

/-- List 反復の membership carrier は Finset 反復と一致する。 -/
theorem groundingExpandFinset.iterate_toFinset (s : Shape) (fuel : Nat) :
    (Nat.iterate (groundingExpand s) fuel (groundingSeeds s)).toFinset =
      Nat.iterate (groundingExpandFinset s) fuel (groundingSeeds s).toFinset := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        groundingExpand.toFinset_eq, ih]

/-- `groundingSeeds` の Finset は有効 carrier の部分集合である。 -/
theorem groundingSeeds.toFinset_subset_allValid (s : Shape) :
    (groundingSeeds s).toFinset ⊆ (QuarterPos.allValid s).toFinset := by
  intro p hp
  simp at hp ⊢
  exact groundingSeeds.subset_allValid hp

/-- `allValid.length` 回の Finset 接地閉包反復は固定点になっている。 -/
theorem groundingExpandFinset.fixed_at_allValid_length (s : Shape) :
    groundingExpandFinset s
        ((groundingExpandFinset s)^[(QuarterPos.allValid s).length] (groundingSeeds s).toFinset) =
      (groundingExpandFinset s)^[(QuarterPos.allValid s).length] (groundingSeeds s).toFinset := by
  classical
  let bound : Finset QuarterPos := (QuarterPos.allValid s).toFinset
  let start : Finset QuarterPos := (groundingSeeds s).toFinset
  let step : Finset QuarterPos → Finset QuarterPos := groundingExpandFinset s
  let fuel : Nat := (QuarterPos.allValid s).length
  have hFixedCard : step (step^[#bound] start) = step^[#bound] start := by
    exact finset_iterate_fixed_of_bounded bound start step
      (fun known hKnown => groundingExpandFinset.infl s known hKnown)
      (by simpa [bound, start] using groundingSeeds.toFinset_subset_allValid s)
      (fun known _hKnown => by
        simpa [bound, step] using groundingExpandFinset.subset_allValid s known)
  have hCardLeFuel : #bound ≤ fuel := by
    simpa [bound, fuel] using List.toFinset_card_le (QuarterPos.allValid s)
  have hFixedFuel : step (step^[fuel] start) = step^[fuel] start :=
    iterate_fixed_at_of_fixed_at_le start step hFixedCard hCardLeFuel
  simpa [start, step, fuel] using hFixedFuel

/-- `groundingExpand` は既知集合に対して単調。 -/
theorem groundingExpand.monotone {s : Shape} {known known' : List QuarterPos}
    (hSub : ∀ p : QuarterPos, p ∈ known → p ∈ known') {p : QuarterPos}
    (h : p ∈ groundingExpand s known) : p ∈ groundingExpand s known' := by
  obtain ⟨hValid, hStep⟩ := (groundingExpand.mem_iff s known p).mp h
  apply (groundingExpand.mem_iff s known' p).mpr
  refine ⟨hValid, ?_⟩
  rcases hStep with hKnown | ⟨q, hKnown, hEdge⟩
  · exact Or.inl (hSub p hKnown)
  · exact Or.inr ⟨q, hSub q hKnown, hEdge⟩

/-- 接地エッジに対して閉じた既知集合は、`groundingExpand` 後も増えない。 -/
theorem groundingExpand.subset_of_closed {s : Shape} {known : List QuarterPos}
    (hClosed : ∀ p : QuarterPos, p ∈ QuarterPos.allValid s →
      (∃ q : QuarterPos, q ∈ known ∧ IsGroundingEdge s q p) → p ∈ known)
    {p : QuarterPos} (h : p ∈ groundingExpand s known) : p ∈ known := by
  obtain ⟨hValid, hStep⟩ := (groundingExpand.mem_iff s known p).mp h
  rcases hStep with hKnown | hEdge
  · exact hKnown
  · exact hClosed p hValid hEdge

/-- sound な既知集合から `groundingExpand` で得た位置は Prop 層で接地している。 -/
theorem groundingExpand.sound {s : Shape} {known : List QuarterPos}
    (hKnownSound : ∀ q : QuarterPos, q ∈ known → IsGrounded s q)
    {p : QuarterPos} (h : p ∈ groundingExpand s known) : IsGrounded s p := by
  obtain ⟨_hValid, hStep⟩ := (groundingExpand.mem_iff s known p).mp h
  rcases hStep with hKnown | ⟨q, hKnown, hEdge⟩
  · exact hKnownSound p hKnown
  · obtain ⟨p0, hLayer, hNonempty, hPath⟩ := hKnownSound q hKnown
    exact ⟨p0, hLayer, hNonempty, Relation.ReflTransGen.tail hPath hEdge⟩

/-- 任意 fuel の接地閉包反復は Prop 層に対して sound。 -/
theorem groundedPositions.sound_iter (s : Shape) (fuel : Nat) {p : QuarterPos}
    (h : p ∈ Nat.iterate (groundingExpand s) fuel (groundingSeeds s)) :
    IsGrounded s p := by
  induction fuel generalizing p with
  | zero =>
      exact groundingSeeds.sound h
  | succ n ih =>
      rw [Function.iterate_succ_apply'] at h
      exact groundingExpand.sound (fun q hq => ih hq) h

/-- 有限反復で得られる実行可能な接地位置列挙。仕様は membership bridge で与える。 -/
def groundedPositions (s : Shape) : List QuarterPos :=
  Nat.iterate (groundingExpand s) (QuarterPos.allValid s).length (groundingSeeds s)

/-- `groundedPositions` の Finset carrier は Finset 版閉包反復と一致する。 -/
theorem groundedPositions.toFinset_eq (s : Shape) :
    (groundedPositions s).toFinset =
      (groundingExpandFinset s)^[(QuarterPos.allValid s).length] (groundingSeeds s).toFinset := by
  unfold groundedPositions
  simpa using groundingExpandFinset.iterate_toFinset s (QuarterPos.allValid s).length

/-- `groundedPositions` は Finset として `groundingExpand` の固定点である。 -/
theorem groundedPositions.expand_toFinset_eq (s : Shape) :
    (groundingExpand s (groundedPositions s)).toFinset = (groundedPositions s).toFinset := by
  classical
  have hGroundedToFinset := groundedPositions.toFinset_eq s
  calc
    (groundingExpand s (groundedPositions s)).toFinset
        = groundingExpandFinset s (groundedPositions s).toFinset :=
          groundingExpand.toFinset_eq s (groundedPositions s)
    _ = groundingExpandFinset s
        ((groundingExpandFinset s)^[(QuarterPos.allValid s).length] (groundingSeeds s).toFinset) := by
          rw [hGroundedToFinset]
    _ = (groundingExpandFinset s)^[(QuarterPos.allValid s).length] (groundingSeeds s).toFinset :=
          groundingExpandFinset.fixed_at_allValid_length s
    _ = (groundedPositions s).toFinset := hGroundedToFinset.symm

/-- seed は有限反復後の `groundedPositions` にも含まれる。 -/
theorem groundedPositions.mem_of_seed {s : Shape} {p : QuarterPos}
    (h : p ∈ groundingSeeds s) : p ∈ groundedPositions s := by
  unfold groundedPositions
  have hValid : p ∈ QuarterPos.allValid s := groundingSeeds.subset_allValid h
  induction (QuarterPos.allValid s).length with
  | zero => exact h
  | succ fuel ih =>
      rw [Function.iterate_succ_apply']
      exact groundingExpand.mem_of_known hValid ih

/-- `groundedPositions` は `groundingExpand` に対して閉じている。 -/
theorem groundedPositions.expand_subset {s : Shape} {p : QuarterPos}
    (h : p ∈ groundingExpand s (groundedPositions s)) : p ∈ groundedPositions s := by
  have hpFin : p ∈ (groundedPositions s).toFinset := by
    have hpExpand : p ∈ (groundingExpand s (groundedPositions s)).toFinset := by
      simpa using h
    rwa [groundedPositions.expand_toFinset_eq s] at hpExpand
  simpa using hpFin

/-- `groundedPositions` に含まれる位置は Prop 層で接地している。 -/
theorem groundedPositions.sound {s : Shape} {p : QuarterPos}
    (h : p ∈ groundedPositions s) : IsGrounded s p := by
  unfold groundedPositions at h
  exact groundedPositions.sound_iter s (QuarterPos.allValid s).length h

/-- Prop 層で接地している位置は `groundedPositions` に列挙される。 -/
theorem groundedPositions.complete {s : Shape} {p : QuarterPos}
    (h : IsGrounded s p) : p ∈ groundedPositions s := by
  obtain ⟨seed, hLayer, hNonempty, hPath⟩ := h
  have hSeed : seed ∈ groundingSeeds s := by
    exact (groundingSeeds.mem_iff s seed).mpr
      ⟨getQuarter_nonempty_mem_allValid hNonempty, hLayer, hNonempty⟩
  induction hPath with
  | refl =>
      exact groundedPositions.mem_of_seed hSeed
  | tail _ hEdge ih =>
      exact groundedPositions.expand_subset
        (groundingExpand.mem_of_edge (IsGroundingEdge.right_mem_allValid hEdge) ih hEdge)

/-- `groundedPositions` による実行可能な接地判定。 -/
def isGroundedBool (s : Shape) (p : QuarterPos) : Bool :=
  (groundedPositions s).contains p

/-- `isGroundedBool` と Prop 層の `IsGrounded` の bridge。 -/
theorem isGroundedBool_iff (s : Shape) (p : QuarterPos) :
    isGroundedBool s p = true ↔ IsGrounded s p := by
  constructor
  · intro h
    exact groundedPositions.sound (by simpa [isGroundedBool] using h)
  · intro h
    exact by simpa [isGroundedBool] using groundedPositions.complete h

end Gravity.Internal

end S2IL