-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Settled
import S2IL.Operations.Gravity.Internal.Floating
import S2IL.Operations.Gravity.Internal.Shift

/-!
# S2IL.Operations.Gravity.Defs

Wave Gravity の Layer A/B 定義層。

## 公開 API

- `FloatingPos` — 現在のシェイプで非接地な非空象限
- `floatingMask` / `floatingPositions` — Wave tick で落下する位置の mask / 列挙
- `floatingHeight` — floating 位置の最大 layer index（空なら 0）
- `Shape.waveStep` — floating 位置を同時に 1 レイヤ下げる atomic tick
- `Shape.waveGravityCore` — fixed fuel の Wave tick 反復
- `Shape.waveGravityCoreFast` — floating 位置が空になった時点で停止する実行用 core
- `Shape.gravity` — Wave Gravity 本体

## Internal（外部 import 禁止）

- `S2IL.Operations.Gravity.Internal.Shift`
- `S2IL.Operations.Gravity.Internal.Floating`
- `S2IL.Operations.Gravity.Internal.FinsetClosure`
- `S2IL.Operations.Gravity.Internal.GroundingBool`
- `S2IL.Operations.Gravity.Internal.GroundingClosure`
-/

namespace S2IL

/-- 現在のシェイプで非接地な非空象限。Wave tick の落下対象。 -/
def FloatingPos (s : Shape) (p : QuarterPos) : Prop :=
  p ∈ QuarterPos.allValid s ∧
  ¬ (QuarterPos.getQuarter s p).isEmpty ∧
  ¬ IsGrounded s p

noncomputable instance instDecidableFloatingPos (s : Shape) : DecidablePred (FloatingPos s) :=
  Classical.decPred _

/-- `FloatingPos` と同じ意図を持つ、Wave tick 用の実行可能 Bool mask。 -/
def floatingMask (s : Shape) (p : QuarterPos) : Bool :=
  QuarterPos.isValid s p && Gravity.Internal.groundingNonempty s p &&
    !Gravity.Internal.isGroundedBool s p

private def floatingMaskWithGrounded (s : Shape) (grounded : List QuarterPos)
    (p : QuarterPos) : Bool :=
  QuarterPos.isValid s p && Gravity.Internal.groundingNonempty s p &&
    !grounded.contains p

/-- Wave tick で 1 レイヤ下げる全 floating 位置。 -/
def floatingPositions (s : Shape) : List QuarterPos :=
  let grounded := Gravity.Internal.groundedPositions s
  (QuarterPos.allValid s).filter (floatingMaskWithGrounded s grounded)

/-- Floating 位置の最大 layer index。floating 位置がなければ `0`。 -/
def floatingHeight (s : Shape) : Nat :=
  ((floatingPositions s).map fun p => p.1).foldl Nat.max 0

/-- `floatingMask` と Prop 層の `FloatingPos` の bridge。 -/
theorem floatingMask_iff (s : Shape) (p : QuarterPos) :
    floatingMask s p = true ↔ FloatingPos s p := by
  simp [floatingMask, FloatingPos, QuarterPos.isValid, QuarterPos.mem_allValid,
    Gravity.Internal.groundingNonempty]
  constructor
  · rintro ⟨⟨hValid, hNonempty⟩, hBool⟩
    refine ⟨hValid, hNonempty, ?_⟩
    intro hGrounded
    have hGroundedBool : Gravity.Internal.isGroundedBool s p = true :=
      (Gravity.Internal.isGroundedBool_iff s p).mpr hGrounded
    rw [hGroundedBool] at hBool
    contradiction
  · rintro ⟨hValid, hNonempty, hNotGrounded⟩
    refine ⟨⟨hValid, hNonempty⟩, ?_⟩
    cases hBool : Gravity.Internal.isGroundedBool s p with
    | false => rfl
    | true =>
        exact False.elim (hNotGrounded ((Gravity.Internal.isGroundedBool_iff s p).mp hBool))

private theorem floatingMaskWithGrounded_iff (s : Shape) (grounded : List QuarterPos)
    (hGrounded : ∀ p : QuarterPos, grounded.contains p = true ↔ IsGrounded s p)
    (p : QuarterPos) :
    floatingMaskWithGrounded s grounded p = true ↔ FloatingPos s p := by
  simp [floatingMaskWithGrounded, FloatingPos, QuarterPos.isValid, QuarterPos.mem_allValid,
    Gravity.Internal.groundingNonempty]
  constructor
  · rintro ⟨⟨hValid, hNonempty⟩, hBool⟩
    refine ⟨hValid, hNonempty, ?_⟩
    intro hGroundedProp
    have hGroundedBool : grounded.contains p = true := (hGrounded p).mpr hGroundedProp
    have hpGrounded : p ∈ grounded := by simpa using hGroundedBool
    exact hBool hpGrounded
  · rintro ⟨hValid, hNonempty, hNotGrounded⟩
    refine ⟨⟨hValid, hNonempty⟩, ?_⟩
    cases hBool : grounded.contains p with
    | false => simpa using hBool
    | true => exact False.elim (hNotGrounded ((hGrounded p).mp hBool))

/-- `floatingPositions` の membership 仕様。リスト順序には依存しない。 -/
theorem mem_floatingPositions_iff (s : Shape) (p : QuarterPos) :
    p ∈ floatingPositions s ↔ FloatingPos s p := by
  have hGrounded : ∀ p : QuarterPos,
      (Gravity.Internal.groundedPositions s).contains p = true ↔ IsGrounded s p := by
    intro p
    simpa [Gravity.Internal.isGroundedBool] using Gravity.Internal.isGroundedBool_iff s p
  constructor
  · intro h
    exact (floatingMaskWithGrounded_iff s (Gravity.Internal.groundedPositions s)
      hGrounded p).mp ((List.mem_filter.mp h).2)
  · intro h
    exact List.mem_filter.mpr ⟨h.1, (floatingMaskWithGrounded_iff s
      (Gravity.Internal.groundedPositions s) hGrounded p).mpr h⟩

namespace FloatingPos

/-- Floating 位置は layer 0 には存在しない。 -/
theorem layer_pos {s : Shape} {p : QuarterPos} (h : FloatingPos s p) : 0 < p.1 := by
  by_contra hLayer
  have hZero : p.1 = 0 := Nat.eq_zero_of_not_pos hLayer
  have hGrounded : IsGrounded s p := by
    exact ⟨p, hZero, h.2.1, Relation.ReflTransGen.refl⟩
  exact h.2.2 hGrounded

/-- Floating 位置の 1 レイヤ下は同じシェイプの有効範囲内にある。 -/
theorem down_valid {s : Shape} {p : QuarterPos} (h : FloatingPos s p) :
    p.down ∈ QuarterPos.allValid s := by
  rw [QuarterPos.mem_allValid]
  have hValid : p.1 < s.length := by
    exact (QuarterPos.mem_allValid s p).mp h.1
  exact Nat.lt_of_le_of_lt (Nat.sub_le p.1 1) hValid

/-- Floating 位置の直下は空、または同じ tick で落下する floating 位置である。 -/
theorem down_empty_or_floating {s : Shape} {p : QuarterPos} (h : FloatingPos s p) :
    (QuarterPos.getQuarter s p.down).isEmpty ∨ FloatingPos s p.down := by
  by_cases hDownEmpty : (QuarterPos.getQuarter s p.down).isEmpty
  · exact Or.inl hDownEmpty
  · refine Or.inr ⟨down_valid h, hDownEmpty, ?_⟩
    intro hDownGrounded
    obtain ⟨p0, hp0Layer, hp0Nonempty, hpath⟩ := hDownGrounded
    have hLayerPos : 0 < p.1 := layer_pos h
    have hDownUp : p.down.1 + 1 = p.1 := by
      simp [QuarterPos.down]
      omega
    have hedge : IsGroundingEdge s p.down p := by
      apply Or.inl
      constructor
      · apply Or.inl
        refine ⟨?_, ?_, hDownEmpty, h.2.1⟩
        · simp [QuarterPos.down]
        · exact Or.inl hDownUp
      · simp [QuarterPos.down]
    exact h.2.2 ⟨p0, hp0Layer, hp0Nonempty, Relation.ReflTransGen.tail hpath hedge⟩

end FloatingPos

namespace QuarterPos

/-- `down` は floating 位置上では単射であり、shift 同士は同じセルへ衝突しない。 -/
theorem down_injective_on_floating {s : Shape} {p q : QuarterPos}
    (hp : FloatingPos s p) (hq : FloatingPos s q) (hdown : p.down = q.down) : p = q := by
  have hpPos : 0 < p.1 := FloatingPos.layer_pos hp
  have hqPos : 0 < q.1 := FloatingPos.layer_pos hq
  have hLayerSub : p.1 - 1 = q.1 - 1 := by
    have hfst := congrArg Prod.fst hdown
    simpa [QuarterPos.down] using hfst
  have hDir : p.2 = q.2 := by
    have hsnd := congrArg Prod.snd hdown
    simpa [QuarterPos.down] using hsnd
  have hLayer : p.1 = q.1 := by omega
  exact Prod.ext hLayer hDir

end QuarterPos

namespace Shape

/-- Wave Gravity の 1 tick。現在 floating な全位置を同時に 1 レイヤ下げる。 -/
def waveStep (s : Shape) : Shape :=
  _root_.S2IL.Gravity.Internal.atomicShiftDown s (floatingPositions s)

/-- `waveStep` はレイヤ数を変えない。 -/
@[simp] theorem waveStep.layerCount (s : Shape) :
    (waveStep s).layerCount = s.layerCount := by
  simp [waveStep, Shape.layerCount]

/-- `waveStep` を fixed fuel 回だけ反復する Wave Gravity core。 -/
def waveGravityCore (fuel : Nat) (s : Shape) : Shape :=
  Nat.iterate waveStep fuel s

/-- 早期停止つき Wave Gravity core。floating 位置が空になった時点で残り fuel を消費しない。 -/
def waveGravityCoreFast : Nat → Shape → Shape
  | 0, s => s
  | fuel + 1, s =>
      let floating := floatingPositions s
      if floating = [] then
        s
      else
        waveGravityCoreFast fuel (_root_.S2IL.Gravity.Internal.atomicShiftDown s floating)

/-- `waveGravityCoreFast` はレイヤ数を変えない。 -/
@[simp] theorem waveGravityCoreFast.layerCount (fuel : Nat) (s : Shape) :
    (waveGravityCoreFast fuel s).layerCount = s.layerCount := by
  induction fuel generalizing s with
  | zero => simp [waveGravityCoreFast, Shape.layerCount]
  | succ fuel ih =>
      unfold waveGravityCoreFast
      by_cases h : floatingPositions s = []
      · simp [h]
      · simp only [h, ↓reduceIte]
        rw [ih]
        simp [Shape.layerCount]

/-- Wave Gravity 本体。fixed fuel と同値な早期停止 core 後に末尾空レイヤを正規化する。 -/
def gravity (s : Shape) : Shape :=
  (waveGravityCoreFast s.length s).normalize

/-- `gravity` はレイヤ数を増やさない。 -/
theorem gravity.layerCount_le (s : Shape) :
    (gravity s).layerCount ≤ s.layerCount := by
  rw [gravity]
  exact Nat.le_trans (Shape.normalize.layerCount_le _) (by
    rw [waveGravityCoreFast.layerCount])

end Shape

end S2IL
