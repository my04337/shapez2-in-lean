-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape

/-!
# Internal: Wave Gravity atomic shift

このファイルは `S2IL.Operations.Gravity` namespace の補助補題を集める。
**外部モジュール（S2IL/Operations/Gravity.lean, S2IL/Operations/Gravity/*.lean 以外）からは import 禁止**。
-/

namespace S2IL

namespace Gravity.Internal

/-- `positions` の各元位置を、`source` から読んだ値のまま `target` 上の 1 レイヤ下へ書く。 -/
def writeShiftedDown (source : Shape) (positions : List QuarterPos) (target : Shape) : Shape :=
  positions.foldl
    (fun acc p => QuarterPos.setQuarter acc p.down (QuarterPos.getQuarter source p))
    target

/-- `writeShiftedDown` は target のレイヤ数を変えない。 -/
@[simp] theorem length_writeShiftedDown
    (source : Shape) (positions : List QuarterPos) (target : Shape) :
    (writeShiftedDown source positions target).length = target.length := by
  induction positions generalizing target with
  | nil => simp [writeShiftedDown]
  | cons p ps ih =>
      unfold writeShiftedDown
      change (writeShiftedDown source ps
        (QuarterPos.setQuarter target p.down (QuarterPos.getQuarter source p))).length =
          target.length
      rw [ih, QuarterPos.length_setQuarter]

/-- `r` へ流入する shifted source がなければ、`writeShiftedDown` は `r` を変えない。 -/
theorem getQuarter_writeShiftedDown_of_no_preimage
    (source target : Shape) (positions : List QuarterPos) (r : QuarterPos)
    (hNo : ∀ p : QuarterPos, p ∈ positions → p.down ≠ r) :
    QuarterPos.getQuarter (writeShiftedDown source positions target) r =
      QuarterPos.getQuarter target r := by
  induction positions generalizing target with
  | nil => simp [writeShiftedDown]
  | cons p ps ih =>
      unfold writeShiftedDown
      change QuarterPos.getQuarter (writeShiftedDown source ps
        (QuarterPos.setQuarter target p.down (QuarterPos.getQuarter source p))) r = _
      rw [ih]
      · rw [QuarterPos.getQuarter_setQuarter]
        have hne : r ≠ p.down := fun h => hNo p (by simp) h.symm
        simp [hne]
      · intro q hq
        exact hNo q (by simp [hq])

/--
`positions` 上で `down` の preimage が一意なら、対応する source 象限が書き込まれる。
一般の `positions` では last-write 順序に依存するため、一意性を明示的に仮定する。
-/
theorem getQuarter_writeShiftedDown_of_unique_preimage
    (source target : Shape) (positions : List QuarterPos) (p : QuarterPos)
    (hmem : p ∈ positions)
    (hvalid : p.down.1 < target.length)
    (hUnique : ∀ q : QuarterPos, q ∈ positions → q.down = p.down → q = p) :
    QuarterPos.getQuarter (writeShiftedDown source positions target) p.down =
      QuarterPos.getQuarter source p := by
  induction positions generalizing target with
  | nil => cases hmem
  | cons x xs ih =>
      unfold writeShiftedDown
      change QuarterPos.getQuarter (writeShiftedDown source xs
        (QuarterPos.setQuarter target x.down (QuarterPos.getQuarter source x))) p.down = _
      by_cases hx : x = p
      · subst x
        by_cases hpTail : p ∈ xs
        · apply ih
          · exact hpTail
          · simpa [QuarterPos.length_setQuarter] using hvalid
          · intro q hq hdown
            exact hUnique q (by simp [hq]) hdown
        · rw [getQuarter_writeShiftedDown_of_no_preimage]
          · rw [QuarterPos.getQuarter_setQuarter]
            have hvalidLayer : p.1 - 1 < target.length := by
              simpa [QuarterPos.down] using hvalid
            simp [QuarterPos.down, hvalidLayer]
          · intro q hq hdown
            have hqEq : q = p := hUnique q (by simp [hq]) hdown
            subst q
            exact hpTail hq
      · have hpTail : p ∈ xs := by
          have hmemOr : p = x ∨ p ∈ xs := by simpa using hmem
          rcases hmemOr with hpHead | hpTail
          · exact False.elim (hx hpHead.symm)
          · exact hpTail
        apply ih
        · exact hpTail
        · simpa [QuarterPos.length_setQuarter] using hvalid
        · intro q hq hdown
          exact hUnique q (by simp [hq]) hdown

/-- `positions` を同時に空け、元の値を 1 レイヤ下へ書く atomic shift。 -/
def atomicShiftDown (source : Shape) (positions : List QuarterPos) : Shape :=
  writeShiftedDown source positions (Shape.clearPositions source positions)

/-- `atomicShiftDown` は source のレイヤ数を変えない。 -/
@[simp] theorem length_atomicShiftDown (source : Shape) (positions : List QuarterPos) :
    (atomicShiftDown source positions).length = source.length := by
  simp [atomicShiftDown]

/-- 一意な shifted preimage がある位置には、source のその象限が書き込まれる。 -/
theorem getQuarter_atomicShiftDown_of_unique_preimage
    (source : Shape) (positions : List QuarterPos) (p : QuarterPos)
    (hmem : p ∈ positions)
    (hvalid : p.down.1 < source.length)
    (hUnique : ∀ q : QuarterPos, q ∈ positions → q.down = p.down → q = p) :
    QuarterPos.getQuarter (atomicShiftDown source positions) p.down =
      QuarterPos.getQuarter source p := by
  unfold atomicShiftDown
  apply getQuarter_writeShiftedDown_of_unique_preimage
  · exact hmem
  · simpa using hvalid
  · exact hUnique

/-- 流入がなく、clear 対象でもない位置は `atomicShiftDown` で不変。 -/
theorem getQuarter_atomicShiftDown_of_static
    (source : Shape) (positions : List QuarterPos) (r : QuarterPos)
    (hNo : ∀ p : QuarterPos, p ∈ positions → p.down ≠ r)
    (hNotClear : r ∉ positions) :
    QuarterPos.getQuarter (atomicShiftDown source positions) r =
      QuarterPos.getQuarter source r := by
  unfold atomicShiftDown
  rw [getQuarter_writeShiftedDown_of_no_preimage]
  · exact Shape.getQuarter_clearPositions_of_not_mem hNotClear
  · exact hNo

/-- 流入がなく、clear 対象である位置は `atomicShiftDown` 後に空になる。 -/
theorem getQuarter_atomicShiftDown_of_cleared
    (source : Shape) (positions : List QuarterPos) (r : QuarterPos)
    (hNo : ∀ p : QuarterPos, p ∈ positions → p.down ≠ r)
    (hClear : r ∈ positions) :
    QuarterPos.getQuarter (atomicShiftDown source positions) r = Quarter.empty := by
  unfold atomicShiftDown
  rw [getQuarter_writeShiftedDown_of_no_preimage]
  · exact Shape.getQuarter_clearPositions_of_mem hClear
  · exact hNo

end Gravity.Internal

end S2IL
