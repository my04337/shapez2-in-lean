-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.Types.Shape

/-!
# S2IL.Shape.Types.QuarterPos

絶対位置 `QuarterPos := Nat × Fin 4` と点ごとの shape 操作。
-/

namespace S2IL

/-- 象限の絶対位置（レイヤ番号 × 方角）。 -/
abbrev QuarterPos := Nat × Fin 4

namespace QuarterPos

def mk (layer : Nat) (dir : Direction) : QuarterPos := (layer, dir)
def layer (pos : QuarterPos) : Nat := pos.1
def dir   (pos : QuarterPos) : Direction := pos.2

/-- 指定位置の象限を取得（範囲外は空）。 -/
def getQuarter (s : Shape) (pos : QuarterPos) : Quarter :=
  if h : pos.1 < s.length then s[pos.1] pos.2 else Quarter.empty

/-- 指定位置の象限を設定。範囲外は変更しない。 -/
def setQuarter (s : Shape) (pos : QuarterPos) (q : Quarter) : Shape :=
  if h : pos.1 < s.length then
    s.set pos.1 ((s[pos.1]'h).setDir pos.2 q)
  else s

/-- `setQuarter` はシェイプのレイヤ数を変えない。 -/
@[simp] theorem length_setQuarter (s : Shape) (pos : QuarterPos) (q : Quarter) :
    (setQuarter s pos q).length = s.length := by
  unfold setQuarter
  by_cases h : pos.1 < s.length <;> simp [h]

/-- `setQuarter` 後の点取得仕様。範囲外への書き込みは no-op。 -/
theorem getQuarter_setQuarter (s : Shape) (pos p : QuarterPos) (q : Quarter) :
    getQuarter (setQuarter s pos q) p =
      if p = pos ∧ pos.1 < s.length then q else getQuarter s p := by
  obtain ⟨pl, pd⟩ := p
  obtain ⟨il, id⟩ := pos
  by_cases hpos : il < s.length
  · by_cases hp : pl < s.length
    · unfold setQuarter getQuarter
      rw [dif_pos hpos]
      rw [dif_pos (by simpa [List.length_set] using hp)]
      rw [dif_pos hp]
      rw [List.getElem_set]
      by_cases hLayer : il = pl
      · subst hLayer
        simp [Layer.setDir, hpos]
      · have hLayerReverse : ¬ pl = il := fun h => hLayer h.symm
        simp [hLayer, hLayerReverse]
    · unfold setQuarter getQuarter
      rw [dif_pos hpos]
      rw [dif_neg (by simpa [List.length_set] using hp)]
      rw [dif_neg hp]
      by_cases h : (pl, pd) = (il, id)
      · cases h
        exact False.elim (hp hpos)
      · simp [h]
  · unfold setQuarter getQuarter
    rw [dif_neg hpos]
    by_cases hp : pl < s.length
    · rw [dif_pos hp]
      simp [hpos]
    · rw [dif_neg hp]
      simp [hpos]

/-- 位置がシェイプ範囲内か。 -/
def isValid (s : Shape) (pos : QuarterPos) : Bool := decide (pos.1 < s.length)

/-- シェイプの全有効位置を列挙する（レイヤ昇順 × 4 方角）。 -/
def allValid (s : Shape) : List QuarterPos :=
  (List.range s.length).flatMap (fun n => Direction.all.map (fun d => (n, d)))

/-- 時計回り 90° 回転: 方角を +1。 -/
def rotateCW (pos : QuarterPos) : QuarterPos := (pos.1, pos.2 + 1)

/-- 反時計回り 90° 回転: 方角を -1。 -/
def rotateCCW (pos : QuarterPos) : QuarterPos := (pos.1, pos.2 - 1)

/-- 位置を 1 レイヤ下へ移す。layer 0 では `Nat` subtraction により layer 0 に留まる。 -/
def down (pos : QuarterPos) : QuarterPos := (pos.1 - 1, pos.2)

/-- 位置を 1 レイヤ下へ移せる場合だけ返す optional 版。 -/
def down? (pos : QuarterPos) : Option QuarterPos :=
  if 0 < pos.1 then some pos.down else none

@[simp] theorem down_fst (pos : QuarterPos) : pos.down.1 = pos.1 - 1 := rfl

@[simp] theorem down_snd (pos : QuarterPos) : pos.down.2 = pos.2 := rfl

@[simp] theorem down?_eq_none_of_layer_zero {pos : QuarterPos} (h : pos.1 = 0) :
    pos.down? = none := by
  simp [down?, h]

@[simp] theorem down?_eq_some_of_layer_pos {pos : QuarterPos} (h : 0 < pos.1) :
    pos.down? = some pos.down := by
  simp [down?, h]

end QuarterPos

namespace Shape

/-- 同じ長さで、全位置の `getQuarter` が一致する `Shape` は等しい。 -/
theorem ext_getQuarter {a b : Shape}
    (hlen : a.length = b.length)
    (hget : ∀ p : QuarterPos, QuarterPos.getQuarter a p = QuarterPos.getQuarter b p) :
    a = b := by
  apply List.ext_getElem
  · exact hlen
  · intro n ha hb
    funext d
    have h := hget (n, d)
    simp [QuarterPos.getQuarter, ha, hb] at h
    exact h

/-- 指定位置リストを空象限に置換する。 -/
def clearPositions (s : Shape) (positions : List QuarterPos) : Shape :=
  positions.foldl (fun acc p => QuarterPos.setQuarter acc p Quarter.empty) s

/-- `clearPositions` はシェイプのレイヤ数を変えない。 -/
@[simp] theorem length_clearPositions (s : Shape) (positions : List QuarterPos) :
    (clearPositions s positions).length = s.length := by
  induction positions generalizing s with
  | nil => simp [clearPositions]
  | cons p ps ih =>
      unfold clearPositions
      change (clearPositions (QuarterPos.setQuarter s p Quarter.empty) ps).length = s.length
      rw [ih, QuarterPos.length_setQuarter]

/-- `clearPositions` 後の点取得仕様。指定リストに含まれる位置は空、それ以外は不変。 -/
theorem getQuarter_clearPositions (s : Shape) (positions : List QuarterPos) (p : QuarterPos) :
    QuarterPos.getQuarter (clearPositions s positions) p =
      if p ∈ positions then Quarter.empty else QuarterPos.getQuarter s p := by
  induction positions generalizing s with
  | nil => simp [clearPositions]
  | cons x xs ih =>
      unfold clearPositions
      change QuarterPos.getQuarter
        (clearPositions (QuarterPos.setQuarter s x Quarter.empty) xs) p = _
      rw [ih]
      rw [QuarterPos.getQuarter_setQuarter]
      by_cases hxs : p ∈ xs
      · simp [hxs]
      · by_cases hpx : p = x
        · subst x
          by_cases hpValid : p.1 < s.length
          · simp [hxs, hpValid]
          · simp [hxs, hpValid, QuarterPos.getQuarter]
        · simp [hxs, hpx]

/-- `clearPositions` で指定された位置は空になる。 -/
theorem getQuarter_clearPositions_of_mem {s : Shape} {positions : List QuarterPos}
    {p : QuarterPos} (h : p ∈ positions) :
    QuarterPos.getQuarter (clearPositions s positions) p = Quarter.empty := by
  rw [getQuarter_clearPositions]
  simp [h]

/-- `clearPositions` で指定されない位置は不変。 -/
theorem getQuarter_clearPositions_of_not_mem {s : Shape} {positions : List QuarterPos}
    {p : QuarterPos} (h : p ∉ positions) :
    QuarterPos.getQuarter (clearPositions s positions) p = QuarterPos.getQuarter s p := by
  rw [getQuarter_clearPositions]
  simp [h]

end Shape

end S2IL
