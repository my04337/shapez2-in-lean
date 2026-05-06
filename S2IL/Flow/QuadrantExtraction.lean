import S2IL.Operations

/-!
# S2IL.Flow.QuadrantExtraction

固定加工ライン例としての象限抽出 theorem。

`halfDestroy` は E/W 参照操作なので CW 等変性は持たない。
ここでは `halfDestroy -> rotate* -> halfDestroy` の点ごとの仕様と、
全象限を NE 位置へ抽出する代表工程の仕様だけを公開する。
-/

namespace S2IL
namespace Flow.QuadrantExtraction

/-- `source` の象限だけを `target` に残し、他象限を空にする shape-level 仕様。 -/
def keepOnlyAt (s : Shape) (source target : Direction) : Shape :=
  s.map fun l => fun d => if d = target then l source else Quarter.empty

/-- 東半分は NE/SE を保存する。 -/
theorem eastHalf_preserves_east (l : Layer) {d : Direction} (h : d.val < 2) :
    Layer.eastHalf l d = l d := by
  simp [Layer.eastHalf, h]

/-- 東半分は SW/NW を空にする。 -/
theorem eastHalf_clears_west (l : Layer) {d : Direction} (h : 2 ≤ d.val) :
    Layer.eastHalf l d = Quarter.empty := by
  have hlt : ¬ d.val < 2 := by omega
  simp [Layer.eastHalf, hlt]

/-- `halfDestroy` の点ごとの仕様。範囲外位置は空のまま。 -/
theorem halfDestroy_getQuarter (s : Shape) (n : Nat) (d : Direction) :
    QuarterPos.getQuarter (Shape.halfDestroy s) (n, d) =
      if d.val < 2 then QuarterPos.getQuarter s (n, d) else Quarter.empty := by
  by_cases h : n < s.length
  · simp [Shape.halfDestroy, Shape.eastHalf, QuarterPos.getQuarter, h]
  · simp [Shape.halfDestroy, Shape.eastHalf, QuarterPos.getQuarter, h]

/-- CW 回転後の `getDir` は元レイヤの `d - 1` を参照する。 -/
theorem rotateCW_getDir (l : Layer) (d : Direction) :
    l.rotateCW.getDir d = l.getDir (d - 1) := rfl

/-- CCW 回転後の `getDir` は元レイヤの `d + 1` を参照する。 -/
theorem rotateCCW_getDir (l : Layer) (d : Direction) :
    l.rotateCCW.getDir d = l.getDir (d + 1) := by
  rcases d with ⟨v, hv⟩
  match v, hv with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

/-- 180° 回転後の `getDir` は元レイヤの `d - 2` を参照する。 -/
theorem rotate180_getDir (l : Layer) (d : Direction) :
    l.rotate180.getDir d = l.getDir (d - 2) := by
  rcases d with ⟨v, hv⟩
  match v, hv with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

/-- `keepOnlyAt` の点ごとの仕様。 -/
theorem keepOnlyAt_getQuarter
    (s : Shape) (source target : Direction) (n : Nat) (d : Direction) :
    QuarterPos.getQuarter (keepOnlyAt s source target) (n, d) =
      if d = target then QuarterPos.getQuarter s (n, source) else Quarter.empty := by
  by_cases h : n < s.length
  · simp [keepOnlyAt, QuarterPos.getQuarter, h]
  · simp [keepOnlyAt, QuarterPos.getQuarter, h]

/-- `halfDestroy -> rotateCW -> halfDestroy` は元 NE を SE に残す。 -/
theorem extractAfterRotateCW_getQuarter (s : Shape) (n : Nat) (d : Direction) :
    QuarterPos.getQuarter
        (Shape.halfDestroy (Shape.rotateCW (Shape.halfDestroy s))) (n, d) =
      if d = 1 then QuarterPos.getQuarter s (n, 0) else Quarter.empty := by
  by_cases h : n < s.length
  · rcases d with ⟨v, hv⟩
    match v, hv with
    | 0, _ => simp [Shape.halfDestroy, Shape.eastHalf, Shape.rotateCW,
        QuarterPos.getQuarter, h]
    | 1, _ => simp [Shape.halfDestroy, Shape.eastHalf, Shape.rotateCW,
        QuarterPos.getQuarter, h]
    | 2, _ => simp [Shape.halfDestroy, Shape.eastHalf, Shape.rotateCW,
        QuarterPos.getQuarter, h]
    | 3, _ => simp [Shape.halfDestroy, Shape.eastHalf, Shape.rotateCW,
        QuarterPos.getQuarter, h]
  · rcases d with ⟨v, hv⟩
    match v, hv with
    | 0, _ => simp [Shape.halfDestroy, Shape.eastHalf, Shape.rotateCW,
        QuarterPos.getQuarter, h]
    | 1, _ => simp [Shape.halfDestroy, Shape.eastHalf, Shape.rotateCW,
        QuarterPos.getQuarter, h]
    | 2, _ => simp [Shape.halfDestroy, Shape.eastHalf, Shape.rotateCW,
        QuarterPos.getQuarter, h]
    | 3, _ => simp [Shape.halfDestroy, Shape.eastHalf, Shape.rotateCW,
        QuarterPos.getQuarter, h]

/-- `halfDestroy -> rotateCCW -> halfDestroy` は元 SE を NE に残す。 -/
theorem extractAfterRotateCCW_getQuarter (s : Shape) (n : Nat) (d : Direction) :
    QuarterPos.getQuarter
        (Shape.halfDestroy (Shape.rotateCCW (Shape.halfDestroy s))) (n, d) =
      if d = 0 then QuarterPos.getQuarter s (n, 1) else Quarter.empty := by
  by_cases h : n < s.length
  · rcases d with ⟨v, hv⟩
    match v, hv with
    | 0, _ => simp [Shape.halfDestroy, Shape.eastHalf, Shape.rotateCCW,
        Shape.rotateCW, QuarterPos.getQuarter, h]
    | 1, _ => simp [Shape.halfDestroy, Shape.eastHalf, Shape.rotateCCW,
        Shape.rotateCW, QuarterPos.getQuarter, h]
    | 2, _ => simp [Shape.halfDestroy, Shape.eastHalf, Shape.rotateCCW,
        Shape.rotateCW, QuarterPos.getQuarter, h]
    | 3, _ => simp [Shape.halfDestroy, Shape.eastHalf, Shape.rotateCCW,
        Shape.rotateCW, QuarterPos.getQuarter, h]
  · rcases d with ⟨v, hv⟩
    match v, hv with
    | 0, _ => simp [Shape.halfDestroy, Shape.eastHalf, Shape.rotateCCW,
        Shape.rotateCW, QuarterPos.getQuarter, h]
    | 1, _ => simp [Shape.halfDestroy, Shape.eastHalf, Shape.rotateCCW,
        Shape.rotateCW, QuarterPos.getQuarter, h]
    | 2, _ => simp [Shape.halfDestroy, Shape.eastHalf, Shape.rotateCCW,
        Shape.rotateCW, QuarterPos.getQuarter, h]
    | 3, _ => simp [Shape.halfDestroy, Shape.eastHalf, Shape.rotateCCW,
        Shape.rotateCW, QuarterPos.getQuarter, h]

/-- `halfDestroy -> rotate180 -> halfDestroy` は、最初の東半分が西側へ移るため空になる。 -/
theorem extractAfterRotate180_getQuarter (s : Shape) (n : Nat) (d : Direction) :
    QuarterPos.getQuarter
        (Shape.halfDestroy (Shape.rotate180 (Shape.halfDestroy s))) (n, d) =
      Quarter.empty := by
  by_cases h : n < s.length
  · rcases d with ⟨v, hv⟩
    match v, hv with
    | 0, _ => simp [Shape.halfDestroy, Shape.eastHalf, Shape.rotate180,
        Shape.rotateCW, QuarterPos.getQuarter, h]
    | 1, _ => simp [Shape.halfDestroy, Shape.eastHalf, Shape.rotate180,
        Shape.rotateCW, QuarterPos.getQuarter, h]
    | 2, _ => simp [Shape.halfDestroy, Shape.eastHalf, Shape.rotate180,
        Shape.rotateCW, QuarterPos.getQuarter, h]
    | 3, _ => simp [Shape.halfDestroy, Shape.eastHalf, Shape.rotate180,
        Shape.rotateCW, QuarterPos.getQuarter, h]
  · rcases d with ⟨v, hv⟩
    match v, hv with
    | 0, _ => simp [Shape.halfDestroy, Shape.eastHalf, Shape.rotate180,
        Shape.rotateCW, QuarterPos.getQuarter, h]
    | 1, _ => simp [Shape.halfDestroy, Shape.eastHalf, Shape.rotate180,
        Shape.rotateCW, QuarterPos.getQuarter, h]
    | 2, _ => simp [Shape.halfDestroy, Shape.eastHalf, Shape.rotate180,
        Shape.rotateCW, QuarterPos.getQuarter, h]
    | 3, _ => simp [Shape.halfDestroy, Shape.eastHalf, Shape.rotate180,
        Shape.rotateCW, QuarterPos.getQuarter, h]

/-- 元 NE を NE 位置へ抽出する代表工程。 -/
def extractNEToNE (s : Shape) : Shape :=
  Shape.rotateCCW (Shape.halfDestroy (Shape.rotateCW (Shape.halfDestroy s)))

/-- 元 SE を NE 位置へ抽出する代表工程。 -/
def extractSEToNE (s : Shape) : Shape :=
  Shape.halfDestroy (Shape.rotateCCW (Shape.halfDestroy s))

/-- 元 SW を NE 位置へ抽出する代表工程。 -/
def extractSWToNE (s : Shape) : Shape :=
  Shape.halfDestroy (Shape.rotateCCW (Shape.halfDestroy (Shape.rotateCCW s)))

/-- 元 NW を NE 位置へ抽出する代表工程。 -/
def extractNWToNE (s : Shape) : Shape :=
  Shape.rotateCCW (Shape.halfDestroy (Shape.rotateCW (Shape.halfDestroy (Shape.rotateCW s))))

/-- `extractNEToNE` は元 NE だけを NE に残す。 -/
theorem extractNEToNE_getQuarter (s : Shape) (n : Nat) (d : Direction) :
    QuarterPos.getQuarter (extractNEToNE s) (n, d) =
      if d = 0 then QuarterPos.getQuarter s (n, 0) else Quarter.empty := by
  by_cases h : n < s.length
  · rcases d with ⟨v, hv⟩
    match v, hv with
    | 0, _ => simp [extractNEToNE, Shape.halfDestroy, Shape.eastHalf,
        Shape.rotateCW, Shape.rotateCCW, QuarterPos.getQuarter, h]
    | 1, _ => simp [extractNEToNE, Shape.halfDestroy, Shape.eastHalf,
        Shape.rotateCW, Shape.rotateCCW, QuarterPos.getQuarter, h]
    | 2, _ => simp [extractNEToNE, Shape.halfDestroy, Shape.eastHalf,
        Shape.rotateCW, Shape.rotateCCW, QuarterPos.getQuarter, h]
    | 3, _ => simp [extractNEToNE, Shape.halfDestroy, Shape.eastHalf,
        Shape.rotateCW, Shape.rotateCCW, QuarterPos.getQuarter, h]
  · rcases d with ⟨v, hv⟩
    match v, hv with
    | 0, _ => simp [extractNEToNE, Shape.halfDestroy, Shape.eastHalf,
        Shape.rotateCW, Shape.rotateCCW, QuarterPos.getQuarter, h]
    | 1, _ => simp [extractNEToNE, Shape.halfDestroy, Shape.eastHalf,
        Shape.rotateCW, Shape.rotateCCW, QuarterPos.getQuarter, h]
    | 2, _ => simp [extractNEToNE, Shape.halfDestroy, Shape.eastHalf,
        Shape.rotateCW, Shape.rotateCCW, QuarterPos.getQuarter, h]
    | 3, _ => simp [extractNEToNE, Shape.halfDestroy, Shape.eastHalf,
        Shape.rotateCW, Shape.rotateCCW, QuarterPos.getQuarter, h]

/-- `extractSEToNE` は元 SE だけを NE に残す。 -/
theorem extractSEToNE_getQuarter (s : Shape) (n : Nat) (d : Direction) :
    QuarterPos.getQuarter (extractSEToNE s) (n, d) =
      if d = 0 then QuarterPos.getQuarter s (n, 1) else Quarter.empty := by
  simpa [extractSEToNE] using extractAfterRotateCCW_getQuarter s n d

/-- `extractSWToNE` は元 SW だけを NE に残す。 -/
theorem extractSWToNE_getQuarter (s : Shape) (n : Nat) (d : Direction) :
    QuarterPos.getQuarter (extractSWToNE s) (n, d) =
      if d = 0 then QuarterPos.getQuarter s (n, 2) else Quarter.empty := by
  by_cases h : n < s.length
  · rcases d with ⟨v, hv⟩
    match v, hv with
    | 0, _ => simp [extractSWToNE, Shape.halfDestroy, Shape.eastHalf,
        Shape.rotateCW, Shape.rotateCCW, QuarterPos.getQuarter, h]
    | 1, _ => simp [extractSWToNE, Shape.halfDestroy, Shape.eastHalf,
        Shape.rotateCW, Shape.rotateCCW, QuarterPos.getQuarter, h]
    | 2, _ => simp [extractSWToNE, Shape.halfDestroy, Shape.eastHalf,
        Shape.rotateCW, Shape.rotateCCW, QuarterPos.getQuarter, h]
    | 3, _ => simp [extractSWToNE, Shape.halfDestroy, Shape.eastHalf,
        Shape.rotateCW, Shape.rotateCCW, QuarterPos.getQuarter, h]
  · rcases d with ⟨v, hv⟩
    match v, hv with
    | 0, _ => simp [extractSWToNE, Shape.halfDestroy, Shape.eastHalf,
        Shape.rotateCW, Shape.rotateCCW, QuarterPos.getQuarter, h]
    | 1, _ => simp [extractSWToNE, Shape.halfDestroy, Shape.eastHalf,
        Shape.rotateCW, Shape.rotateCCW, QuarterPos.getQuarter, h]
    | 2, _ => simp [extractSWToNE, Shape.halfDestroy, Shape.eastHalf,
        Shape.rotateCW, Shape.rotateCCW, QuarterPos.getQuarter, h]
    | 3, _ => simp [extractSWToNE, Shape.halfDestroy, Shape.eastHalf,
        Shape.rotateCW, Shape.rotateCCW, QuarterPos.getQuarter, h]

/-- `extractNWToNE` は元 NW だけを NE に残す。 -/
theorem extractNWToNE_getQuarter (s : Shape) (n : Nat) (d : Direction) :
    QuarterPos.getQuarter (extractNWToNE s) (n, d) =
      if d = 0 then QuarterPos.getQuarter s (n, 3) else Quarter.empty := by
  by_cases h : n < s.length
  · rcases d with ⟨v, hv⟩
    match v, hv with
    | 0, _ => simp [extractNWToNE, Shape.halfDestroy, Shape.eastHalf,
        Shape.rotateCW, Shape.rotateCCW, QuarterPos.getQuarter, h]
    | 1, _ => simp [extractNWToNE, Shape.halfDestroy, Shape.eastHalf,
        Shape.rotateCW, Shape.rotateCCW, QuarterPos.getQuarter, h]
    | 2, _ => simp [extractNWToNE, Shape.halfDestroy, Shape.eastHalf,
        Shape.rotateCW, Shape.rotateCCW, QuarterPos.getQuarter, h]
    | 3, _ => simp [extractNWToNE, Shape.halfDestroy, Shape.eastHalf,
        Shape.rotateCW, Shape.rotateCCW, QuarterPos.getQuarter, h]
  · rcases d with ⟨v, hv⟩
    match v, hv with
    | 0, _ => simp [extractNWToNE, Shape.halfDestroy, Shape.eastHalf,
        Shape.rotateCW, Shape.rotateCCW, QuarterPos.getQuarter, h]
    | 1, _ => simp [extractNWToNE, Shape.halfDestroy, Shape.eastHalf,
        Shape.rotateCW, Shape.rotateCCW, QuarterPos.getQuarter, h]
    | 2, _ => simp [extractNWToNE, Shape.halfDestroy, Shape.eastHalf,
        Shape.rotateCW, Shape.rotateCCW, QuarterPos.getQuarter, h]
    | 3, _ => simp [extractNWToNE, Shape.halfDestroy, Shape.eastHalf,
        Shape.rotateCW, Shape.rotateCCW, QuarterPos.getQuarter, h]

/-- 全象限を NE 位置へ抽出できる。 -/
theorem complete (s : Shape) :
    extractNEToNE s = keepOnlyAt s 0 0 ∧
    extractSEToNE s = keepOnlyAt s 1 0 ∧
    extractSWToNE s = keepOnlyAt s 2 0 ∧
    extractNWToNE s = keepOnlyAt s 3 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Shape.ext_getQuarter
    · simp [extractNEToNE, keepOnlyAt, Shape.rotateCCW, Shape.rotateCW,
        Shape.halfDestroy, Shape.eastHalf]
    · intro p
      obtain ⟨n, d⟩ := p
      rw [extractNEToNE_getQuarter]
      rw [keepOnlyAt_getQuarter]
  · apply Shape.ext_getQuarter
    · simp [extractSEToNE, keepOnlyAt, Shape.rotateCCW, Shape.rotateCW,
        Shape.halfDestroy, Shape.eastHalf]
    · intro p
      obtain ⟨n, d⟩ := p
      rw [extractSEToNE_getQuarter]
      rw [keepOnlyAt_getQuarter]
  · apply Shape.ext_getQuarter
    · simp [extractSWToNE, keepOnlyAt, Shape.rotateCCW, Shape.rotateCW,
        Shape.halfDestroy, Shape.eastHalf]
    · intro p
      obtain ⟨n, d⟩ := p
      rw [extractSWToNE_getQuarter]
      rw [keepOnlyAt_getQuarter]
  · apply Shape.ext_getQuarter
    · simp [extractNWToNE, keepOnlyAt, Shape.rotateCCW, Shape.rotateCW,
        Shape.halfDestroy, Shape.eastHalf]
    · intro p
      obtain ⟨n, d⟩ := p
      rw [extractNWToNE_getQuarter]
      rw [keepOnlyAt_getQuarter]

end Flow.QuadrantExtraction
end S2IL
