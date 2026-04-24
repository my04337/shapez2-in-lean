-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel
import S2IL.Operations.Gravity
import S2IL.Operations.Shatter

/-!
# S2IL.Operations.Cutter

切断機 (A-2-1 + B-4-2)。東西切断と安定化を行う。

## 公開 API

- `Layer.eastHalf` / `Layer.westHalf` / `Layer.combineEastWest`
- `Shape.eastHalf` / `Shape.westHalf` / `Shape.combineHalves`
- `Shape.cut : Shape → Option Shape × Option Shape`
- `Shape.halfDestroy : Shape → Option Shape`
- 構造的恒等式と **180° 回転等変性**

## 単一チェーン原則の例外：E/W 参照操作

切断系 (cut / halfDestroy / swap / shatterOnCut / eastHalf / westHalf / combineHalves)
は **絶対方角 E/W** に依存する。CW 90° 回転は E/W 軸を N/S 軸へ写すため、
`s.rotateCW.cut = (s.cut.1.map rotateCW, s.cut.2.map rotateCW)` は **一般に偽**
（反例: `CgRgCrSr` の東半分は `CgRg----`、CW 回転後のシェイプ `SrCgRgCr` の
東半分は `SrCg----`）。

これらの操作は CW ではなく `rotate180` 下で綺麗な等変性を持つ。180° 回転は
E↔W を入れ替えるため、タプルの成分も swap する:

$$s.\mathrm{rotate180}.\mathrm{cut} = (s.\mathrm{cut.2}.\mathrm{rotate180},\ s.\mathrm{cut.1}.\mathrm{rotate180})$$

本ファイルでは `rotate180_comm` を primitive axiom として置き、CW_comm / CCW_comm
は導出しない（そもそも成立しない）。architecture-layer-ab.md §1.4 参照。
-/

namespace S2IL

-- ============================================================
-- Layer level
-- ============================================================

axiom Layer.eastHalf : Layer → Layer
axiom Layer.westHalf : Layer → Layer
axiom Layer.combineEastWest : Layer → Layer → Layer

axiom Layer.combineEastWest_eastHalf_westHalf (l : Layer) :
    Layer.combineEastWest l.eastHalf l.westHalf = l

-- ============================================================
-- Shape level
-- ============================================================

axiom Shape.eastHalf : Shape → Shape
axiom Shape.westHalf : Shape → Shape
axiom Shape.combineHalves : Shape → Shape → Shape
axiom Shape.cut : Shape → Option Shape × Option Shape
axiom Shape.halfDestroy : Shape → Option Shape

axiom Shape.combineHalves_eastHalf_westHalf (s : Shape) :
    Shape.combineHalves s.eastHalf s.westHalf = s

axiom Shape.halfDestroy_eq_cut_east (s : Shape) :
    s.halfDestroy = s.cut.1

axiom Shape.combineHalves_self (s : Shape) :
    Shape.combineHalves s s = s

-- ============================================================
-- Equivariance (rotate180 only; CW / CCW do NOT hold)
-- ============================================================

/-- 東半分と 180° 回転: 180° 回転は E↔W を入れ替えるため、
    元の西半分を 180° 回転したものが rotated の東半分になる。 -/
axiom Shape.eastHalf_rotate180_comm (s : Shape) :
    s.rotate180.eastHalf = s.westHalf.rotate180

/-- 西半分と 180° 回転: 対称に、元の東半分の 180° 回転が rotated の西半分。 -/
axiom Shape.westHalf_rotate180_comm (s : Shape) :
    s.rotate180.westHalf = s.eastHalf.rotate180

/-- `cut` と 180° 回転: 成分が swap される。 -/
axiom Shape.cut_rotate180_comm (s : Shape) :
    s.rotate180.cut =
      (s.cut.2.map Shape.rotate180, s.cut.1.map Shape.rotate180)

/-- `halfDestroy` と 180° 回転: 元の西半分（= `cut.2`）が rotated 後の残存側になる。 -/
axiom Shape.halfDestroy_rotate180_comm (s : Shape) :
    s.rotate180.halfDestroy = s.cut.2.map Shape.rotate180

end S2IL
