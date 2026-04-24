-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.Shape
import S2IL.Kernel.Transform.Rotate
import Aesop

/-!
# CrystalGenerator (結晶製造機)

結晶製造機の動作を定義する。

## 概要

結晶製造機はシェイプと液剤（`Color`）を受け取り、
シェイプ内の **空象限 (empty)** および **ピン象限 (pin)** を
液剤と同じ色の **結晶 (crystal)** で充填する。

- 全レイヤが対象となる（複数レイヤにまたがって充填される）
- 通常パーツ (`colored`) や既存の結晶 (`crystal`) は変更されない
- 落下・砕け散り・結合処理は発生しない

複数の結晶製造機を連続させることで、異なる色の結晶を1つのシェイプ内に
組み合わせることができる。
-/

namespace CrystalGenerator

/-- 象限を結晶で充填する。空・ピンなら指定色の結晶に、それ以外はそのまま返す -/
def fillQuarter (q : Quarter) (color : Color) : Quarter :=
    match q with
    | .empty => .crystal color
    | .pin   => .crystal color
    | _      => q

/-- レイヤの全象限を結晶で充填する -/
def fillLayer (l : Layer) (color : Color) : Layer :=
    ⟨fillQuarter l.ne color, fillQuarter l.se color,
     fillQuarter l.sw color, fillQuarter l.nw color⟩

-- ============================================================
-- 定理
-- ============================================================

/-- fillQuarter は colored 象限を保存する -/
theorem fillQuarter_colored (p : RegularPartCode) (c color : Color) :
        fillQuarter (.colored p c) color = .colored p c := rfl

/-- fillQuarter は crystal 象限を保存する -/
theorem fillQuarter_crystal (c color : Color) :
        fillQuarter (.crystal c) color = .crystal c := rfl

/-- fillQuarter は冪等である（同じ色で2回適用しても結果は同じ） -/
@[simp] theorem fillQuarter_idempotent (q : Quarter) (color : Color) :
        fillQuarter (fillQuarter q color) color = fillQuarter q color := by
    cases q <;> rfl

/-- fillLayer は冪等である -/
@[simp] theorem fillLayer_idempotent (l : Layer) (color : Color) :
        fillLayer (fillLayer l color) color = fillLayer l color := by
    simp only [fillLayer, fillQuarter_idempotent]

/-- fillLayer と 180° 回転は可換である -/
@[aesop norm simp] theorem fillLayer_rotate180 (l : Layer) (color : Color) :
        (fillLayer l color).rotate180 = fillLayer l.rotate180 color := by
    simp only [fillLayer, Layer.rotate180, Layer.rotateCW]

/-- fillLayer と時計回り 90° 回転は可換である -/
@[aesop norm simp] theorem fillLayer_rotateCW (l : Layer) (color : Color) :
        (fillLayer l color).rotateCW = fillLayer l.rotateCW color := by
    simp only [fillLayer, Layer.rotateCW]

end CrystalGenerator

namespace Shape

/-- 結晶製造機を適用する。空象限とピン象限を指定色の結晶で充填する -/
def crystallize (s : Shape) (color : Color) : Shape :=
    s.mapLayers (CrystalGenerator.fillLayer · color)

-- ============================================================
-- 定理
-- ============================================================

/-- crystallize は冪等である -/
@[simp] theorem crystallize_idempotent (s : Shape) (color : Color) :
        (s.crystallize color).crystallize color = s.crystallize color := by
    ext; simp only [crystallize, mapLayers, List.map_map, List.getElem?_map,
        Option.map_eq_some_iff, Function.comp_apply, CrystalGenerator.fillLayer_idempotent]

/-- 結晶製造と時計回り 90° 回転は可換である -/
@[aesop norm simp] theorem crystallize_rotateCW_comm (s : Shape) (color : Color) :
        (s.crystallize color).rotateCW = (s.rotateCW).crystallize color := by
    ext
    simp only [crystallize, rotateCW, mapLayers, List.map_map,
        List.getElem?_map, Option.map_eq_some_iff, Function.comp_apply]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, (CrystalGenerator.fillLayer_rotateCW a color).symm⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, CrystalGenerator.fillLayer_rotateCW a color⟩

/-- 結晶製造と 180° 回転は可換である（rotateCW² のコロラリー） -/
@[aesop norm simp] theorem crystallize_rotate180_comm (s : Shape) (color : Color) :
        (s.crystallize color).rotate180 = (s.rotate180).crystallize color := by
    simp only [rotate180_eq_rotateCW_rotateCW, crystallize_rotateCW_comm]

/-- 結晶製造と反時計回り 90° 回転は可換である（rotateCW³ のコロラリー） -/
@[aesop norm simp] theorem crystallize_rotateCCW_comm (s : Shape) (color : Color) :
        (s.crystallize color).rotateCCW = (s.rotateCCW).crystallize color := by
    simp only [rotateCCW_eq_rotateCW_rotateCW_rotateCW, crystallize_rotateCW_comm]

end Shape
