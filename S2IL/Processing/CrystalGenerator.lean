-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.Shape

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

end CrystalGenerator

namespace Shape

/-- 結晶製造機を適用する。空象限とピン象限を指定色の結晶で充填する -/
def crystallize (s : Shape) (color : Color) : Shape :=
    ⟨CrystalGenerator.fillLayer s.bottom color,
     s.upper.map (CrystalGenerator.fillLayer · color)⟩

end Shape
