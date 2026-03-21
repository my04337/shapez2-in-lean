-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.Shape

/-!
# Painter (着色機)

着色機の動作を定義する。

## 概要

着色機はシェイプと液剤（`Color`）を受け取り、
シェイプの **最上位レイヤ (topmost layer)** の着色可能な象限の色を置き換える。

- 着色対象は `colored part color` の象限のみ
- 結晶 (`crystal`)、ピン (`pin`)、空 (`empty`) の象限は着色されない
- 既に着色されている象限は新しい色で上書きされる
- 最上位レイヤ以外のレイヤは影響を受けない
-/

namespace Painter

/-- 象限を着色する。`colored` なら色を置き換え、それ以外はそのまま返す -/
def paintQuarter (q : Quarter) (color : Color) : Quarter :=
    match q with
    | .colored part _ => .colored part color
    | _ => q

/-- レイヤの全象限を着色する -/
def paintLayer (l : Layer) (color : Color) : Layer :=
    ⟨paintQuarter l.ne color, paintQuarter l.se color,
     paintQuarter l.sw color, paintQuarter l.nw color⟩

end Painter

namespace Shape

/-- 着色機を適用する。最上位レイヤの着色可能な象限の色を置き換える -/
def paint (s : Shape) (color : Color) : Shape :=
    match s.upper.dropLast, s.upper.getLast? with
    | rest, some top => ⟨s.bottom, rest ++ [Painter.paintLayer top color]⟩
    | _, none        => ⟨Painter.paintLayer s.bottom color, []⟩

end Shape
