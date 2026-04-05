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

-- ============================================================
-- 定理
-- ============================================================

/-- paintQuarter は empty 象限を保存する -/
theorem paintQuarter_empty (color : Color) :
        paintQuarter .empty color = .empty := rfl

/-- paintQuarter は pin 象限を保存する -/
theorem paintQuarter_pin (color : Color) :
        paintQuarter .pin color = .pin := rfl

/-- paintQuarter は crystal 象限を保存する -/
theorem paintQuarter_crystal (c color : Color) :
        paintQuarter (.crystal c) color = .crystal c := rfl

/-- paintQuarter は冪等である（同じ色で2回適用しても結果は同じ） -/
@[simp] theorem paintQuarter_idempotent (q : Quarter) (color : Color) :
        paintQuarter (paintQuarter q color) color = paintQuarter q color := by
    cases q <;> rfl

/-- paintLayer は冪等である -/
@[simp] theorem paintLayer_idempotent (l : Layer) (color : Color) :
        paintLayer (paintLayer l color) color = paintLayer l color := by
    simp only [paintLayer, paintQuarter_idempotent]

end Painter

namespace Shape

/-- 着色機を適用する。最上位レイヤの着色可能な象限の色を置き換える -/
def paint (s : Shape) (color : Color) : Shape :=
    let initLayers := s.layers.dropLast
    let topLyr := s.layers.getLast s.layers_ne
    ⟨initLayers ++ [Painter.paintLayer topLyr color],
        by simp only [ne_eq, List.append_eq_nil_iff, List.cons_ne_self, and_false, not_false_eq_true]⟩

-- ============================================================
-- 定理
-- ============================================================

/-- paint は冪等である -/
@[simp] theorem paint_idempotent (s : Shape) (color : Color) :
        (s.paint color).paint color = s.paint color := by
    ext1; simp only [paint, ne_eq, List.cons_ne_self, not_false_eq_true,
        List.dropLast_append_of_ne_nil, List.dropLast_singleton, List.append_nil,
        List.getLast_append_of_ne_nil, List.getLast_singleton, Painter.paintLayer_idempotent]

end Shape
