-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.Shape
import S2IL.Behavior.Rotate
import Aesop

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

/-- paintLayer と 180° 回転は可換である -/
@[aesop norm simp] theorem paintLayer_rotate180 (l : Layer) (color : Color) :
        (paintLayer l color).rotate180 = paintLayer l.rotate180 color := by
    simp only [paintLayer, Layer.rotate180, Layer.rotateCW]

/-- paintLayer と時計回り 90° 回転は可換である -/
@[aesop norm simp] theorem paintLayer_rotateCW (l : Layer) (color : Color) :
        (paintLayer l color).rotateCW = paintLayer l.rotateCW color := by
    simp only [paintLayer, Layer.rotateCW]

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

/-- 着色と時計回り 90° 回転は可換である -/
@[aesop norm simp] theorem paint_rotateCW_comm (s : Shape) (color : Color) :
        (s.paint color).rotateCW = (s.rotateCW).paint color := by
    simp only [paint, rotateCW, mapLayers]
    congr 1
    rw [List.map_append, List.map_cons, List.map_nil, List.map_dropLast]
    congr 1
    rw [Painter.paintLayer_rotateCW, List.getLast_map]

/-- 着色と 180° 回転は可換である（rotateCW² のコロラリー） -/
@[aesop norm simp] theorem paint_rotate180_comm (s : Shape) (color : Color) :
        (s.paint color).rotate180 = (s.rotate180).paint color := by
    simp only [rotate180_eq_rotateCW_rotateCW, paint_rotateCW_comm]

/-- 着色と反時計回り 90° 回転は可換である（rotateCW³ のコロラリー） -/
@[aesop norm simp] theorem paint_rotateCCW_comm (s : Shape) (color : Color) :
        (s.paint color).rotateCCW = (s.rotateCCW).paint color := by
    simp only [rotateCCW_eq_rotateCW_rotateCW_rotateCW, paint_rotateCW_comm]

end Shape
