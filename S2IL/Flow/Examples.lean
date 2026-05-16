-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Flow.Equivariance

/-!
# S2IL.Flow.Examples

Layer C-1 の代表フロー。

MAM に直結する象限抽出は、現行の E/W 方向定義と照合してから theorem 化する。
このファイルではまず、安全な小規模代表例を置く。
-/

namespace S2IL
namespace Flow.Examples

/-- 1 レイヤから指定方角だけを残す補助仕様。 -/
def layerOnlyDirection (direction : Direction) (layer : Layer) : Layer :=
  fun candidate => if candidate = direction then layer candidate else Quarter.empty

/-- Shape の各レイヤから指定方角だけを残す補助仕様。 -/
def shapeOnlyDirection (direction : Direction) (shape : Shape) : Shape :=
  shape.map (layerOnlyDirection direction)

/-- CW 回転してから指定色で着色する代表フロー。 -/
def rotateThenPaint (color : Color) : Flow Shape Shape :=
  Flow.comp Flow.rotateCW (Flow.paint color)

/-- `cut` で分けた東西半分をそのまま再合成する代表フロー。 -/
def cutThenCombine : Flow Shape Shape :=
  Flow.comp Flow.cut Flow.combineHalves

/-- ペアの両側を同じ色で着色する product flow。 -/
def paintBoth (color : Color) : Flow (Shape × Shape) (Shape × Shape) :=
  Flow.pairMap (Flow.paint color) (Flow.paint color)

/-- ペアの両側を CW 回転する product flow。 -/
def rotateBothCW : Flow (Shape × Shape) (Shape × Shape) :=
  Flow.pairMap Flow.rotateCW Flow.rotateCW

/-- 2 色を混色してから Shape に塗る代表フロー。 -/
def mixThenPaint : Flow (Shape × (Color × Color)) Shape :=
  Flow.comp (Flow.second Flow.mix) Flow.paintWith

/-- 2 色を混色してから Shape に結晶を生成する代表フロー。 -/
def mixThenCrystallize : Flow (Shape × (Color × Color)) Shape :=
  Flow.comp (Flow.second Flow.mix) Flow.crystallizeWith

/-- Cutter の両出力を同じ色で塗ってから再合成する代表フロー。 -/
def cutPaintBothCombine (color : Color) : Flow Shape Shape :=
  Flow.comp Flow.cut (Flow.comp (paintBoth color) Flow.combineHalves)

/-- 現行 E/W 実装に基づく NE 象限抽出フロー。抽出後は元の NE 位置へ戻す。 -/
def extractNE : Flow Shape Shape :=
  Flow.comp (Flow.comp Flow.halfDestroy Flow.rotateCW)
    (Flow.comp Flow.halfDestroy Flow.rotateCCW)

/-- 現行 E/W 実装に基づく SE 象限抽出フロー。抽出後は元の SE 位置へ戻す。 -/
def extractSE : Flow Shape Shape :=
  Flow.comp (Flow.comp Flow.halfDestroy Flow.rotateCCW)
    (Flow.comp Flow.halfDestroy Flow.rotateCW)

/-- 現行 E/W 実装に基づく SW 象限抽出フロー。抽出後は元の SW 位置へ戻す。 -/
def extractSW : Flow Shape Shape :=
  Flow.comp (Flow.comp Flow.rotate180 extractNE) Flow.rotate180

/-- 現行 E/W 実装に基づく NW 象限抽出フロー。抽出後は元の NW 位置へ戻す。 -/
def extractNW : Flow Shape Shape :=
  Flow.comp (Flow.comp Flow.rotate180 extractSE) Flow.rotate180

private theorem layer_extractNE_eq (layer : Layer) :
    Layer.rotateCCW (Layer.eastHalf (Layer.rotateCW (Layer.eastHalf layer))) =
      layerOnlyDirection Direction.ne layer := by
  funext direction
  rcases direction with ⟨value, isLt⟩
  match value, isLt with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

private theorem layer_extractSE_eq (layer : Layer) :
    Layer.rotateCW (Layer.eastHalf (Layer.rotateCCW (Layer.eastHalf layer))) =
      layerOnlyDirection Direction.se layer := by
  funext direction
  rcases direction with ⟨value, isLt⟩
  match value, isLt with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

private theorem layer_rotate180_onlyNE_eq_onlySW (layer : Layer) :
    Layer.rotate180 (layerOnlyDirection Direction.ne (Layer.rotate180 layer)) =
      layerOnlyDirection Direction.sw layer := by
  funext direction
  rcases direction with ⟨value, isLt⟩
  match value, isLt with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

private theorem layer_rotate180_onlySE_eq_onlyNW (layer : Layer) :
    Layer.rotate180 (layerOnlyDirection Direction.se (Layer.rotate180 layer)) =
      layerOnlyDirection Direction.nw layer := by
  funext direction
  rcases direction with ⟨value, isLt⟩
  match value, isLt with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

/-- `extractNE` は各レイヤの NE 象限だけを残す。 -/
theorem extractNE_eval (shape : Shape) :
    Flow.eval extractNE shape = shapeOnlyDirection Direction.ne shape := by
  change Shape.rotateCCW (Shape.halfDestroy (Shape.rotateCW (Shape.halfDestroy shape))) =
    shapeOnlyDirection Direction.ne shape
  unfold Shape.halfDestroy Shape.eastHalf Shape.rotateCW Shape.rotateCCW shapeOnlyDirection
  simp only [Shape.rotateCW, List.map_map]
  apply List.map_congr_left
  intro layer _
  exact layer_extractNE_eq layer

/-- `extractSE` は各レイヤの SE 象限だけを残す。 -/
theorem extractSE_eval (shape : Shape) :
    Flow.eval extractSE shape = shapeOnlyDirection Direction.se shape := by
  change Shape.rotateCW (Shape.halfDestroy (Shape.rotateCCW (Shape.halfDestroy shape))) =
    shapeOnlyDirection Direction.se shape
  unfold Shape.halfDestroy Shape.eastHalf Shape.rotateCW Shape.rotateCCW shapeOnlyDirection
  simp only [Shape.rotateCW, List.map_map]
  apply List.map_congr_left
  intro layer _
  exact layer_extractSE_eq layer

/-- `extractSW` は各レイヤの SW 象限だけを残す。 -/
theorem extractSW_eval (shape : Shape) :
    Flow.eval extractSW shape = shapeOnlyDirection Direction.sw shape := by
  change Shape.rotate180 (Flow.eval extractNE (Shape.rotate180 shape)) =
    shapeOnlyDirection Direction.sw shape
  rw [extractNE_eval]
  unfold Shape.rotate180 Shape.rotateCW shapeOnlyDirection
  simp only [List.map_map]
  apply List.map_congr_left
  intro layer _
  exact layer_rotate180_onlyNE_eq_onlySW layer

/-- `extractNW` は各レイヤの NW 象限だけを残す。 -/
theorem extractNW_eval (shape : Shape) :
    Flow.eval extractNW shape = shapeOnlyDirection Direction.nw shape := by
  change Shape.rotate180 (Flow.eval extractSE (Shape.rotate180 shape)) =
    shapeOnlyDirection Direction.nw shape
  rw [extractSE_eval]
  unfold Shape.rotate180 Shape.rotateCW shapeOnlyDirection
  simp only [List.map_map]
  apply List.map_congr_left
  intro layer _
  exact layer_rotate180_onlySE_eq_onlyNW layer

noncomputable section

/-- Stacker 後に指定色で着色する生成系の代表フロー。 -/
def stackThenPaint (config : GameConfig) (color : Color) : Flow (Shape × Shape) Shape :=
  Flow.comp (Flow.stack config) (Flow.paint color)

/-- Swapper 後に Stacker を適用する生成系の代表フロー。 -/
def swapThenStack (config : GameConfig) : Flow (Shape × Shape) Shape :=
  Flow.comp Flow.swapShapes (Flow.stack config)

/-- 結晶生成後に Gravity を適用する生成系の代表フロー。 -/
def crystallizeThenGravity (color : Color) : Flow Shape Shape :=
  Flow.comp (Flow.crystallize color) Flow.gravity

/-- Pin Pusher 後に指定色で着色する生成系の代表フロー。 -/
def pinPushThenPaint (config : GameConfig) (color : Color) : Flow Shape Shape :=
  Flow.comp (Flow.pinPush config) (Flow.paint color)

end

/-- `cutThenCombine` は外延的に `id` と等しい。 -/
theorem cutThenCombine_equivalent_id :
    Flow.Equivalent cutThenCombine (Flow.id : Flow Shape Shape) := by
  intro shape
  change Shape.combineHalves (Shape.eastHalf shape) (Shape.westHalf shape) = shape
  exact Shape.combineHalves.eastHalf_westHalf shape

/-- 結晶生成後に Gravity を通した代表フローは settled な Shape を返す。 -/
theorem crystallizeThenGravity_isSettled (color : Color) (shape : Shape) :
    IsSettled (Flow.eval (crystallizeThenGravity color) shape) := by
  change IsSettled (Shape.gravity (Shape.crystallize shape color))
  exact Shape.gravity.isSettled (Shape.crystallize shape color)

/-- `mixThenPaint` は Color Mixer の出力色で Painter を適用する。 -/
theorem mixThenPaint_eval (input : Shape × (Color × Color)) :
    Flow.eval mixThenPaint input =
      Shape.paint input.1 (S2IL.Operations.mix input.2.1 input.2.2) := rfl

/-- `mixThenCrystallize` は Color Mixer の出力色で Crystal Generator を適用する。 -/
theorem mixThenCrystallize_eval (input : Shape × (Color × Color)) :
    Flow.eval mixThenCrystallize input =
      Shape.crystallize input.1 (S2IL.Operations.mix input.2.1 input.2.2) := rfl

/-- `swapThenStack` は Swapper の出力ペアを Stacker に渡す。 -/
theorem swapThenStack_eval (config : GameConfig) (input : Shape × Shape) :
    Flow.eval (swapThenStack config) input =
      Shape.stack (Shape.swap input.1 input.2).1 (Shape.swap input.1 input.2).2 config := rfl

end Flow.Examples
end S2IL
