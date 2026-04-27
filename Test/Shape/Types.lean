-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

/-!
# Test.Shape.Types

`Direction` / `Quarter` / `Layer` / `Shape` / `QuarterPos` の単体テスト。
-/

import S2IL.Shape

open S2IL

namespace Test.Shape.Types

-- ============================================================
-- Direction
-- ============================================================

section DirectionTest

-- 定数
#guard Direction.ne == (0 : Fin 4)
#guard Direction.se == (1 : Fin 4)
#guard Direction.sw == (2 : Fin 4)
#guard Direction.nw == (3 : Fin 4)
#guard Direction.all.length == 4

-- rotateCW: NE → SE → SW → NW → NE
#guard Direction.rotateCW Direction.ne == Direction.se
#guard Direction.rotateCW Direction.se == Direction.sw
#guard Direction.rotateCW Direction.sw == Direction.nw
#guard Direction.rotateCW Direction.nw == Direction.ne

-- 4 周性
example (d : Direction) :
    d.rotateCW.rotateCW.rotateCW.rotateCW = d := by
  unfold Direction.rotateCW
  ext
  simp [Fin.add_def]
  omega

-- 東西
#guard Direction.isEast Direction.ne
#guard Direction.isEast Direction.se
#guard !Direction.isEast Direction.sw
#guard !Direction.isEast Direction.nw
#guard !Direction.isWest Direction.ne
#guard Direction.isWest Direction.sw

-- 隣接（円環上 ±1）
#guard Direction.isAdjacent Direction.ne Direction.se
#guard Direction.isAdjacent Direction.se Direction.ne  -- 対称
#guard Direction.isAdjacent Direction.sw Direction.nw
#guard Direction.isAdjacent Direction.nw Direction.ne  -- 環の折返し
-- 反対側（NE↔SW, SE↔NW）は隣接でない
#guard !Direction.isAdjacent Direction.ne Direction.sw
#guard !Direction.isAdjacent Direction.se Direction.nw
-- 自分自身は隣接でない
#guard !Direction.isAdjacent Direction.ne Direction.ne

example (d1 d2 : Direction) :
    Direction.isAdjacent d1 d2 = Direction.isAdjacent d2 d1 :=
  Direction.isAdjacent_symm d1 d2

end DirectionTest

-- ============================================================
-- Quarter
-- ============================================================

section QuarterTest

-- isEmpty / isCrystal / canFormBond / isFragile
#guard Quarter.empty.isEmpty
#guard !Quarter.pin.isEmpty
#guard !(Quarter.crystal .red).isEmpty
#guard !(Quarter.colored .circle .red).isEmpty

#guard !Quarter.empty.canFormBond
#guard !Quarter.pin.canFormBond
#guard (Quarter.crystal .red).canFormBond
#guard (Quarter.colored .circle .red).canFormBond

#guard !Quarter.empty.isFragile
#guard !Quarter.pin.isFragile
#guard (Quarter.crystal .red).isFragile
#guard !(Quarter.colored .circle .red).isFragile

#guard !Quarter.empty.isCrystal
#guard !Quarter.pin.isCrystal
#guard (Quarter.crystal .red).isCrystal
#guard !(Quarter.colored .circle .red).isCrystal

-- partCode? / color?
#guard Quarter.empty.partCode? == none
#guard Quarter.pin.partCode? == some .pin
#guard (Quarter.crystal .red).partCode? == some .crystal
#guard (Quarter.colored .circle .red).partCode? == some .circle

#guard Quarter.empty.color? == none
#guard Quarter.pin.color? == none
#guard (Quarter.crystal .red).color? == some .red
#guard (Quarter.colored .star .blue).color? == some .blue

end QuarterTest

-- ============================================================
-- Layer
-- ============================================================

section LayerTest

private def crystalLayer : Layer :=
  Layer.mk (.crystal .red) (.crystal .green) (.crystal .blue) (.crystal .white)

private def mixedLayer : Layer :=
  Layer.mk (.colored .circle .red) (.colored .star .blue)
           (.colored .windmill .yellow) (.colored .rectangle .green)

-- mk の方角アクセス
#guard crystalLayer 0 == Quarter.crystal .red
#guard crystalLayer 1 == Quarter.crystal .green
#guard crystalLayer 2 == Quarter.crystal .blue
#guard crystalLayer 3 == Quarter.crystal .white

-- empty
#guard Layer.empty 0 == Quarter.empty
#guard Layer.empty 3 == Quarter.empty
#guard Layer.empty.isEmpty

-- isEmpty: 1 象限でも非空ならば false
#guard !crystalLayer.isEmpty
#guard !(Layer.mk .empty .empty .empty Quarter.pin).isEmpty

-- rotateCW: 値が方角 +1 ぶん前にずれる（index は -1 シフト）
example : crystalLayer.rotateCW 1 = crystalLayer 0 := rfl
example : crystalLayer.rotateCW 2 = crystalLayer 1 := rfl
example : crystalLayer.rotateCW 0 = crystalLayer 3 := rfl

-- 4 周性
example (l : Layer) : l.rotateCW.rotateCW.rotateCW.rotateCW = l := by
  funext d
  unfold Layer.rotateCW
  congr 1
  ext
  simp [Fin.sub_def, Fin.add_def]
  omega

-- getDir / setDir
#guard mixedLayer.getDir Direction.ne == Quarter.colored .circle .red

example : (mixedLayer.setDir .ne .empty).getDir .ne = .empty := by
  unfold Layer.getDir Layer.setDir; simp

example : (mixedLayer.setDir .ne .empty).getDir .se = mixedLayer.getDir .se := by
  unfold Layer.getDir Layer.setDir; decide

end LayerTest

-- ============================================================
-- Shape
-- ============================================================

section ShapeTest

private def L1 : Layer :=
  Layer.mk (.colored .circle .red) (.colored .circle .red)
           (.colored .circle .red) (.colored .circle .red)
private def L2 : Layer :=
  Layer.mk (.crystal .red) (.crystal .green) (.crystal .blue) (.crystal .white)
private def L_empty : Layer := Layer.empty

-- empty / single / double / triple / quadruple
#guard Shape.empty.layerCount == 0
#guard (Shape.single L1).layerCount == 1
#guard (Shape.double L1 L2).layerCount == 2
#guard (Shape.triple L1 L2 L1).layerCount == 3
#guard (Shape.quadruple L1 L2 L1 L2).layerCount == 4

-- bottomLayer / topLayer
#guard (Shape.empty).bottomLayer 0 == Quarter.empty
#guard (Shape.empty).topLayer 0 == Quarter.empty
#guard (Shape.single L1).bottomLayer 0 == L1 0
#guard (Shape.single L1).topLayer 0 == L1 0
#guard (Shape.double L1 L2).bottomLayer 0 == L1 0
#guard (Shape.double L1 L2).topLayer 0 == L2 0

-- mapLayers
example : (Shape.single L1).mapLayers (fun _ => Layer.empty) = Shape.single Layer.empty := rfl

-- IsNormalized: 末尾が空でなければ true
example : Shape.IsNormalized (Shape.single L1) := by decide
example : Shape.IsNormalized Shape.empty := by decide
example : ¬ Shape.IsNormalized (Shape.double L1 L_empty) := by decide

-- normalize: 末尾連続の空レイヤを除去
#guard (Shape.normalize (Shape.double L1 L_empty)).layerCount == 1
#guard (Shape.normalize (Shape.triple L1 L_empty L_empty)).layerCount == 1
-- 中間の空レイヤは保持
#guard (Shape.normalize (Shape.triple L1 L_empty L2)).layerCount == 3
-- 既に正規化済みなら恒等
example : Shape.normalize (Shape.single L1) = Shape.single L1 :=
  Shape.normalize_of_isNormalized _ (by decide)
-- 全レイヤが空の場合は 0 層
#guard (Shape.normalize (Shape.double L_empty L_empty)).layerCount == 0

end ShapeTest

-- ============================================================
-- QuarterPos
-- ============================================================

section QuarterPosTest

private def L : Layer :=
  Layer.mk (.colored .circle .red) (.colored .star .blue)
           (.colored .windmill .yellow) (.colored .rectangle .green)
private def s2 : Shape := Shape.double L Layer.empty

-- mk / layer / dir
example : QuarterPos.mk 3 Direction.ne = (3, Direction.ne) := rfl
#guard ((5 : Nat), Direction.sw).layer == 5
#guard ((5 : Nat), Direction.sw).dir == Direction.sw

-- isValid
#guard QuarterPos.isValid s2 (0, Direction.ne)
#guard QuarterPos.isValid s2 (1, Direction.nw)
#guard !QuarterPos.isValid s2 (2, Direction.ne)
#guard !QuarterPos.isValid Shape.empty (0, Direction.ne)

-- getQuarter: 範囲外は empty
#guard QuarterPos.getQuarter s2 (0, Direction.ne) == Quarter.colored .circle .red
#guard QuarterPos.getQuarter s2 (1, Direction.ne) == Quarter.empty
#guard QuarterPos.getQuarter s2 (99, Direction.ne) == Quarter.empty

-- setQuarter / getQuarter の関係
example : QuarterPos.getQuarter (QuarterPos.setQuarter s2 (0, .ne) .pin) (0, .ne) = .pin := by
  decide

example : QuarterPos.getQuarter (QuarterPos.setQuarter s2 (0, .ne) .pin) (0, .se)
        = QuarterPos.getQuarter s2 (0, .se) := by decide

-- 範囲外への setQuarter は無変化
example : QuarterPos.setQuarter s2 (99, .ne) .pin = s2 := by decide

-- rotateCW / rotateCCW: 方角のみ変化
#guard QuarterPos.rotateCW (3, Direction.ne) == ((3, Direction.se) : QuarterPos)
#guard QuarterPos.rotateCCW (3, Direction.ne) == ((3, Direction.nw) : QuarterPos)

-- allValid: 各レイヤ × 4 方角
#guard (QuarterPos.allValid Shape.empty).length == 0
#guard (QuarterPos.allValid (Shape.single L)).length == 4
#guard (QuarterPos.allValid s2).length == 8

end QuarterPosTest

end Test.Shape.Types
