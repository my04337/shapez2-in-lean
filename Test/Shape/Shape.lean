-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- Shape のユニットテスト
import S2IL.Shape

-- 便利なレイヤ定義（テスト用）
private def greenRect : Layer := Layer.mk
    (.colored .rectangle .green) (.colored .rectangle .green)
    (.colored .rectangle .green) (.colored .rectangle .green)

private def redCircle : Layer := Layer.mk
    (.colored .circle .red) (.colored .circle .red)
    (.colored .circle .red) (.colored .circle .red)

private def emptyLayer : Layer := Layer.mk .empty .empty .empty .empty

private def mixedLayer : Layer := Layer.mk
    (.colored .circle .red) (.colored .star .blue)
    (.colored .windmill .yellow) (.colored .rectangle .green)

-- ============================================================
-- layerCount
-- ============================================================

#guard (Shape.single greenRect).layerCount == 1
#guard (Shape.double greenRect redCircle).layerCount == 2
#guard (Shape.triple greenRect redCircle mixedLayer).layerCount == 3
#guard (Shape.quadruple greenRect redCircle mixedLayer emptyLayer).layerCount == 4

-- ============================================================
-- layers
-- ============================================================

#guard (Shape.single greenRect).layers == [greenRect]
#guard (Shape.double greenRect redCircle).layers == [greenRect, redCircle]
#guard (Shape.triple greenRect redCircle mixedLayer).layers
    == [greenRect, redCircle, mixedLayer]
#guard (Shape.quadruple greenRect redCircle mixedLayer emptyLayer).layers
    == [greenRect, redCircle, mixedLayer, emptyLayer]

-- ============================================================
-- bottomLayer / topLayer
-- ============================================================

-- single: bottom == top
#guard (Shape.single greenRect).bottomLayer == greenRect
#guard (Shape.single greenRect).topLayer == greenRect

-- double
#guard (Shape.double greenRect redCircle).bottomLayer == greenRect
#guard (Shape.double greenRect redCircle).topLayer == redCircle

-- triple
#guard (Shape.triple greenRect redCircle mixedLayer).bottomLayer == greenRect
#guard (Shape.triple greenRect redCircle mixedLayer).topLayer == mixedLayer

-- quadruple
#guard (Shape.quadruple greenRect redCircle mixedLayer emptyLayer).bottomLayer == greenRect
#guard (Shape.quadruple greenRect redCircle mixedLayer emptyLayer).topLayer == emptyLayer

-- ============================================================
-- toNotation
-- ============================================================

-- 1 レイヤ
#guard (Shape.single greenRect).toNotation == "RgRgRgRg"

-- 2 レイヤ （`:` 区切り）
#guard (Shape.double greenRect redCircle).toNotation == "RgRgRgRg:CrCrCrCr"

-- 3 レイヤ
#guard (Shape.triple greenRect redCircle mixedLayer).toNotation
    == "RgRgRgRg:CrCrCrCr:CrSbWyRg"

-- 4 レイヤ
#guard (Shape.quadruple greenRect redCircle mixedLayer emptyLayer).toNotation
    == "RgRgRgRg:CrCrCrCr:CrSbWyRg:--------"

-- ============================================================
-- DecidableEq / BEq
-- ============================================================

-- 同値性
#guard Shape.single greenRect == Shape.single greenRect
#guard Shape.double greenRect redCircle == Shape.double greenRect redCircle

-- 非同値性
#guard Shape.single greenRect != Shape.single redCircle
#guard Shape.single greenRect != Shape.double greenRect redCircle
