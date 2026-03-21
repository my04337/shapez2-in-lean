-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- 回転操作のユニットテスト
import S2IL.Behavior.Rotate

-- ============================================================
-- テスト用データ
-- ============================================================

-- 全象限が同種の均一レイヤ
private def greenRect : Layer := Layer.mk
    (.colored .rectangle .green) (.colored .rectangle .green)
    (.colored .rectangle .green) (.colored .rectangle .green)

private def redCircle : Layer := Layer.mk
    (.colored .circle .red) (.colored .circle .red)
    (.colored .circle .red) (.colored .circle .red)

-- 全象限が空のレイヤ
private def emptyLayer : Layer := Layer.mk .empty .empty .empty .empty

-- 各象限が異なるレイヤ（回転の検出に最適）
private def mixedLayer : Layer := Layer.mk
    (.colored .circle .red) (.colored .star .blue)
    (.colored .windmill .yellow) (.colored .rectangle .green)

-- クリスタルレイヤ
private def crystalLayer : Layer := Layer.mk
    (.crystal .red) (.crystal .green) (.crystal .blue) (.crystal .white)

-- NE のみにパーツがあるレイヤ（用語集の例: `Cr------`）
private def neOnly : Layer := Layer.mk
    (.colored .circle .red) .empty .empty .empty

-- ピンレイヤ
private def pinLayer : Layer := Layer.mk .pin .pin .pin .pin

-- ============================================================
-- Layer.rotateCW: 時計回り 90° 回転
-- ============================================================

-- 用語集の例: Cr------ → --Cr---- (NE の内容が SE へ移動)
#guard neOnly.rotateCW == Layer.mk .empty (.colored .circle .red) .empty .empty
#guard neOnly.rotateCW.toString == "--Cr----"

-- 均一レイヤは回転しても同じ
#guard greenRect.rotateCW == greenRect
#guard redCircle.rotateCW == redCircle
#guard emptyLayer.rotateCW == emptyLayer

-- 混合レイヤ: NE→SE, SE→SW, SW→NW, NW→NE
-- 元: ne=Cr se=Sb sw=Wy nw=Rg
-- 後: ne=Rg se=Cr sw=Sb nw=Wy
#guard mixedLayer.rotateCW == Layer.mk
    (.colored .rectangle .green) (.colored .circle .red)
    (.colored .star .blue) (.colored .windmill .yellow)

-- クリスタルレイヤの回転
-- 元: ne=cr se=cg sw=cb nw=cw
-- 後: ne=cw se=cr sw=cg nw=cb
#guard crystalLayer.rotateCW == Layer.mk
    (.crystal .white) (.crystal .red) (.crystal .green) (.crystal .blue)

-- ピンレイヤは回転しても同じ
#guard pinLayer.rotateCW == pinLayer

-- toString 経由の検証
#guard mixedLayer.toString == "CrSbWyRg"
#guard mixedLayer.rotateCW.toString == "RgCrSbWy"

-- ============================================================
-- Layer.rotateCCW: 反時計回り 90° 回転
-- ============================================================

-- NE のみ → NW に移動
#guard neOnly.rotateCCW == Layer.mk .empty .empty .empty (.colored .circle .red)
#guard neOnly.rotateCCW.toString == "------Cr"

-- 混合レイヤ: NE→NW, SE→NE, SW→SE, NW→SW
-- 元: ne=Cr se=Sb sw=Wy nw=Rg
-- 後: ne=Sb se=Wy sw=Rg nw=Cr
#guard mixedLayer.rotateCCW == Layer.mk
    (.colored .star .blue) (.colored .windmill .yellow)
    (.colored .rectangle .green) (.colored .circle .red)

-- toString 経由の検証
#guard mixedLayer.rotateCCW.toString == "SbWyRgCr"

-- 均一レイヤは変わらない
#guard greenRect.rotateCCW == greenRect
#guard emptyLayer.rotateCCW == emptyLayer

-- ============================================================
-- Layer.rotate180: 180° 回転
-- ============================================================

-- NE のみ → SW に移動
#guard neOnly.rotate180 == Layer.mk .empty .empty (.colored .circle .red) .empty
#guard neOnly.rotate180.toString == "----Cr--"

-- 混合レイヤ: NE↔SW, SE↔NW
-- 元: ne=Cr se=Sb sw=Wy nw=Rg
-- 後: ne=Wy se=Rg sw=Cr nw=Sb
#guard mixedLayer.rotate180 == Layer.mk
    (.colored .windmill .yellow) (.colored .rectangle .green)
    (.colored .circle .red) (.colored .star .blue)

-- toString 経由の検証
#guard mixedLayer.rotate180.toString == "WyRgCrSb"

-- 均一レイヤは変わらない
#guard greenRect.rotate180 == greenRect
#guard emptyLayer.rotate180 == emptyLayer

-- ============================================================
-- Layer: 恒等性・逆元のテスト
-- ============================================================

-- 4 回 CW 回転 = 恒等
#guard mixedLayer.rotateCW.rotateCW.rotateCW.rotateCW == mixedLayer
#guard crystalLayer.rotateCW.rotateCW.rotateCW.rotateCW == crystalLayer

-- CW ∘ CCW = 恒等
#guard mixedLayer.rotateCW.rotateCCW == mixedLayer
#guard mixedLayer.rotateCCW.rotateCW == mixedLayer

-- 180° × 2 = 恒等
#guard mixedLayer.rotate180.rotate180 == mixedLayer

-- CW × 2 = 180°
#guard mixedLayer.rotateCW.rotateCW == mixedLayer.rotate180

-- CW × 3 = CCW
#guard mixedLayer.rotateCW.rotateCW.rotateCW == mixedLayer.rotateCCW

-- 4 回 CCW 回転 = 恒等
#guard mixedLayer.rotateCCW.rotateCCW.rotateCCW.rotateCCW == mixedLayer

-- CW と 180° の可換性
#guard mixedLayer.rotateCW.rotate180 == mixedLayer.rotate180.rotateCW
#guard mixedLayer.rotateCCW.rotate180 == mixedLayer.rotate180.rotateCCW

-- 空性の保存
#guard emptyLayer.rotateCW.isEmpty == true
#guard emptyLayer.rotateCCW.isEmpty == true
#guard emptyLayer.rotate180.isEmpty == true
#guard mixedLayer.rotateCW.isEmpty == false

-- ============================================================
-- Shape.rotateCW: シェイプの時計回り 90° 回転
-- ============================================================

-- 1 レイヤシェイプ
#guard (Shape.single mixedLayer).rotateCW ==
    Shape.single mixedLayer.rotateCW
#guard (Shape.single mixedLayer).rotateCW.toString == "RgCrSbWy"

-- 2 レイヤシェイプ
#guard (Shape.double greenRect mixedLayer).rotateCW ==
    Shape.double greenRect.rotateCW mixedLayer.rotateCW
#guard (Shape.double greenRect mixedLayer).rotateCW.toString == "RgRgRgRg:RgCrSbWy"

-- 3 レイヤシェイプ
#guard (Shape.triple greenRect redCircle mixedLayer).rotateCW.toString
    == "RgRgRgRg:CrCrCrCr:RgCrSbWy"

-- 4 レイヤシェイプ
#guard (Shape.quadruple greenRect redCircle mixedLayer crystalLayer).rotateCW.toString
    == "RgRgRgRg:CrCrCrCr:RgCrSbWy:cwcrcgcb"

-- 用語集の例（シェイプレベル）
#guard (Shape.single neOnly).rotateCW.toString == "--Cr----"

-- ============================================================
-- Shape.rotateCCW: シェイプの反時計回り 90° 回転
-- ============================================================

#guard (Shape.single mixedLayer).rotateCCW.toString == "SbWyRgCr"
#guard (Shape.double greenRect mixedLayer).rotateCCW.toString == "RgRgRgRg:SbWyRgCr"

-- ============================================================
-- Shape.rotate180: シェイプの 180° 回転
-- ============================================================

#guard (Shape.single mixedLayer).rotate180.toString == "WyRgCrSb"
#guard (Shape.double greenRect mixedLayer).rotate180.toString == "RgRgRgRg:WyRgCrSb"

-- ============================================================
-- Shape: 恒等性・逆元のテスト
-- ============================================================

-- 4 回 CW = 恒等
#guard (Shape.single mixedLayer).rotateCW.rotateCW.rotateCW.rotateCW
    == Shape.single mixedLayer
#guard (Shape.double greenRect mixedLayer).rotateCW.rotateCW.rotateCW.rotateCW
    == Shape.double greenRect mixedLayer
#guard (Shape.quadruple greenRect redCircle mixedLayer crystalLayer).rotateCW.rotateCW.rotateCW.rotateCW == Shape.quadruple greenRect redCircle mixedLayer crystalLayer

-- CW ∘ CCW = 恒等
#guard (Shape.single mixedLayer).rotateCW.rotateCCW == Shape.single mixedLayer
#guard (Shape.single mixedLayer).rotateCCW.rotateCW == Shape.single mixedLayer

-- 180° × 2 = 恒等
#guard (Shape.single mixedLayer).rotate180.rotate180 == Shape.single mixedLayer
#guard (Shape.double greenRect mixedLayer).rotate180.rotate180
    == Shape.double greenRect mixedLayer

-- レイヤ数の保存
#guard (Shape.single mixedLayer).rotateCW.layerCount == 1
#guard (Shape.double greenRect mixedLayer).rotateCW.layerCount == 2
#guard (Shape.triple greenRect redCircle mixedLayer).rotateCW.layerCount == 3
#guard (Shape.quadruple greenRect redCircle mixedLayer crystalLayer).rotateCW.layerCount == 4

#guard (Shape.single mixedLayer).rotateCCW.layerCount == 1
#guard (Shape.double greenRect mixedLayer).rotate180.layerCount == 2

-- CW と 180° の可換性
#guard (Shape.single mixedLayer).rotateCW.rotate180
    == (Shape.single mixedLayer).rotate180.rotateCW
#guard (Shape.double greenRect mixedLayer).rotateCCW.rotate180
    == (Shape.double greenRect mixedLayer).rotate180.rotateCCW

-- 4 回 CCW = 恒等
#guard (Shape.single mixedLayer).rotateCCW.rotateCCW.rotateCCW.rotateCCW
    == Shape.single mixedLayer
