-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- Shape のユニットテスト
import S2IL.Shape.GameConfig

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

private def crystalLayer : Layer := Layer.mk
    (.crystal .red) (.crystal .green) (.crystal .blue) (.crystal .white)

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
-- toString
-- ============================================================

-- 1 レイヤ
#guard (Shape.single greenRect).toString == "RgRgRgRg"

-- 2 レイヤ （`:` 区切り）
#guard (Shape.double greenRect redCircle).toString == "RgRgRgRg:CrCrCrCr"

-- 3 レイヤ
#guard (Shape.triple greenRect redCircle mixedLayer).toString
    == "RgRgRgRg:CrCrCrCr:CrSbWyRg"

-- 4 レイヤ
#guard (Shape.quadruple greenRect redCircle mixedLayer emptyLayer).toString
    == "RgRgRgRg:CrCrCrCr:CrSbWyRg:--------"

-- クリスタルを含むシェイプ
#guard (Shape.single crystalLayer).toString == "crcgcbcw"
#guard (Shape.double greenRect crystalLayer).toString == "RgRgRgRg:crcgcbcw"

-- ============================================================
-- ofString?
-- ============================================================

-- 有効な入力: 1 レイヤ
#guard Shape.ofString? "RgRgRgRg" == some (Shape.single greenRect)

-- 有効な入力: 2 レイヤ
#guard Shape.ofString? "RgRgRgRg:CrCrCrCr" == some (Shape.double greenRect redCircle)

-- 有効な入力: 3 レイヤ
#guard Shape.ofString? "RgRgRgRg:CrCrCrCr:CrSbWyRg"
    == some (Shape.triple greenRect redCircle mixedLayer)

-- 有効な入力: 中間に空レイヤを含む 3 レイヤ
#guard Shape.ofString? "CrCrCrCr:--------:CrSbWyRg"
    == some (Shape.triple redCircle emptyLayer mixedLayer)

-- 有効な入力: 4 レイヤ
#guard Shape.ofString? "RgRgRgRg:CrCrCrCr:CrSbWyRg:crcgcbcw"
    == some (Shape.quadruple greenRect redCircle mixedLayer crystalLayer)

-- クリスタルを含むシェイプ
#guard Shape.ofString? "crcgcbcw" == some (Shape.single crystalLayer)

-- 末尾空レイヤの正規化: 末尾の空レイヤはストリップされる
#guard Shape.ofString? "CrCrCrCr:--------" == some (Shape.single redCircle)
#guard Shape.ofString? "RgRgRgRg:CrCrCrCr:CrSbWyRg:--------"
    == some (Shape.triple greenRect redCircle mixedLayer)
#guard Shape.ofString? "RgRgRgRg:--------:--------"
    == some (Shape.single greenRect)
#guard Shape.ofString? "RgRgRgRg:--------:--------:--------"
    == some (Shape.single greenRect)
#guard Shape.ofString? "CrCrCrCr:--------:CrSbWyRg:--------"
    == some (Shape.triple redCircle emptyLayer mixedLayer)

-- 無効な入力: 空文字列
#guard Shape.ofString? "" == none

-- 無効な入力: 全レイヤが空（シェイプとして無効）
#guard Shape.ofString? "--------" == none
#guard Shape.ofString? "--------:--------" == none
#guard Shape.ofString? "--------:--------:--------" == none
#guard Shape.ofString? "--------:--------:--------:--------" == none

-- 無効な入力: 5 セグメント以上（全レイヤ空は無効）
#guard Shape.ofString? "--------:--------:--------:--------:--------" == none

-- 有効な入力: 5 レイヤ（レイヤ数制限なし）
#guard Shape.ofString? "CrCrCrCr:CrCrCrCr:CrCrCrCr:CrCrCrCr:CrCrCrCr"
    == some ⟨[redCircle, redCircle, redCircle, redCircle, redCircle], by simp⟩
#guard (⟨[redCircle, redCircle, redCircle, redCircle, redCircle], by simp⟩ : Shape).layerCount == 5

-- 無効な入力: 不正なレイヤ記法
#guard Shape.ofString? "XXXX" == none
#guard Shape.ofString? "invalid" == none

-- ============================================================
-- ラウンドトリップ: 正規化済みシェイプに対して ofString? (toString s) == some s
-- ============================================================

#guard Shape.ofString? (Shape.single greenRect).toString
    == some (Shape.single greenRect)
#guard Shape.ofString? (Shape.double greenRect redCircle).toString
    == some (Shape.double greenRect redCircle)
#guard Shape.ofString? (Shape.triple greenRect redCircle mixedLayer).toString
    == some (Shape.triple greenRect redCircle mixedLayer)
#guard Shape.ofString? (Shape.quadruple greenRect redCircle mixedLayer crystalLayer).toString
    == some (Shape.quadruple greenRect redCircle mixedLayer crystalLayer)
#guard Shape.ofString? (Shape.single crystalLayer).toString
    == some (Shape.single crystalLayer)
#guard Shape.ofString? (Shape.single (Layer.mk .pin .pin .pin .pin)).toString
    == some (Shape.single (Layer.mk .pin .pin .pin .pin))

-- 非正規化シェイプの toString → ofString? は正規化された結果を返す
#guard Shape.ofString? (Shape.quadruple greenRect redCircle mixedLayer emptyLayer).toString
    == some (Shape.triple greenRect redCircle mixedLayer)
#guard Shape.ofString? (Shape.double greenRect emptyLayer).toString
    == some (Shape.single greenRect)
#guard Shape.ofString? (Shape.single emptyLayer).toString
    == none

-- ============================================================
-- DecidableEq / BEq
-- ============================================================

-- 同値性
#guard Shape.single greenRect == Shape.single greenRect
#guard Shape.double greenRect redCircle == Shape.double greenRect redCircle

-- 非同値性
#guard Shape.single greenRect != Shape.single redCircle
#guard Shape.single greenRect != Shape.double greenRect redCircle

-- ============================================================
-- GameConfig プリセット
-- ============================================================

-- vanilla4 (Normal/Hard)
#guard GameConfig.vanilla4.maxLayers == 4

-- vanilla5 (Insane)
#guard GameConfig.vanilla5.maxLayers == 5

-- stress16 プリセット
#guard GameConfig.stress16.maxLayers == 16

-- ============================================================
-- truncate: 基本テスト (vanilla4)
-- ============================================================

-- レイヤ数が上限以下 → そのまま
#guard (Shape.single greenRect).truncate GameConfig.vanilla4
    == Shape.single greenRect
#guard (Shape.double greenRect redCircle).truncate GameConfig.vanilla4
    == Shape.double greenRect redCircle
#guard (Shape.quadruple greenRect redCircle mixedLayer crystalLayer).truncate GameConfig.vanilla4
    == Shape.quadruple greenRect redCircle mixedLayer crystalLayer

-- 5レイヤ → 4レイヤに切り詰め
private def fiveLayers : Shape :=
    ⟨[greenRect, redCircle, mixedLayer, crystalLayer, greenRect], by simp⟩
#guard (fiveLayers.truncate GameConfig.vanilla4).layerCount == 4

-- truncate は冪等
#guard (fiveLayers.truncate GameConfig.vanilla4).truncate GameConfig.vanilla4
    == fiveLayers.truncate GameConfig.vanilla4

-- ============================================================
-- truncate: vanilla5
-- ============================================================

-- 5レイヤ → vanilla5 では切り詰め不要
#guard (fiveLayers.truncate GameConfig.vanilla5) == fiveLayers
#guard (fiveLayers.truncate GameConfig.vanilla5).layerCount == 5

-- ============================================================
-- truncate: 16レイヤ (stress16) — 層当たり不可能な規模
-- ============================================================

-- 16レイヤのシェイプを構築
private def layer0  : Layer := Layer.mk (.colored .circle .red) (.colored .circle .green) (.colored .circle .blue) (.colored .circle .white)
private def layer1  : Layer := Layer.mk (.colored .rectangle .red) (.colored .rectangle .green) (.colored .rectangle .blue) (.colored .rectangle .white)
private def layer2  : Layer := Layer.mk (.colored .star .red) (.colored .star .green) (.colored .star .blue) (.colored .star .white)
private def layer3  : Layer := Layer.mk (.colored .windmill .red) (.colored .windmill .green) (.colored .windmill .blue) (.colored .windmill .white)
private def layer4  : Layer := Layer.mk (.crystal .red) (.crystal .green) (.crystal .blue) (.crystal .white)
private def layer5  : Layer := Layer.mk .pin .pin .pin .pin
private def layer6  : Layer := Layer.mk (.colored .circle .yellow) (.colored .rectangle .yellow) (.colored .star .yellow) (.colored .windmill .yellow)
private def layer7  : Layer := Layer.mk (.colored .circle .cyan) (.colored .rectangle .cyan) (.colored .star .cyan) (.colored .windmill .cyan)
private def layer8  : Layer := Layer.mk (.colored .circle .magenta) (.colored .rectangle .magenta) (.colored .star .magenta) (.colored .windmill .magenta)
private def layer9  : Layer := Layer.mk (.colored .circle .uncolored) (.colored .rectangle .uncolored) (.colored .star .uncolored) (.colored .windmill .uncolored)
private def layer10 : Layer := Layer.mk (.crystal .yellow) (.crystal .cyan) (.crystal .magenta) (.crystal .white)
private def layer11 : Layer := Layer.mk .pin (.colored .circle .red) .empty .pin
private def layer12 : Layer := Layer.mk (.colored .rectangle .green) .empty (.crystal .blue) .pin
private def layer13 : Layer := Layer.mk .empty (.colored .star .white) .pin (.crystal .red)
private def layer14 : Layer := Layer.mk (.colored .windmill .blue) (.crystal .green) (.colored .circle .yellow) .empty
private def layer15 : Layer := Layer.mk (.colored .circle .red) (.colored .circle .red) (.colored .circle .red) (.colored .circle .red)

private def shape16 : Shape :=
    ⟨[layer0, layer1, layer2, layer3, layer4, layer5, layer6, layer7,
      layer8, layer9, layer10, layer11, layer12, layer13, layer14, layer15], by simp⟩

-- 16レイヤの基本性質
#guard shape16.layerCount == 16
#guard shape16.bottomLayer == layer0
#guard shape16.topLayer == layer15

-- ラウンドトリップ: toString → ofString?
#guard Shape.ofString? shape16.toString == some shape16

-- stress16 での truncate はノーオプ
#guard (shape16.truncate GameConfig.stress16) == shape16
#guard (shape16.truncate GameConfig.stress16).layerCount == 16

-- vanilla4 で切り詰め → 4レイヤ
#guard (shape16.truncate GameConfig.vanilla4).layerCount == 4
#guard (shape16.truncate GameConfig.vanilla4).bottomLayer == layer0
#guard (shape16.truncate GameConfig.vanilla4).topLayer == layer3

-- vanilla5 で切り詰め → 5レイヤ
#guard (shape16.truncate GameConfig.vanilla5).layerCount == 5

-- truncate 冪等性 (16層 → 4層 → 4層)
#guard (shape16.truncate GameConfig.vanilla4).truncate GameConfig.vanilla4
    == shape16.truncate GameConfig.vanilla4

-- truncate 冪等性 (16層 → stress16 → stress16)
#guard (shape16.truncate GameConfig.stress16).truncate GameConfig.stress16
    == shape16.truncate GameConfig.stress16

-- truncate の異なる config での合成: min(4, 16) = 4
#guard (shape16.truncate GameConfig.stress16).truncate GameConfig.vanilla4
    == shape16.truncate GameConfig.vanilla4

-- truncate の異なる config での合成: min(16, 4) = 4
#guard (shape16.truncate GameConfig.vanilla4).truncate GameConfig.stress16
    == shape16.truncate GameConfig.vanilla4
