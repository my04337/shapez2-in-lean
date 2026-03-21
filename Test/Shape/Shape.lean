-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- Shape のユニットテスト
import S2IL.Shape.Shape

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
