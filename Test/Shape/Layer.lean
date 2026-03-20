-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- Layer のユニットテスト
import S2IL.Shape.Layer

-- toString: 全象限が同じパーツ・色のレイヤ
#guard (Layer.mk (.colored .rectangle .green) (.colored .rectangle .green)
                 (.colored .rectangle .green) (.colored .rectangle .green)).toString
    == "RgRgRgRg"

-- toString: 各象限が異なるレイヤ
#guard (Layer.mk (.colored .circle .red) (.colored .star .blue)
                 (.colored .windmill .yellow) (.colored .rectangle .green)).toString
    == "CrSbWyRg"

-- toString: 空の象限を含むレイヤ
#guard (Layer.mk (.colored .circle .red) .empty .empty (.colored .circle .red)).toString
    == "Cr----Cr"

-- toString: ピンを含むレイヤ
#guard (Layer.mk .pin .pin .pin .pin).toString == "P-P-P-P-"

-- toString: 全て空のレイヤ
#guard (Layer.mk .empty .empty .empty .empty).toString == "--------"

-- toString: クリスタルを含むレイヤ
#guard (Layer.mk (.crystal .red) (.crystal .green) (.crystal .blue) (.crystal .white)).toString
    == "crcgcbcw"

-- ofString?: 有効な入力
#guard Layer.ofString? "RgRgRgRg" == some (Layer.mk
    (.colored .rectangle .green) (.colored .rectangle .green)
    (.colored .rectangle .green) (.colored .rectangle .green))

#guard Layer.ofString? "CrSbWyRg" == some (Layer.mk
    (.colored .circle .red) (.colored .star .blue)
    (.colored .windmill .yellow) (.colored .rectangle .green))

#guard Layer.ofString? "Cr----Cr" == some (Layer.mk
    (.colored .circle .red) .empty .empty (.colored .circle .red))

#guard Layer.ofString? "P-P-P-P-" == some (Layer.mk .pin .pin .pin .pin)

#guard Layer.ofString? "--------" == some (Layer.mk .empty .empty .empty .empty)

-- ofString?: クリスタルを含むレイヤ
#guard Layer.ofString? "crcgcbcw" == some (Layer.mk
    (.crystal .red) (.crystal .green) (.crystal .blue) (.crystal .white))

#guard Layer.ofString? "CuCuCuCu" == some (Layer.mk
    (.colored .circle .uncolored) (.colored .circle .uncolored)
    (.colored .circle .uncolored) (.colored .circle .uncolored))

-- ofString?: 無効な入力（文字数不足）
#guard Layer.ofString? "" == none
#guard Layer.ofString? "Cr" == none
#guard Layer.ofString? "CrCr" == none
#guard Layer.ofString? "CrCrCr" == none

-- ofString?: 無効な入力（文字数過多）
#guard Layer.ofString? "CrCrCrCrCr" == none

-- ofString?: 無効な入力（不正な文字）
#guard Layer.ofString? "XXXXXXXX" == none
#guard Layer.ofString? "C-C-C-C-" == none  -- カラーコードなし
#guard Layer.ofString? "PrPrPrPr" == none  -- ピンに色コードは無効

-- ラウンドトリップ: ofString? (toString l) == some l
#guard Layer.ofString? (Layer.mk .empty .empty .empty .empty).toString
    == some (Layer.mk .empty .empty .empty .empty)
#guard Layer.ofString? (Layer.mk .pin .pin .pin .pin).toString
    == some (Layer.mk .pin .pin .pin .pin)
#guard Layer.ofString? (Layer.mk (.colored .circle .red) (.colored .star .blue)
                                  (.colored .windmill .yellow) (.colored .rectangle .green)).toString
    == some (Layer.mk (.colored .circle .red) (.colored .star .blue)
                      (.colored .windmill .yellow) (.colored .rectangle .green))
#guard Layer.ofString? (Layer.mk (.crystal .red) (.crystal .green)
                                  (.crystal .blue) (.crystal .white)).toString
    == some (Layer.mk (.crystal .red) (.crystal .green)
                      (.crystal .blue) (.crystal .white))

-- isEmpty
#guard (Layer.mk .empty .empty .empty .empty).isEmpty == true
#guard (Layer.mk (.colored .circle .red) .empty .empty .empty).isEmpty == false
#guard (Layer.mk .empty .empty .empty .pin).isEmpty == false
#guard (Layer.mk .pin .pin .pin .pin).isEmpty == false
#guard (Layer.mk (.crystal .red) .empty .empty .empty).isEmpty == false

-- DecidableEq: 同値性と非同値性
#guard Layer.mk .empty .empty .empty .empty == Layer.mk .empty .empty .empty .empty
#guard Layer.mk .pin .pin .pin .pin == Layer.mk .pin .pin .pin .pin
#guard Layer.mk (.colored .circle .red) .empty .empty .empty
    != Layer.mk .empty .empty .empty .empty
#guard Layer.mk (.colored .circle .red) .empty .empty .empty
    != Layer.mk (.colored .circle .blue) .empty .empty .empty
#guard Layer.mk (.crystal .red) .empty .empty .empty
    != Layer.mk (.crystal .blue) .empty .empty .empty
