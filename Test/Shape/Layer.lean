-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- Layer のユニットテスト
import S2IL.Shape.Layer

-- toNotation: 全象限が同じパーツ・色のレイヤ
#guard (Layer.mk (.colored .rectangle .green) (.colored .rectangle .green)
                 (.colored .rectangle .green) (.colored .rectangle .green)).toNotation
    == "RgRgRgRg"

-- toNotation: 各象限が異なるレイヤ
#guard (Layer.mk (.colored .circle .red) (.colored .star .blue)
                 (.colored .windmill .yellow) (.colored .rectangle .green)).toNotation
    == "CrSbWyRg"

-- toNotation: 空の象限を含むレイヤ
#guard (Layer.mk (.colored .circle .red) .empty .empty (.colored .circle .red)).toNotation
    == "Cr----Cr"

-- toNotation: ピンを含むレイヤ
#guard (Layer.mk .pin .pin .pin .pin).toNotation == "P-P-P-P-"

-- toNotation: 全て空のレイヤ
#guard (Layer.mk .empty .empty .empty .empty).toNotation == "--------"

-- fromNotation?: 有効な入力
#guard Layer.fromNotation? "RgRgRgRg" == some (Layer.mk
    (.colored .rectangle .green) (.colored .rectangle .green)
    (.colored .rectangle .green) (.colored .rectangle .green))

#guard Layer.fromNotation? "CrSbWyRg" == some (Layer.mk
    (.colored .circle .red) (.colored .star .blue)
    (.colored .windmill .yellow) (.colored .rectangle .green))

#guard Layer.fromNotation? "Cr----Cr" == some (Layer.mk
    (.colored .circle .red) .empty .empty (.colored .circle .red))

#guard Layer.fromNotation? "P-P-P-P-" == some (Layer.mk .pin .pin .pin .pin)

#guard Layer.fromNotation? "--------" == some (Layer.mk .empty .empty .empty .empty)

-- fromNotation?: クリスタルを含むレイヤ
#guard Layer.fromNotation? "CuCuCuCu" == some (Layer.mk
    (.colored .circle .uncolored) (.colored .circle .uncolored)
    (.colored .circle .uncolored) (.colored .circle .uncolored))

-- fromNotation?: 無効な入力（文字数不足）
#guard Layer.fromNotation? "" == none
#guard Layer.fromNotation? "Cr" == none
#guard Layer.fromNotation? "CrCr" == none
#guard Layer.fromNotation? "CrCrCr" == none

-- fromNotation?: 無効な入力（文字数過多）
#guard Layer.fromNotation? "CrCrCrCrCr" == none

-- fromNotation?: 無効な入力（不正な文字）
#guard Layer.fromNotation? "XXXXXXXX" == none
#guard Layer.fromNotation? "C-C-C-C-" == none  -- カラーコードなし
#guard Layer.fromNotation? "PrPrPrPr" == none  -- ピンに色コードは無効

-- ラウンドトリップ: fromNotation? (toNotation l) == some l
#guard Layer.fromNotation? (Layer.mk .empty .empty .empty .empty).toNotation
    == some (Layer.mk .empty .empty .empty .empty)
#guard Layer.fromNotation? (Layer.mk .pin .pin .pin .pin).toNotation
    == some (Layer.mk .pin .pin .pin .pin)
#guard Layer.fromNotation? (Layer.mk (.colored .circle .red) (.colored .star .blue)
                                      (.colored .windmill .yellow) (.colored .rectangle .green)).toNotation
    == some (Layer.mk (.colored .circle .red) (.colored .star .blue)
                      (.colored .windmill .yellow) (.colored .rectangle .green))

-- isEmpty
#guard (Layer.mk .empty .empty .empty .empty).isEmpty == true
#guard (Layer.mk (.colored .circle .red) .empty .empty .empty).isEmpty == false
#guard (Layer.mk .empty .empty .empty .pin).isEmpty == false
#guard (Layer.mk .pin .pin .pin .pin).isEmpty == false

-- DecidableEq: 同値性と非同値性
#guard Layer.mk .empty .empty .empty .empty == Layer.mk .empty .empty .empty .empty
#guard Layer.mk .pin .pin .pin .pin == Layer.mk .pin .pin .pin .pin
#guard Layer.mk (.colored .circle .red) .empty .empty .empty
    != Layer.mk .empty .empty .empty .empty
#guard Layer.mk (.colored .circle .red) .empty .empty .empty
    != Layer.mk (.colored .circle .blue) .empty .empty .empty
