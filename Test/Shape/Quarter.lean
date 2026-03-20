-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- Quarter のユニットテスト
import S2IL.Shape.Quarter

-- toNotation: 各コンストラクタが正しい記法を返すこと
#guard Quarter.empty.toNotation == "--"
#guard Quarter.pin.toNotation == "P-"
#guard (Quarter.colored .circle .red).toNotation == "Cr"
#guard (Quarter.colored .rectangle .green).toNotation == "Rg"
#guard (Quarter.colored .star .blue).toNotation == "Sb"
#guard (Quarter.colored .windmill .yellow).toNotation == "Wy"
#guard (Quarter.colored .circle .uncolored).toNotation == "Cu"
#guard (Quarter.colored .rectangle .white).toNotation == "Rw"

-- fromNotation?: 有効な入力が正しいコンストラクタを返すこと
#guard Quarter.fromNotation? "--" == some Quarter.empty
#guard Quarter.fromNotation? "P-" == some Quarter.pin
#guard Quarter.fromNotation? "Cr" == some (Quarter.colored .circle .red)
#guard Quarter.fromNotation? "Rg" == some (Quarter.colored .rectangle .green)
#guard Quarter.fromNotation? "Sb" == some (Quarter.colored .star .blue)
#guard Quarter.fromNotation? "Wy" == some (Quarter.colored .windmill .yellow)
#guard Quarter.fromNotation? "Cu" == some (Quarter.colored .circle .uncolored)

-- fromNotation?: 無効な入力は none を返すこと
#guard Quarter.fromNotation? "" == none
#guard Quarter.fromNotation? "  " == none
#guard Quarter.fromNotation? "C" == none
#guard Quarter.fromNotation? "CCC" == none
#guard Quarter.fromNotation? "XX" == none
#guard Quarter.fromNotation? "C-" == none
#guard Quarter.fromNotation? "c-" == none
#guard Quarter.fromNotation? "-C" == none
#guard Quarter.fromNotation? "-c" == none
-- ピンと結晶は colored にならないため none
#guard Quarter.fromNotation? "Pr" == none
#guard Quarter.fromNotation? "cr" == none
#guard Quarter.fromNotation? "Pg" == none
#guard Quarter.fromNotation? "cu" == none

-- ラウンドトリップ: fromNotation? (toNotation q) == some q
#guard Quarter.fromNotation? (Quarter.empty.toNotation) == some Quarter.empty
#guard Quarter.fromNotation? (Quarter.pin.toNotation) == some Quarter.pin
#guard Quarter.fromNotation? ((Quarter.colored .circle .red).toNotation) == some (Quarter.colored .circle .red)
#guard Quarter.fromNotation? ((Quarter.colored .windmill .uncolored).toNotation) == some (Quarter.colored .windmill .uncolored)

-- isEmpty
#guard Quarter.empty.isEmpty == true
#guard Quarter.pin.isEmpty == false
#guard (Quarter.colored .circle .red).isEmpty == false

-- partCode?: PartCode に変換されること（ピンは PartCode.pin を返す）
#guard Quarter.empty.partCode? == none
#guard Quarter.pin.partCode? == some PartCode.pin
#guard (Quarter.colored .circle .red).partCode? == some PartCode.circle
#guard (Quarter.colored .star .blue).partCode? == some PartCode.star
#guard (Quarter.colored .windmill .cyan).partCode? == some PartCode.windmill
#guard (Quarter.colored .rectangle .green).partCode? == some PartCode.rectangle

-- color?
#guard Quarter.empty.color? == none
#guard Quarter.pin.color? == none
#guard (Quarter.colored .circle .red).color? == some Color.red
#guard (Quarter.colored .rectangle .uncolored).color? == some Color.uncolored

-- DecidableEq: 同値性と非同値性
#guard Quarter.empty == Quarter.empty
#guard Quarter.pin == Quarter.pin
#guard Quarter.colored .circle .red == Quarter.colored .circle .red
#guard Quarter.empty != Quarter.pin
#guard Quarter.pin != Quarter.colored .circle .red
#guard Quarter.colored .circle .red != Quarter.colored .circle .blue
#guard Quarter.colored .circle .red != Quarter.colored .star .red
