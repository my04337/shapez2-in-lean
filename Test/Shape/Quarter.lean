-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- Quarter のユニットテスト
import S2IL.Shape.Quarter

-- toString: 各コンストラクタが正しい文字列を返すこと
#guard Quarter.empty.toString == "--"
#guard Quarter.pin.toString == "P-"
#guard (Quarter.colored .circle .red).toString == "Cr"
#guard (Quarter.colored .rectangle .green).toString == "Rg"
#guard (Quarter.colored .star .blue).toString == "Sb"
#guard (Quarter.colored .windmill .yellow).toString == "Wy"
#guard (Quarter.colored .circle .uncolored).toString == "Cu"
#guard (Quarter.colored .rectangle .white).toString == "Rw"
#guard (Quarter.crystal .red).toString == "cr"
#guard (Quarter.crystal .green).toString == "cg"
#guard (Quarter.crystal .blue).toString == "cb"
#guard (Quarter.crystal .uncolored).toString == "cu"
#guard (Quarter.crystal .cyan).toString == "cc"

-- ofString?: 有効な入力が正しいコンストラクタを返すこと
#guard Quarter.ofString? "--" == some Quarter.empty
#guard Quarter.ofString? "P-" == some Quarter.pin
#guard Quarter.ofString? "Cr" == some (Quarter.colored .circle .red)
#guard Quarter.ofString? "Rg" == some (Quarter.colored .rectangle .green)
#guard Quarter.ofString? "Sb" == some (Quarter.colored .star .blue)
#guard Quarter.ofString? "Wy" == some (Quarter.colored .windmill .yellow)
#guard Quarter.ofString? "Cu" == some (Quarter.colored .circle .uncolored)
#guard Quarter.ofString? "cr" == some (Quarter.crystal .red)
#guard Quarter.ofString? "cg" == some (Quarter.crystal .green)
#guard Quarter.ofString? "cb" == some (Quarter.crystal .blue)
#guard Quarter.ofString? "cu" == some (Quarter.crystal .uncolored)
#guard Quarter.ofString? "cc" == some (Quarter.crystal .cyan)

-- ofString?: 無効な入力は none を返すこと
#guard Quarter.ofString? "" == none
#guard Quarter.ofString? "  " == none
#guard Quarter.ofString? "C" == none
#guard Quarter.ofString? "CCC" == none
#guard Quarter.ofString? "XX" == none
#guard Quarter.ofString? "C-" == none
#guard Quarter.ofString? "c-" == none
#guard Quarter.ofString? "-C" == none
#guard Quarter.ofString? "-c" == none
-- ピンは colored にならないため none
#guard Quarter.ofString? "Pr" == none
#guard Quarter.ofString? "Pg" == none

-- ラウンドトリップ: ofString? (toString q) == some q
#guard Quarter.ofString? (Quarter.empty.toString) == some Quarter.empty
#guard Quarter.ofString? (Quarter.pin.toString) == some Quarter.pin
#guard Quarter.ofString? ((Quarter.colored .circle .red).toString) == some (Quarter.colored .circle .red)
#guard Quarter.ofString? ((Quarter.colored .windmill .uncolored).toString) == some (Quarter.colored .windmill .uncolored)
#guard Quarter.ofString? ((Quarter.crystal .red).toString) == some (Quarter.crystal .red)
#guard Quarter.ofString? ((Quarter.crystal .cyan).toString) == some (Quarter.crystal .cyan)

-- isEmpty
#guard Quarter.empty.isEmpty == true
#guard Quarter.pin.isEmpty == false
#guard (Quarter.colored .circle .red).isEmpty == false
#guard (Quarter.crystal .red).isEmpty == false

-- partCode?: PartCode に変換されること
#guard Quarter.empty.partCode? == none
#guard Quarter.pin.partCode? == some PartCode.pin
#guard (Quarter.colored .circle .red).partCode? == some PartCode.circle
#guard (Quarter.colored .star .blue).partCode? == some PartCode.star
#guard (Quarter.colored .windmill .cyan).partCode? == some PartCode.windmill
#guard (Quarter.colored .rectangle .green).partCode? == some PartCode.rectangle
#guard (Quarter.crystal .red).partCode? == some PartCode.crystal

-- color?
#guard Quarter.empty.color? == none
#guard Quarter.pin.color? == none
#guard (Quarter.colored .circle .red).color? == some Color.red
#guard (Quarter.colored .rectangle .uncolored).color? == some Color.uncolored
#guard (Quarter.crystal .blue).color? == some Color.blue
#guard (Quarter.crystal .uncolored).color? == some Color.uncolored

-- DecidableEq: 同値性と非同値性
#guard Quarter.empty == Quarter.empty
#guard Quarter.pin == Quarter.pin
#guard Quarter.colored .circle .red == Quarter.colored .circle .red
#guard Quarter.crystal .red == Quarter.crystal .red
#guard Quarter.empty != Quarter.pin
#guard Quarter.pin != Quarter.colored .circle .red
#guard Quarter.colored .circle .red != Quarter.colored .circle .blue
#guard Quarter.colored .circle .red != Quarter.colored .star .red
#guard Quarter.crystal .red != Quarter.crystal .blue
#guard Quarter.crystal .red != Quarter.colored .circle .red
