-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- PartCode / RegularPartCode のユニットテスト
import S2IL.Shape.PartCode

-- toChar: 各バリアントが正しい文字を返すこと
#guard PartCode.circle.toChar == 'C'
#guard PartCode.rectangle.toChar == 'R'
#guard PartCode.star.toChar == 'S'
#guard PartCode.windmill.toChar == 'W'
#guard PartCode.pin.toChar == 'P'
#guard PartCode.crystal.toChar == 'c'

-- ofChar?: 有効な文字が正しいバリアントを返すこと
#guard PartCode.ofChar? 'C' == some PartCode.circle
#guard PartCode.ofChar? 'R' == some PartCode.rectangle
#guard PartCode.ofChar? 'S' == some PartCode.star
#guard PartCode.ofChar? 'W' == some PartCode.windmill
#guard PartCode.ofChar? 'P' == some PartCode.pin
#guard PartCode.ofChar? 'c' == some PartCode.crystal

-- ofChar?: 無効な文字は none を返すこと
#guard PartCode.ofChar? 'X' == none
#guard PartCode.ofChar? 'r' == none
#guard PartCode.ofChar? '-' == none
#guard PartCode.ofChar? ' ' == none
#guard PartCode.ofChar? 'C' != none

-- ラウンドトリップ: ofChar? (toChar p) == some p
#guard PartCode.ofChar? (PartCode.circle.toChar) == some PartCode.circle
#guard PartCode.ofChar? (PartCode.rectangle.toChar) == some PartCode.rectangle
#guard PartCode.ofChar? (PartCode.star.toChar) == some PartCode.star
#guard PartCode.ofChar? (PartCode.windmill.toChar) == some PartCode.windmill
#guard PartCode.ofChar? (PartCode.pin.toChar) == some PartCode.pin
#guard PartCode.ofChar? (PartCode.crystal.toChar) == some PartCode.crystal

-- DecidableEq: 同値性と非同値性
#guard PartCode.circle == PartCode.circle
#guard PartCode.rectangle == PartCode.rectangle
#guard PartCode.circle != PartCode.rectangle
#guard PartCode.star != PartCode.windmill
#guard PartCode.pin != PartCode.crystal

-- all: 全バリアントが含まれていること
#guard PartCode.all.length == 6

-- RegularPartCode: toChar
#guard RegularPartCode.circle.toChar == 'C'
#guard RegularPartCode.rectangle.toChar == 'R'
#guard RegularPartCode.star.toChar == 'S'
#guard RegularPartCode.windmill.toChar == 'W'

-- RegularPartCode: ofChar? 有効文字
#guard RegularPartCode.ofChar? 'C' == some RegularPartCode.circle
#guard RegularPartCode.ofChar? 'R' == some RegularPartCode.rectangle
#guard RegularPartCode.ofChar? 'S' == some RegularPartCode.star
#guard RegularPartCode.ofChar? 'W' == some RegularPartCode.windmill

-- RegularPartCode: ofChar? はピン・クリスタル・無効文字を除外すること
#guard RegularPartCode.ofChar? 'P' == none
#guard RegularPartCode.ofChar? 'c' == none
#guard RegularPartCode.ofChar? 'X' == none
#guard RegularPartCode.ofChar? '-' == none

-- RegularPartCode: ラウンドトリップ
#guard RegularPartCode.ofChar? (RegularPartCode.circle.toChar) == some RegularPartCode.circle
#guard RegularPartCode.ofChar? (RegularPartCode.rectangle.toChar) == some RegularPartCode.rectangle
#guard RegularPartCode.ofChar? (RegularPartCode.star.toChar) == some RegularPartCode.star
#guard RegularPartCode.ofChar? (RegularPartCode.windmill.toChar) == some RegularPartCode.windmill

-- RegularPartCode: toPartCode が PartCode に対応すること
#guard RegularPartCode.circle.toPartCode == PartCode.circle
#guard RegularPartCode.rectangle.toPartCode == PartCode.rectangle
#guard RegularPartCode.star.toPartCode == PartCode.star
#guard RegularPartCode.windmill.toPartCode == PartCode.windmill

-- RegularPartCode: ofPartCode? が通常パーツのみ some を返すこと
#guard RegularPartCode.ofPartCode? .circle == some RegularPartCode.circle
#guard RegularPartCode.ofPartCode? .rectangle == some RegularPartCode.rectangle
#guard RegularPartCode.ofPartCode? .star == some RegularPartCode.star
#guard RegularPartCode.ofPartCode? .windmill == some RegularPartCode.windmill
#guard RegularPartCode.ofPartCode? .pin == none
#guard RegularPartCode.ofPartCode? .crystal == none

-- RegularPartCode: DecidableEq
#guard RegularPartCode.circle == RegularPartCode.circle
#guard RegularPartCode.circle != RegularPartCode.rectangle

-- RegularPartCode: all
#guard RegularPartCode.all.length == 4
