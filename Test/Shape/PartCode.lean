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

-- fromChar?: 有効な文字が正しいバリアントを返すこと
#guard PartCode.fromChar? 'C' == some PartCode.circle
#guard PartCode.fromChar? 'R' == some PartCode.rectangle
#guard PartCode.fromChar? 'S' == some PartCode.star
#guard PartCode.fromChar? 'W' == some PartCode.windmill
#guard PartCode.fromChar? 'P' == some PartCode.pin
#guard PartCode.fromChar? 'c' == some PartCode.crystal

-- fromChar?: 無効な文字は none を返すこと
#guard PartCode.fromChar? 'X' == none
#guard PartCode.fromChar? 'r' == none
#guard PartCode.fromChar? '-' == none
#guard PartCode.fromChar? ' ' == none
#guard PartCode.fromChar? 'C' != none

-- ラウンドトリップ: fromChar? (toChar p) == some p
#guard PartCode.fromChar? (PartCode.circle.toChar) == some PartCode.circle
#guard PartCode.fromChar? (PartCode.rectangle.toChar) == some PartCode.rectangle
#guard PartCode.fromChar? (PartCode.star.toChar) == some PartCode.star
#guard PartCode.fromChar? (PartCode.windmill.toChar) == some PartCode.windmill
#guard PartCode.fromChar? (PartCode.pin.toChar) == some PartCode.pin
#guard PartCode.fromChar? (PartCode.crystal.toChar) == some PartCode.crystal

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

-- RegularPartCode: fromChar? 有効文字
#guard RegularPartCode.fromChar? 'C' == some RegularPartCode.circle
#guard RegularPartCode.fromChar? 'R' == some RegularPartCode.rectangle
#guard RegularPartCode.fromChar? 'S' == some RegularPartCode.star
#guard RegularPartCode.fromChar? 'W' == some RegularPartCode.windmill

-- RegularPartCode: fromChar? はピン・クリスタル・無効文字を除外すること
#guard RegularPartCode.fromChar? 'P' == none
#guard RegularPartCode.fromChar? 'c' == none
#guard RegularPartCode.fromChar? 'X' == none
#guard RegularPartCode.fromChar? '-' == none

-- RegularPartCode: ラウンドトリップ
#guard RegularPartCode.fromChar? (RegularPartCode.circle.toChar) == some RegularPartCode.circle
#guard RegularPartCode.fromChar? (RegularPartCode.rectangle.toChar) == some RegularPartCode.rectangle
#guard RegularPartCode.fromChar? (RegularPartCode.star.toChar) == some RegularPartCode.star
#guard RegularPartCode.fromChar? (RegularPartCode.windmill.toChar) == some RegularPartCode.windmill

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
