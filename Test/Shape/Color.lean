-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- Color のユニットテスト
import S2IL.Shape.Color

-- toChar: 各バリアントが正しい文字を返すこと
#guard Color.red.toChar == 'r'
#guard Color.green.toChar == 'g'
#guard Color.blue.toChar == 'b'
#guard Color.yellow.toChar == 'y'
#guard Color.cyan.toChar == 'c'
#guard Color.magenta.toChar == 'm'
#guard Color.white.toChar == 'w'
#guard Color.uncolored.toChar == 'u'

-- fromChar?: 有効な文字が正しいバリアントを返すこと
#guard Color.fromChar? 'r' == some Color.red
#guard Color.fromChar? 'g' == some Color.green
#guard Color.fromChar? 'b' == some Color.blue
#guard Color.fromChar? 'y' == some Color.yellow
#guard Color.fromChar? 'c' == some Color.cyan
#guard Color.fromChar? 'm' == some Color.magenta
#guard Color.fromChar? 'w' == some Color.white
#guard Color.fromChar? 'u' == some Color.uncolored

-- fromChar?: 無効な文字は none を返すこと
#guard Color.fromChar? 'X' == none
#guard Color.fromChar? 'R' == none
#guard Color.fromChar? ' ' == none

-- '-' は色の不在を表し、Color のバリアントではないため none
#guard Color.fromChar? '-' == none

-- ラウンドトリップ: fromChar? (toChar c) == some c
#guard Color.fromChar? (Color.red.toChar) == some Color.red
#guard Color.fromChar? (Color.green.toChar) == some Color.green
#guard Color.fromChar? (Color.blue.toChar) == some Color.blue
#guard Color.fromChar? (Color.yellow.toChar) == some Color.yellow
#guard Color.fromChar? (Color.cyan.toChar) == some Color.cyan
#guard Color.fromChar? (Color.magenta.toChar) == some Color.magenta
#guard Color.fromChar? (Color.white.toChar) == some Color.white
#guard Color.fromChar? (Color.uncolored.toChar) == some Color.uncolored

-- DecidableEq: 同値性と非同値性
#guard Color.red == Color.red
#guard Color.uncolored == Color.uncolored
#guard Color.red != Color.blue
#guard Color.cyan != Color.magenta
#guard Color.uncolored != Color.white

-- all: 全バリアントが含まれていること
#guard Color.all.length == 8
