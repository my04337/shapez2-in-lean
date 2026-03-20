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

-- ofChar?: 有効な文字が正しいバリアントを返すこと
#guard Color.ofChar? 'r' == some Color.red
#guard Color.ofChar? 'g' == some Color.green
#guard Color.ofChar? 'b' == some Color.blue
#guard Color.ofChar? 'y' == some Color.yellow
#guard Color.ofChar? 'c' == some Color.cyan
#guard Color.ofChar? 'm' == some Color.magenta
#guard Color.ofChar? 'w' == some Color.white
#guard Color.ofChar? 'u' == some Color.uncolored

-- ofChar?: 無効な文字は none を返すこと
#guard Color.ofChar? 'X' == none
#guard Color.ofChar? 'R' == none
#guard Color.ofChar? ' ' == none

-- '-' は色の不在を表し、Color のバリアントではないため none
#guard Color.ofChar? '-' == none

-- ラウンドトリップ: ofChar? (toChar c) == some c
#guard Color.ofChar? (Color.red.toChar) == some Color.red
#guard Color.ofChar? (Color.green.toChar) == some Color.green
#guard Color.ofChar? (Color.blue.toChar) == some Color.blue
#guard Color.ofChar? (Color.yellow.toChar) == some Color.yellow
#guard Color.ofChar? (Color.cyan.toChar) == some Color.cyan
#guard Color.ofChar? (Color.magenta.toChar) == some Color.magenta
#guard Color.ofChar? (Color.white.toChar) == some Color.white
#guard Color.ofChar? (Color.uncolored.toChar) == some Color.uncolored

-- DecidableEq: 同値性と非同値性
#guard Color.red == Color.red
#guard Color.uncolored == Color.uncolored
#guard Color.red != Color.blue
#guard Color.cyan != Color.magenta
#guard Color.uncolored != Color.white

-- all: 全バリアントが含まれていること
#guard Color.all.length == 8
