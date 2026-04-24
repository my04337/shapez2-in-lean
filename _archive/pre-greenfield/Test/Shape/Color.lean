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

-- ============================================================
-- mix: 混色テスト (全 64 パターン)
-- ============================================================

-- Red × 各色
#guard Color.red.mix Color.red == Color.red
#guard Color.red.mix Color.green == Color.yellow
#guard Color.red.mix Color.blue == Color.magenta
#guard Color.red.mix Color.yellow == Color.red
#guard Color.red.mix Color.cyan == Color.white
#guard Color.red.mix Color.magenta == Color.red
#guard Color.red.mix Color.white == Color.red
#guard Color.red.mix Color.uncolored == Color.red

-- Green × 各色
#guard Color.green.mix Color.red == Color.yellow
#guard Color.green.mix Color.green == Color.green
#guard Color.green.mix Color.blue == Color.cyan
#guard Color.green.mix Color.yellow == Color.green
#guard Color.green.mix Color.cyan == Color.green
#guard Color.green.mix Color.magenta == Color.white
#guard Color.green.mix Color.white == Color.green
#guard Color.green.mix Color.uncolored == Color.green

-- Blue × 各色
#guard Color.blue.mix Color.red == Color.magenta
#guard Color.blue.mix Color.green == Color.cyan
#guard Color.blue.mix Color.blue == Color.blue
#guard Color.blue.mix Color.yellow == Color.white
#guard Color.blue.mix Color.cyan == Color.blue
#guard Color.blue.mix Color.magenta == Color.blue
#guard Color.blue.mix Color.white == Color.blue
#guard Color.blue.mix Color.uncolored == Color.blue

-- Yellow × 各色
#guard Color.yellow.mix Color.red == Color.red
#guard Color.yellow.mix Color.green == Color.green
#guard Color.yellow.mix Color.blue == Color.white
#guard Color.yellow.mix Color.yellow == Color.yellow
#guard Color.yellow.mix Color.cyan == Color.green
#guard Color.yellow.mix Color.magenta == Color.red
#guard Color.yellow.mix Color.white == Color.yellow
#guard Color.yellow.mix Color.uncolored == Color.yellow

-- Cyan × 各色
#guard Color.cyan.mix Color.red == Color.white
#guard Color.cyan.mix Color.green == Color.green
#guard Color.cyan.mix Color.blue == Color.blue
#guard Color.cyan.mix Color.yellow == Color.green
#guard Color.cyan.mix Color.cyan == Color.cyan
#guard Color.cyan.mix Color.magenta == Color.blue
#guard Color.cyan.mix Color.white == Color.cyan
#guard Color.cyan.mix Color.uncolored == Color.cyan

-- Magenta × 各色
#guard Color.magenta.mix Color.red == Color.red
#guard Color.magenta.mix Color.green == Color.white
#guard Color.magenta.mix Color.blue == Color.blue
#guard Color.magenta.mix Color.yellow == Color.red
#guard Color.magenta.mix Color.cyan == Color.blue
#guard Color.magenta.mix Color.magenta == Color.magenta
#guard Color.magenta.mix Color.white == Color.magenta
#guard Color.magenta.mix Color.uncolored == Color.magenta

-- White × 各色
#guard Color.white.mix Color.red == Color.red
#guard Color.white.mix Color.green == Color.green
#guard Color.white.mix Color.blue == Color.blue
#guard Color.white.mix Color.yellow == Color.yellow
#guard Color.white.mix Color.cyan == Color.cyan
#guard Color.white.mix Color.magenta == Color.magenta
#guard Color.white.mix Color.white == Color.white
#guard Color.white.mix Color.uncolored == Color.white

-- Uncolored × 各色
#guard Color.uncolored.mix Color.red == Color.red
#guard Color.uncolored.mix Color.green == Color.green
#guard Color.uncolored.mix Color.blue == Color.blue
#guard Color.uncolored.mix Color.yellow == Color.yellow
#guard Color.uncolored.mix Color.cyan == Color.cyan
#guard Color.uncolored.mix Color.magenta == Color.magenta
#guard Color.uncolored.mix Color.white == Color.white
#guard Color.uncolored.mix Color.uncolored == Color.uncolored

-- 可換性のスポットチェック
#guard Color.red.mix Color.green == Color.green.mix Color.red
#guard Color.blue.mix Color.yellow == Color.yellow.mix Color.blue
#guard Color.cyan.mix Color.magenta == Color.magenta.mix Color.cyan
#guard Color.white.mix Color.uncolored == Color.uncolored.mix Color.white
