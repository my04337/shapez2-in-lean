-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- ColorMixer (混色機) のユニットテスト
import S2IL.Behavior.ColorMixer
import S2IL.Machine.Machine

-- ============================================================
-- ColorMixer.mix: ColorMixer モジュール経由の混色テスト
-- ============================================================

-- 原色同士
#guard ColorMixer.mix Color.red Color.green == Color.yellow
#guard ColorMixer.mix Color.red Color.blue == Color.magenta
#guard ColorMixer.mix Color.green Color.blue == Color.cyan

-- 冪等性
#guard ColorMixer.mix Color.red Color.red == Color.red
#guard ColorMixer.mix Color.yellow Color.yellow == Color.yellow
#guard ColorMixer.mix Color.white Color.white == Color.white
#guard ColorMixer.mix Color.uncolored Color.uncolored == Color.uncolored

-- White 恒等元
#guard ColorMixer.mix Color.white Color.red == Color.red
#guard ColorMixer.mix Color.white Color.green == Color.green
#guard ColorMixer.mix Color.white Color.blue == Color.blue
#guard ColorMixer.mix Color.white Color.yellow == Color.yellow
#guard ColorMixer.mix Color.white Color.cyan == Color.cyan
#guard ColorMixer.mix Color.white Color.magenta == Color.magenta

-- 二次色 × 原色
#guard ColorMixer.mix Color.yellow Color.red == Color.red
#guard ColorMixer.mix Color.yellow Color.blue == Color.blue
#guard ColorMixer.mix Color.cyan Color.green == Color.green
#guard ColorMixer.mix Color.cyan Color.red == Color.red
#guard ColorMixer.mix Color.magenta Color.blue == Color.blue
#guard ColorMixer.mix Color.magenta Color.green == Color.green

-- 二次色 × 二次色
#guard ColorMixer.mix Color.yellow Color.cyan == Color.green
#guard ColorMixer.mix Color.yellow Color.magenta == Color.red
#guard ColorMixer.mix Color.cyan Color.magenta == Color.blue

-- ============================================================
-- Machine.mixColor: Option ラッパーのテスト
-- ============================================================

-- 両方 some: 正常に混色される
#guard Machine.mixColor (some Color.red) (some Color.green) == some Color.yellow
#guard Machine.mixColor (some Color.white) (some Color.blue) == some Color.blue
#guard Machine.mixColor (some Color.cyan) (some Color.magenta) == some Color.blue

-- 片方 none: none を返す
#guard Machine.mixColor none (some Color.red) == none
#guard Machine.mixColor (some Color.red) none == none

-- 両方 none: none を返す
#guard Machine.mixColor none none == none
