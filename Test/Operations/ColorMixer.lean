-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

/-!
# Test.Operations.ColorMixer

混色機 (A-2-3) のテスト。`S2IL.Operations.mix` は `Color.mix` の alias なので
`Color.mix` の規則表 ( `docs/shapez2/game-system-overview.md` ) を網羅的にカバーする。
-/

import S2IL.Operations

open S2IL S2IL.Operations

namespace Test.Operations.ColorMixer

-- ============================================================
-- 恒等元: uncolored
-- ============================================================

example (a : Color) : mix Color.uncolored a = a := mix_uncolored_left a
example (a : Color) : mix a Color.uncolored = a := mix_uncolored_right a

#guard mix Color.uncolored Color.red == Color.red
#guard mix Color.blue Color.uncolored == Color.blue

-- ============================================================
-- 可換性
-- ============================================================

example (a b : Color) : mix a b = mix b a := mix_comm a b

-- ============================================================
-- 同色
-- ============================================================

#guard mix Color.red     Color.red     == Color.red
#guard mix Color.green   Color.green   == Color.green
#guard mix Color.blue    Color.blue    == Color.blue
#guard mix Color.yellow  Color.yellow  == Color.yellow
#guard mix Color.cyan    Color.cyan    == Color.cyan
#guard mix Color.magenta Color.magenta == Color.magenta

-- ============================================================
-- 1 原色 + 1 原色 (異) → ビット OR で 2 原色
-- ============================================================

#guard mix Color.red   Color.green == Color.yellow
#guard mix Color.green Color.blue  == Color.cyan
#guard mix Color.red   Color.blue  == Color.magenta

-- 可換性チェック
#guard mix Color.green Color.red  == Color.yellow
#guard mix Color.blue  Color.red  == Color.magenta

-- ============================================================
-- 1 原色 + 2 原色（含む）→ 1 原色（AND）
-- ============================================================

#guard mix Color.red   Color.yellow  == Color.red
#guard mix Color.red   Color.magenta == Color.red
#guard mix Color.green Color.yellow  == Color.green
#guard mix Color.green Color.cyan    == Color.green
#guard mix Color.blue  Color.cyan    == Color.blue
#guard mix Color.blue  Color.magenta == Color.blue

-- ============================================================
-- 1 原色 + 2 原色（含まない）→ white
-- ============================================================

#guard mix Color.red   Color.cyan    == Color.white
#guard mix Color.green Color.magenta == Color.white
#guard mix Color.blue  Color.yellow  == Color.white

-- ============================================================
-- 2 原色 + 2 原色（異）→ white
-- ============================================================

#guard mix Color.yellow  Color.cyan    == Color.white
#guard mix Color.yellow  Color.magenta == Color.white
#guard mix Color.cyan    Color.magenta == Color.white

-- ============================================================
-- 3 原色 (white / black) の規則
-- ============================================================

#guard mix Color.white Color.white == Color.black
#guard mix Color.black Color.black == Color.black
#guard mix Color.white Color.black == Color.uncolored
#guard mix Color.black Color.white == Color.uncolored

-- 3 原色 + 非 3 原色 (非無色) → 相手側
#guard mix Color.white Color.red    == Color.red
#guard mix Color.black Color.yellow == Color.yellow
#guard mix Color.red    Color.white == Color.red
#guard mix Color.yellow Color.black == Color.yellow

end Test.Operations.ColorMixer
