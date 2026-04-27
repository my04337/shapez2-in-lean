-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

/-!
# Test.Shape.Atom

`Color` / `PartCode` / `RegularPartCode` の単体テスト。
表現変換（`toChar` / `ofChar?`）と、`Color.mix` 規則（[新仕様](../../docs/shapez2/game-system-overview.md)）を網羅する。
-/

import S2IL.Shape

open S2IL

namespace Test.Shape.Atom

-- ============================================================
-- Color: toChar / ofChar? / round-trip
-- ============================================================

section ColorChar

#guard Color.red.toChar       == 'r'
#guard Color.green.toChar     == 'g'
#guard Color.blue.toChar      == 'b'
#guard Color.yellow.toChar    == 'y'
#guard Color.cyan.toChar      == 'c'
#guard Color.magenta.toChar   == 'm'
#guard Color.white.toChar     == 'w'
#guard Color.black.toChar     == 'k'
#guard Color.uncolored.toChar == 'u'

#guard Color.ofChar? 'r' == some Color.red
#guard Color.ofChar? 'k' == some Color.black
#guard Color.ofChar? 'u' == some Color.uncolored

-- 無効入力
#guard Color.ofChar? 'X' == none
#guard Color.ofChar? '-' == none  -- '-' は色不在（Color のバリアントではない）
#guard Color.ofChar? ' ' == none

-- all は 9 色（black 追加）
#guard Color.all.length == 9

end ColorChar

-- ============================================================
-- Color.mix: 新仕様（black 追加・w+w=k・2 原色×2 原色=w）
-- ============================================================

section ColorMix

-- 単位元 (uncolored)
#guard Color.mix .uncolored .red       == .red
#guard Color.mix .red       .uncolored == .red
#guard Color.mix .uncolored .uncolored == .uncolored

-- 同色は不変（黒以外、白は例外）
#guard Color.mix .red    .red    == .red
#guard Color.mix .yellow .yellow == .yellow
-- 例外: w + w = k, k + k = k
#guard Color.mix .white .white == .black
#guard Color.mix .black .black == .black
-- w + k → uncolored
#guard Color.mix .white .black == .uncolored
#guard Color.mix .black .white == .uncolored

-- 1 原色 + 1 原色（異）= 2 原色（OR）
#guard Color.mix .red   .green == .yellow
#guard Color.mix .green .blue  == .cyan
#guard Color.mix .red   .blue  == .magenta

-- 1 原色 + 2 原色（含む）= 1 原色
#guard Color.mix .red    .yellow  == .red
#guard Color.mix .green  .cyan    == .green
#guard Color.mix .blue   .magenta == .blue

-- 1 原色 + 2 原色（含まない）= white
#guard Color.mix .red   .cyan    == .white
#guard Color.mix .green .magenta == .white
#guard Color.mix .blue  .yellow  == .white

-- 2 原色 + 2 原色（異）= white
#guard Color.mix .yellow .cyan    == .white
#guard Color.mix .yellow .magenta == .white
#guard Color.mix .cyan   .magenta == .white

-- white + 非無色非 3 原色 = 相手側
#guard Color.mix .white .red    == .red
#guard Color.mix .white .yellow == .yellow

-- black + 非無色非 3 原色 = 相手側
#guard Color.mix .black .red    == .red
#guard Color.mix .black .yellow == .yellow

-- 可換性スポット
example : Color.mix .red .green = Color.mix .green .red := Color.mix_comm .red .green
example : Color.mix .yellow .magenta = Color.mix .magenta .yellow :=
  Color.mix_comm .yellow .magenta

end ColorMix

-- ============================================================
-- PartCode / RegularPartCode
-- ============================================================

section PartCode

#guard PartCode.circle.toChar    == 'C'
#guard PartCode.rectangle.toChar == 'R'
#guard PartCode.star.toChar      == 'S'
#guard PartCode.windmill.toChar  == 'W'
#guard PartCode.pin.toChar       == 'P'
#guard PartCode.crystal.toChar   == 'c'

#guard PartCode.ofChar? 'C' == some PartCode.circle
#guard PartCode.ofChar? 'P' == some PartCode.pin
#guard PartCode.ofChar? 'c' == some PartCode.crystal
#guard PartCode.ofChar? 'X' == none
-- 'r' は Color の文字。PartCode 側では無効
#guard PartCode.ofChar? 'r' == none

#guard PartCode.all.length == 6

end PartCode

section RegularPartCode

#guard RegularPartCode.circle.toChar   == 'C'
#guard RegularPartCode.windmill.toChar == 'W'

-- ピン・結晶は通常パーツではないので none
#guard RegularPartCode.ofChar? 'P' == none
#guard RegularPartCode.ofChar? 'c' == none
#guard RegularPartCode.ofChar? 'C' == some RegularPartCode.circle

#guard RegularPartCode.all.length == 4

-- toPartCode / ofPartCode? の round-trip
example (p : RegularPartCode) : RegularPartCode.ofPartCode? p.toPartCode = some p :=
  RegularPartCode.ofPartCode_toPartCode p

#guard RegularPartCode.ofPartCode? .pin == none
#guard RegularPartCode.ofPartCode? .crystal == none
#guard RegularPartCode.ofPartCode? .circle == some .circle

end RegularPartCode

end Test.Shape.Atom
