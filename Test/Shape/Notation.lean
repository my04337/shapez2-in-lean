-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

/-!
# Test.Shape.Notation

`Quarter` / `Layer` / `Shape` の文字列表現と round-trip テスト。
-/

import S2IL.Shape

open S2IL

namespace Test.Shape.Notation

-- ============================================================
-- Quarter.toString / ofString?
-- ============================================================

#guard Quarter.empty.toString             == "--"
#guard Quarter.pin.toString               == "P-"
#guard (Quarter.crystal .red).toString    == "cr"
#guard (Quarter.crystal .uncolored).toString == "cu"
#guard (Quarter.colored .circle .yellow).toString == "Cy"
#guard (Quarter.colored .windmill .blue).toString == "Wb"

#guard Quarter.ofString? "--" == some Quarter.empty
#guard Quarter.ofString? "P-" == some Quarter.pin
#guard Quarter.ofString? "cr" == some (Quarter.crystal .red)
#guard Quarter.ofString? "Sg" == some (Quarter.colored .star .green)

-- 失敗ケース: 長さ違反 / 未定義文字 / pin/crystal はそれぞれ専用構文
#guard (Quarter.ofString? "" : Option Quarter) == none
#guard (Quarter.ofString? "x" : Option Quarter) == none
#guard (Quarter.ofString? "Cyy" : Option Quarter) == none
#guard (Quarter.ofString? "PP" : Option Quarter) == none  -- pin は P-
#guard (Quarter.ofString? "Pr" : Option Quarter) == none  -- P は RegularPartCode に含まれない
#guard (Quarter.ofString? "cz" : Option Quarter) == none  -- crystal の色不正

example (q : Quarter) : Quarter.ofString? q.toString = some q := Quarter.ofString_toString q

-- ============================================================
-- Layer.toString / ofString?（8 文字 = NE → SE → SW → NW）
-- ============================================================

private def L4r : Layer :=
  Layer.mk (.crystal .red) (.crystal .red) (.crystal .red) (.crystal .red)
private def L_dist : Layer :=
  Layer.mk (.colored .circle .red) (.colored .star .green)
           (.crystal .blue) Quarter.empty

#guard L4r.toString == "crcrcrcr"
#guard L_dist.toString == "CrSgcb--"
#guard Layer.empty.toString == "--------"

#guard Layer.ofString? "crcrcrcr" == some L4r
#guard Layer.ofString? "--------" == some Layer.empty

-- 失敗ケース
#guard (Layer.ofString? "" : Option Layer) == none
#guard (Layer.ofString? "crcrcrc" : Option Layer) == none  -- 7 文字
#guard (Layer.ofString? "crcrcrcrr" : Option Layer) == none  -- 9 文字
#guard (Layer.ofString? "crcrcrxx" : Option Layer) == none  -- 不正 Quarter

example (l : Layer) : Layer.ofString? l.toString = some l := Layer.ofString_toString l

-- ============================================================
-- Shape.toString / ofString?（`:` 区切り）
-- ============================================================

private def S0 : Shape := Shape.empty
private def S1 : Shape := Shape.single L4r
private def S2 : Shape := Shape.double L4r L_dist

#guard S0.toString == ""
#guard S1.toString == "crcrcrcr"
#guard S2.toString == "crcrcrcr:CrSgcb--"

#guard Shape.ofString? "" == some Shape.empty
#guard Shape.ofString? "crcrcrcr" == some S1

-- 末尾に空レイヤを連ねた入力は normalize で除去される
#guard Shape.ofString? "crcrcrcr:--------" == some S1
#guard Shape.ofString? "--------" == some Shape.empty

-- 失敗ケース: 区切られた各セグメントが Layer として不正
#guard (Shape.ofString? "xxxxxxxx" : Option Shape) == none
#guard (Shape.ofString? "crcrcrcr:short" : Option Shape) == none

-- 正規化済みシェイプの round-trip
example (s : Shape) (h : s.IsNormalized) : Shape.ofString? s.toString = some s :=
  Shape.ofString_toString s h

example : Shape.ofString? S1.toString = some S1 :=
  Shape.ofString_toString S1 (by decide)
example : Shape.ofString? S2.toString = some S2 :=
  Shape.ofString_toString S2 (by decide)

end Test.Shape.Notation
