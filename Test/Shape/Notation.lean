-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape

/-!
# Test.Shape.Notation

`Quarter` / `Layer` / `Shape` の文字列表現と round-trip テスト。
-/

open S2IL

namespace Test.Shape.Notation

private def parsedLayerToString? (input : String) : Option String :=
  (Layer.ofString? input).map Layer.toString

private def parsedShapeToString? (input : String) : Option String :=
  (Shape.ofString? input).map Shape.toString

-- ============================================================
-- Quarter.toString / ofString?
-- ============================================================

#guard Quarter.empty.toString             == "--"
#guard Quarter.pin.toString               == "P-"
#guard (Quarter.crystal .red).toString    == "cr"
#guard (Quarter.crystal .uncolored).toString == "cu"
#guard (Quarter.refined .uncolored).toString == "Xu"
#guard (Quarter.vortexPlatform .white).toString == "Yw"
#guard (Quarter.vortexPlatform .black).toString == "Yk"
#guard (Quarter.colored .circle .yellow).toString == "Cy"
#guard (Quarter.colored .windmill .blue).toString == "Wb"

#guard Quarter.ofString? "--" == some Quarter.empty
#guard Quarter.ofString? "P-" == some Quarter.pin
#guard Quarter.ofString? "cr" == some (Quarter.crystal .red)
#guard Quarter.ofString? "Xu" == some (Quarter.refined .uncolored)
#guard Quarter.ofString? "Yw" == some (Quarter.vortexPlatform .white)
#guard Quarter.ofString? "Yk" == some (Quarter.vortexPlatform .black)
#guard Quarter.ofString? "Sg" == some (Quarter.colored .star .green)

-- 失敗ケース: 長さ違反 / 未定義文字 / pin/crystal はそれぞれ専用構文
#guard (Quarter.ofString? "" : Option Quarter) == none
#guard (Quarter.ofString? "x" : Option Quarter) == none
#guard (Quarter.ofString? "Cyy" : Option Quarter) == none
#guard (Quarter.ofString? "PP" : Option Quarter) == none  -- pin は P-
#guard (Quarter.ofString? "Pr" : Option Quarter) == none  -- P は RegularPartCode に含まれない
#guard (Quarter.ofString? "cz" : Option Quarter) == none  -- crystal の色不正
#guard (Quarter.ofString? "X-" : Option Quarter) == none  -- refined の色不正
#guard (Quarter.ofString? "Y-" : Option Quarter) == none  -- vortex platform の色不正

example (q : Quarter) : Quarter.ofString? q.toString = some q := Quarter.ofString_toString q

-- ============================================================
-- Layer.toString / ofString?（8 文字 = NE → SE → SW → NW）
-- ============================================================

private def L4r : Layer :=
  Layer.mk (.crystal .red) (.crystal .red) (.crystal .red) (.crystal .red)
private def L_dist : Layer :=
  Layer.mk (.colored .circle .red) (.colored .star .green)
           (.crystal .blue) Quarter.empty
private def L_trade : Layer :=
  Layer.mk (.refined .uncolored) (.vortexPlatform .black)
           (.colored .rectangle .green) (.crystal .white)

#guard L4r.toString == "crcrcrcr"
#guard L_dist.toString == "CrSgcb--"
#guard L_trade.toString == "XuYkRgcw"
#guard Layer.empty.toString == "--------"

#guard parsedLayerToString? "crcrcrcr" == some L4r.toString
#guard parsedLayerToString? "XuYkRgcw" == some L_trade.toString
#guard parsedLayerToString? "--------" == some Layer.empty.toString

-- 失敗ケース
#guard parsedLayerToString? "" == none
#guard parsedLayerToString? "crcrcrc" == none  -- 7 文字
#guard parsedLayerToString? "crcrcrcrr" == none  -- 9 文字
#guard parsedLayerToString? "crcrcrxx" == none  -- 不正 Quarter

example (l : Layer) : Layer.ofString? l.toString = some l := Layer.ofString_toString l

-- ============================================================
-- Shape.toString / ofString?（`:` 区切り）
-- ============================================================

private def S0 : Shape := Shape.empty
private def S1 : Shape := Shape.single L4r
private def S2 : Shape := Shape.double L4r L_dist
private def S_trade : Shape := Shape.double L_trade L4r

#guard S0.toString == ""
#guard S1.toString == "crcrcrcr"
#guard S2.toString == "crcrcrcr:CrSgcb--"
#guard S_trade.toString == "XuYkRgcw:crcrcrcr"

#guard parsedShapeToString? "" == some (Shape.toString Shape.empty)
#guard parsedShapeToString? "crcrcrcr" == some (Shape.toString S1)
#guard parsedShapeToString? "XuYkRgcw:crcrcrcr" == some (Shape.toString S_trade)

-- 末尾に空レイヤを連ねた入力は normalize で除去される
#guard parsedShapeToString? "crcrcrcr:--------" == some (Shape.toString S1)
#guard parsedShapeToString? "--------" == some (Shape.toString Shape.empty)

-- 失敗ケース: 区切られた各セグメントが Layer として不正
#guard parsedShapeToString? "xxxxxxxx" == none
#guard parsedShapeToString? "crcrcrcr:short" == none

-- 正規化済みシェイプの round-trip
example (s : Shape) (h : s.IsNormalized) : Shape.ofString? s.toString = some s :=
  Shape.ofString_toString s h

example : Shape.ofString? S1.toString = some S1 :=
  Shape.ofString_toString S1 (by decide)
example : Shape.ofString? S2.toString = some S2 :=
  Shape.ofString_toString S2 (by decide)
example : Shape.ofString? S_trade.toString = some S_trade :=
  Shape.ofString_toString S_trade (by decide)

end Test.Shape.Notation
