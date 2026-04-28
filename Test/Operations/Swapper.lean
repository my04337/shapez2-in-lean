-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

/-!
# Test.Operations.Swapper

スワップ機 (A-2-1 + B-4-3) のテスト。
`swap s1 s2 = (combineHalves (eastHalf s1) (westHalf s2),
                combineHalves (eastHalf s2) (westHalf s1))`。

§1.4.1 例外規則: `swap` は CW 等変性を持たず、180° のみ
（しかも引数が swap される）。
-/

import S2IL.Operations

open S2IL

namespace Test.Operations.Swapper

-- ============================================================
-- 共通サンプル
-- ============================================================

private def L_a : Layer :=
  Layer.mk (.colored .circle .red) (.colored .star .red)
           (.colored .circle .red) (.colored .star .red)
private def L_b : Layer :=
  Layer.mk (.colored .windmill .blue) (.colored .rectangle .blue)
           (.colored .windmill .blue) (.colored .rectangle .blue)

private def s_a : Shape := [L_a]
private def s_b : Shape := [L_b]

-- ============================================================
-- 基本: 1 層同士の swap
-- ============================================================

-- swap (s_a) (s_b):
--   .1 = (s_a の東半分) + (s_b の西半分)
--   .2 = (s_b の東半分) + (s_a の西半分)
example :
    Shape.swap s_a s_b
      = (Shape.combineHalves (Shape.eastHalf s_a) (Shape.westHalf s_b),
         Shape.combineHalves (Shape.eastHalf s_b) (Shape.westHalf s_a)) := rfl

#guard (Shape.swap s_a s_b).1.length == 1
#guard (Shape.swap s_a s_b).2.length == 1

-- 出力 .1 の各方角:  NE/SE は s_a, SW/NW は s_b
#guard ((Shape.swap s_a s_b).1.head!) Direction.ne == L_a Direction.ne
#guard ((Shape.swap s_a s_b).1.head!) Direction.se == L_a Direction.se
#guard ((Shape.swap s_a s_b).1.head!) Direction.sw == L_b Direction.sw
#guard ((Shape.swap s_a s_b).1.head!) Direction.nw == L_b Direction.nw
-- 出力 .2 の各方角:  NE/SE は s_b, SW/NW は s_a
#guard ((Shape.swap s_a s_b).2.head!) Direction.ne == L_b Direction.ne
#guard ((Shape.swap s_a s_b).2.head!) Direction.sw == L_a Direction.sw

-- ============================================================
-- 同じシェイプ同士: 入力に戻る（combineHalves.eastHalf_westHalf）
-- ============================================================

example (s : Shape) : (Shape.swap s s).1 = s := by
  show Shape.combineHalves (Shape.eastHalf s) (Shape.westHalf s) = s
  exact Shape.combineHalves.eastHalf_westHalf s

example (s : Shape) : (Shape.swap s s).2 = s := by
  show Shape.combineHalves (Shape.eastHalf s) (Shape.westHalf s) = s
  exact Shape.combineHalves.eastHalf_westHalf s

-- ============================================================
-- 長さ不一致: 短い方に揃う
-- ============================================================

private def s_a2 : Shape := [L_a, L_a]
#guard (Shape.swap s_a s_a2).1.length == 1
#guard (Shape.swap s_a2 s_a).2.length == 1
#guard (Shape.swap [] s_a).1.length == 0
#guard (Shape.swap s_a []).2.length == 0

-- ============================================================
-- 180° 等変性: 出力タプル成分が swap される
-- ============================================================

example (s1 s2 : Shape) :
    Shape.swap s1.rotate180 s2.rotate180 =
      ((Shape.swap s1 s2).2.rotate180, (Shape.swap s1 s2).1.rotate180) :=
  Shape.swap.rotate180_comm s1 s2

end Test.Operations.Swapper
