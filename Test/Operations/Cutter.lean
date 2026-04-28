-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

/-!
# Test.Operations.Cutter

切断機・半壊機 (A-2-1 + B-4-2) のテスト。

* `eastHalf` / `westHalf` — NE/SE 側 / SW/NW 側のみ残す
* `combineHalves`         — `List.zipWith` 実装、長さは min に揃う
* `cut`                   — `(eastHalf, westHalf)` のペア
* `halfDestroy`           — `eastHalf` の alias

§1.4.1 例外規則: `cut` / `halfDestroy` は CW 等変性を持たず、180° のみ。
-/

import S2IL.Operations

open S2IL

namespace Test.Operations.Cutter

-- ============================================================
-- 共通サンプル
-- ============================================================

private def L_full : Layer :=
  Layer.mk (.colored .circle .red) (.colored .star .green)
           (.colored .windmill .blue) (.crystal .yellow)
private def s1 : Shape := [L_full]
private def s2 : Shape := [L_full, L_full]

-- ============================================================
-- Layer.eastHalf / westHalf — index 別の値
-- ============================================================

#guard Layer.eastHalf L_full Direction.ne == L_full Direction.ne
#guard Layer.eastHalf L_full Direction.se == L_full Direction.se
#guard Layer.eastHalf L_full Direction.sw == Quarter.empty
#guard Layer.eastHalf L_full Direction.nw == Quarter.empty

#guard Layer.westHalf L_full Direction.ne == Quarter.empty
#guard Layer.westHalf L_full Direction.se == Quarter.empty
#guard Layer.westHalf L_full Direction.sw == L_full Direction.sw
#guard Layer.westHalf L_full Direction.nw == L_full Direction.nw

-- ============================================================
-- Layer.combineHalves — 部分性
-- ============================================================

example (l : Layer) :
    Layer.combineHalves l.eastHalf l.westHalf = l :=
  Layer.combineHalves.eastHalf_westHalf l

example (l : Layer) : Layer.combineHalves l l = l := Layer.combineHalves.self l

-- ============================================================
-- Shape.eastHalf / westHalf — 構造的
-- ============================================================

#guard (Shape.eastHalf [] : Shape) == []
#guard (Shape.westHalf [] : Shape) == []
#guard (Shape.eastHalf s1).length == 1
#guard (Shape.westHalf s1).length == 1
#guard (Shape.eastHalf s2).length == 2

-- 各レイヤに Layer.eastHalf が掛かる
example : Shape.eastHalf s2 = [L_full.eastHalf, L_full.eastHalf] := rfl
example : Shape.westHalf s2 = [L_full.westHalf, L_full.westHalf] := rfl

-- ============================================================
-- Shape.combineHalves — 構造的恒等式
-- ============================================================

example (s : Shape) :
    Shape.combineHalves (Shape.eastHalf s) (Shape.westHalf s) = s :=
  Shape.combineHalves.eastHalf_westHalf s

example (s : Shape) : Shape.combineHalves s s = s := Shape.combineHalves.self s

-- 長さが異なる場合は短い方に揃う（zipWith 仕様）
private def sLong : Shape := [L_full, L_full, L_full]
private def sShort : Shape := [L_full]

#guard (Shape.combineHalves sLong sShort).length == 1
#guard (Shape.combineHalves sShort sLong).length == 1
#guard (Shape.combineHalves sLong (Shape.empty)).length == 0

-- ============================================================
-- Shape.cut / halfDestroy — 派生
-- ============================================================

#guard (Shape.cut s1).1 == Shape.eastHalf s1
#guard (Shape.cut s1).2 == Shape.westHalf s1
#guard Shape.halfDestroy s1 == Shape.eastHalf s1

example (s : Shape) : Shape.halfDestroy s = (Shape.cut s).1 :=
  Shape.halfDestroy.eq_cut_fst s

-- ============================================================
-- 180° 等変性（CW / CCW は持たない、§1.4.1）
-- ============================================================

example (s : Shape) :
    Shape.eastHalf s.rotate180 = (Shape.westHalf s).rotate180 :=
  Shape.eastHalf.rotate180_comm s

example (s : Shape) :
    Shape.westHalf s.rotate180 = (Shape.eastHalf s).rotate180 :=
  Shape.westHalf.rotate180_comm s

example (a b : Shape) :
    (Shape.combineHalves a b).rotate180 =
      Shape.combineHalves b.rotate180 a.rotate180 :=
  Shape.combineHalves.rotate180_comm a b

example (s : Shape) :
    Shape.cut s.rotate180 =
      ((Shape.westHalf s).rotate180, (Shape.eastHalf s).rotate180) :=
  Shape.cut.rotate180_comm s

example (s : Shape) :
    Shape.halfDestroy s.rotate180 = (Shape.westHalf s).rotate180 :=
  Shape.halfDestroy.rotate180_comm s

end Test.Operations.Cutter
