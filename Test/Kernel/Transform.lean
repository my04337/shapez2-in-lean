-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

/-!
# Test.Kernel.Transform

`Layer.rotateCW` / `Shape.rotateCW` / `rotate180` / `rotateCCW` の単体テスト。
4 周性・レイヤ数保存・QuarterPos 双射性を網羅する。
-/

import S2IL.Kernel

open S2IL

namespace Test.Kernel.Transform

private def L : Layer :=
  Layer.mk (.colored .circle .red) (.colored .star .green)
           (.colored .windmill .blue) (.crystal .yellow)
private def s2 : Shape := Shape.double L Layer.empty
private def s3 : Shape := Shape.triple L L L

-- ============================================================
-- 4 周性
-- ============================================================

example (l : Layer) : l.rotateCW.rotateCW.rotateCW.rotateCW = l :=
  Layer.rotateCW.four l

example (s : Shape) : s.rotateCW.rotateCW.rotateCW.rotateCW = s :=
  Shape.rotateCW.four s

-- ============================================================
-- 180° / CCW の単一チェーン依存
-- ============================================================

example (s : Shape) : s.rotate180 = s.rotateCW.rotateCW := rfl
example (s : Shape) : s.rotateCCW = s.rotateCW.rotateCW.rotateCW := rfl
example (l : Layer) : l.rotate180 = l.rotateCW.rotateCW := rfl
example (l : Layer) : l.rotateCCW = l.rotateCW.rotateCW.rotateCW := rfl

-- 4 周性から 180° の自己逆性
example (s : Shape) : s.rotate180.rotate180 = s := by
  show s.rotateCW.rotateCW.rotateCW.rotateCW = s
  exact Shape.rotateCW.four s

-- CW の 3 回 = CCW
example (s : Shape) : s.rotateCW.rotateCW.rotateCW = s.rotateCCW := rfl

-- ============================================================
-- レイヤ数保存
-- ============================================================

#guard s2.rotateCW.layerCount == s2.layerCount
#guard s3.rotate180.layerCount == s3.layerCount
#guard s3.rotateCCW.layerCount == s3.layerCount

example (s : Shape) : s.rotateCW.layerCount = s.layerCount := Shape.layerCount.rotateCW s
example (s : Shape) : s.rotate180.layerCount = s.layerCount := Shape.layerCount.rotate180 s
example (s : Shape) : s.rotateCCW.layerCount = s.layerCount := Shape.layerCount.rotateCCW s

-- ============================================================
-- Layer.rotateCW: index シフト
-- ============================================================

-- l.rotateCW d = l (d - 1)
example (l : Layer) (d : Direction) : l.rotateCW d = l (d - 1) := Layer.rotateCW_apply l d
-- l.rotateCW (d + 1) = l d
example (l : Layer) (d : Direction) : l.rotateCW (d + 1) = l d := Layer.rotateCW_apply_succ l d

-- 具体例: NE 値が SE から流入
#guard L.rotateCW Direction.se == L Direction.ne
#guard L.rotateCW Direction.sw == L Direction.se
#guard L.rotateCW Direction.nw == L Direction.sw
#guard L.rotateCW Direction.ne == L Direction.nw

-- ============================================================
-- QuarterPos.rotateCW / rotateCCW
-- ============================================================

#guard QuarterPos.rotateCW (3, Direction.ne) == ((3, Direction.se) : QuarterPos)
#guard QuarterPos.rotateCW (3, Direction.se) == ((3, Direction.sw) : QuarterPos)
#guard QuarterPos.rotateCCW (3, Direction.ne) == ((3, Direction.nw) : QuarterPos)

-- 双射: CW ∘ CCW = id, CCW ∘ CW = id
example (p : QuarterPos) : p.rotateCCW.rotateCW = p := QuarterPos.rotateCW_rotateCCW p
example (p : QuarterPos) : p.rotateCW.rotateCCW = p := QuarterPos.rotateCCW_rotateCW p

-- 単射性
example : Function.Injective QuarterPos.rotateCW := QuarterPos.rotateCW_injective

-- レイヤ index 不変
example (p : QuarterPos) : p.rotateCW.1 = p.1 := QuarterPos.rotateCW_fst p
example (p : QuarterPos) : p.rotateCCW.1 = p.1 := QuarterPos.rotateCCW_fst p

-- ============================================================
-- allValid_rotateCW / mem_allValid / getQuarter_rotateCW
-- ============================================================

example (s : Shape) : QuarterPos.allValid s.rotateCW = QuarterPos.allValid s :=
  QuarterPos.allValid_rotateCW s

example (s : Shape) (p : QuarterPos) :
    p ∈ QuarterPos.allValid s ↔ p.1 < s.length :=
  QuarterPos.mem_allValid s p

example (s : Shape) (p : QuarterPos) :
    QuarterPos.getQuarter s.rotateCW p.rotateCW = QuarterPos.getQuarter s p :=
  QuarterPos.getQuarter_rotateCW s p

-- ============================================================
-- Direction.isAdjacent は CW で不変
-- ============================================================

example (d1 d2 : Direction) :
    Direction.isAdjacent (d1 + 1) (d2 + 1) = Direction.isAdjacent d1 d2 :=
  Direction.isAdjacent_rotateCW d1 d2

end Test.Kernel.Transform
