-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

/-!
# Test.Kernel.Bond

`IsBonded` / `isBonded` の単体テスト。
具体シェイプ上で結合関係を `decide` で検証し、対称性・CW 等変性をスポット確認する。
-/

import S2IL.Kernel

open S2IL

namespace Test.Kernel.Bond

-- ------------------------------------------------------------
-- 検証用シェイプ
-- ------------------------------------------------------------

-- 4 象限すべて結晶
private def Lc : Layer :=
  Layer.mk (.crystal .red) (.crystal .red) (.crystal .red) (.crystal .red)

-- 結晶 + 通常パーツ + 空 + ピン（隣接判定の各種境界）
private def Lmix : Layer :=
  Layer.mk (.crystal .red) (.colored .circle .red) Quarter.empty Quarter.pin

-- 1 層のみ結晶
private def s1 : Shape := Shape.single Lc

-- 2 層: 下 = 結晶 4 / 上 = 結晶 4
private def s2 : Shape := Shape.double Lc Lc

-- 2 層: 下 = 結晶 4 / 上 = 通常パーツのみ
private def s2mix : Shape := Shape.double Lc Lmix

-- ============================================================
-- 同レイヤ内結合
-- ============================================================

-- 隣接 (NE, SE) は結合
example : IsBondedInLayer s1 (0, .ne) (0, .se) := by decide
#guard isBonded s1 (0, .ne) (0, .se)

-- 環の折返し (NW, NE) も隣接
#guard isBonded s1 (0, .nw) (0, .ne)

-- 反対側 (NE, SW) は隣接でない → 結合なし
#guard !isBonded s1 (0, .ne) (0, .sw)
example : ¬ IsBonded s1 (0, .ne) (0, .sw) := by decide

-- 自己ペア (NE, NE) は隣接条件で false
#guard !isBonded s1 (0, .ne) (0, .ne)

-- 結晶でない象限とは結合しない
#guard !isBonded s2mix (1, .ne) (1, .se)  -- crystal + colored
#guard !isBonded s2mix (1, .se) (1, .sw)  -- colored + empty
#guard !isBonded s2mix (1, .sw) (1, .nw)  -- empty + pin

-- ============================================================
-- 上下レイヤ間結合
-- ============================================================

-- 隣接層 + 同方角 + 結晶
example : IsBondedCrossLayer s2 (0, .ne) (1, .ne) := by decide
#guard isBonded s2 (0, .ne) (1, .ne)
#guard isBonded s2 (1, .se) (0, .se)  -- 逆順も OK

-- 同方角でない場合は結合なし
#guard !isBonded s2 (0, .ne) (1, .se)

-- 隣接していない層（同層でも上下隣でもない）は結合なし
private def s3 : Shape := Shape.triple Lc Lc Lc
#guard !isBonded s3 (0, .ne) (2, .ne)

-- 上層に結晶がない場合は結合なし
#guard !isBonded s2mix (0, .se) (1, .se)  -- 下: crystal, 上: colored

-- ============================================================
-- IsBonded.symm
-- ============================================================

example {s : Shape} {p q : QuarterPos} (h : IsBonded s p q) : IsBonded s q p := h.symm

example : IsBonded s2 (0, .ne) (1, .ne) := by decide
example : IsBonded s2 (1, .ne) (0, .ne) :=
  IsBonded.symm (by decide : IsBonded s2 (0, .ne) (1, .ne))

-- ============================================================
-- IsBonded.rotateCW
-- ============================================================

example (s : Shape) (p q : QuarterPos) :
    IsBonded s.rotateCW p.rotateCW q.rotateCW ↔ IsBonded s p q :=
  IsBonded.rotateCW s p q

-- 具体: (0, NE) と (0, SE) → CW 後 (0, SE) と (0, SW)
#guard isBonded s1.rotateCW (QuarterPos.rotateCW (0, .ne)) (QuarterPos.rotateCW (0, .se))
#guard isBonded s1 (0, .ne) (0, .se)

-- 180° / CCW 系もチェーン経由で成立
example (s : Shape) (p q : QuarterPos) :
    IsBonded s.rotate180 p.rotateCW.rotateCW q.rotateCW.rotateCW ↔ IsBonded s p q :=
  IsBonded.rotate180 s p q

example (s : Shape) (p q : QuarterPos) :
    IsBonded s.rotateCCW p.rotateCW.rotateCW.rotateCW q.rotateCW.rotateCW.rotateCW ↔
      IsBonded s p q :=
  IsBonded.rotateCCW s p q

-- ============================================================
-- Prop/Bool 橋渡し
-- ============================================================

example (s : Shape) (p q : QuarterPos) :
    isBonded s p q = true ↔ IsBonded s p q := isBonded.iff s p q

end Test.Kernel.Bond
