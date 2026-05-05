-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel

/-!
# Test.Kernel.CrystalBond

`IsCrystalBonded` / `isCrystalBonded` の単体テスト。
具体シェイプ上で結晶結合関係を `decide` で検証し、対称性・CW 等変性をスポット確認する。
-/

open S2IL

namespace Test.Kernel.CrystalBond

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
-- 同レイヤ内結晶結合
-- ============================================================

-- 隣接 (NE, SE) は結晶結合
example : IsCrystalBondedInLayer s1 (0, Direction.ne) (0, Direction.se) := by decide
#guard isCrystalBonded s1 (0, Direction.ne) (0, Direction.se)

-- 環の折返し (NW, NE) も隣接
#guard isCrystalBonded s1 (0, Direction.nw) (0, Direction.ne)

-- 反対側 (NE, SW) は隣接でない → 結晶結合なし
#guard !isCrystalBonded s1 (0, Direction.ne) (0, Direction.sw)
example : ¬ IsCrystalBonded s1 (0, Direction.ne) (0, Direction.sw) := by decide

-- 自己ペア (NE, NE) は隣接条件で false
#guard !isCrystalBonded s1 (0, Direction.ne) (0, Direction.ne)

-- 結晶でない象限とは結晶結合しない
#guard !isCrystalBonded s2mix (1, Direction.ne) (1, Direction.se)  -- crystal + colored
#guard !isCrystalBonded s2mix (1, Direction.se) (1, Direction.sw)  -- colored + empty
#guard !isCrystalBonded s2mix (1, Direction.sw) (1, Direction.nw)  -- empty + pin

-- ============================================================
-- 上下レイヤ間結晶結合
-- ============================================================

-- 隣接層 + 同方角 + 結晶
example : IsCrystalBondedCrossLayer s2 (0, Direction.ne) (1, Direction.ne) := by decide
#guard isCrystalBonded s2 (0, Direction.ne) (1, Direction.ne)
#guard isCrystalBonded s2 (1, Direction.se) (0, Direction.se)  -- 逆順も OK

-- 同方角でない場合は結晶結合なし
#guard !isCrystalBonded s2 (0, Direction.ne) (1, Direction.se)

-- 隣接していない層（同層でも上下隣でもない）は結晶結合なし
private def s3 : Shape := Shape.triple Lc Lc Lc
#guard !isCrystalBonded s3 (0, Direction.ne) (2, Direction.ne)

-- 上層に結晶がない場合は結晶結合なし
#guard !isCrystalBonded s2mix (0, Direction.se) (1, Direction.se)  -- 下: crystal, 上: colored

-- ============================================================
-- IsCrystalBonded.symm
-- ============================================================

example {s : Shape} {p q : QuarterPos} (h : IsCrystalBonded s p q) : IsCrystalBonded s q p := h.symm

example : IsCrystalBonded s2 (0, Direction.ne) (1, Direction.ne) := by decide
example : IsCrystalBonded s2 (1, Direction.ne) (0, Direction.ne) :=
  IsCrystalBonded.symm (by decide : IsCrystalBonded s2 (0, Direction.ne) (1, Direction.ne))

-- ============================================================
-- IsCrystalBonded.rotateCW
-- ============================================================

example (s : Shape) (p q : QuarterPos) :
    IsCrystalBonded s.rotateCW p.rotateCW q.rotateCW ↔ IsCrystalBonded s p q :=
  IsCrystalBonded.rotateCW s p q

-- 具体: (0, NE) と (0, SE) → CW 後 (0, SE) と (0, SW)
#guard isCrystalBonded s1.rotateCW
  (QuarterPos.rotateCW (0, Direction.ne)) (QuarterPos.rotateCW (0, Direction.se))
#guard isCrystalBonded s1 (0, Direction.ne) (0, Direction.se)

-- 180° / CCW 系もチェーン経由で成立
example (s : Shape) (p q : QuarterPos) :
    IsCrystalBonded s.rotate180 p.rotateCW.rotateCW q.rotateCW.rotateCW ↔ IsCrystalBonded s p q :=
  IsCrystalBonded.rotate180 s p q

example (s : Shape) (p q : QuarterPos) :
    IsCrystalBonded s.rotateCCW p.rotateCW.rotateCW.rotateCW q.rotateCW.rotateCW.rotateCW ↔
      IsCrystalBonded s p q :=
  IsCrystalBonded.rotateCCW s p q

-- ============================================================
-- Prop/Bool 橋渡し
-- ============================================================

example (s : Shape) (p q : QuarterPos) :
    isCrystalBonded s p q = true ↔ IsCrystalBonded s p q := isCrystalBonded.iff s p q

end Test.Kernel.CrystalBond