-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel

/-!
# Test.Kernel.CrystalBondCluster

`CrystalBondClusterRel` / `crystalBondClusterSet` の単体テスト。
反射律・対称律・1 ステップからの拡張・CW 等変性をスポット確認する。
-/

open S2IL

namespace Test.Kernel.CrystalBondCluster

private def Lc : Layer :=
  Layer.mk (.crystal .red) (.crystal .red) (.crystal .red) (.crystal .red)
private def Lone : Layer :=
  Layer.mk (.crystal .red) Quarter.empty Quarter.empty Quarter.empty

-- ============================================================
-- CrystalBondClusterRel: 反射律
-- ============================================================

example (s : Shape) (p : QuarterPos) : CrystalBondClusterRel s p p :=
  CrystalBondClusterRel.refl s p

-- ============================================================
-- CrystalBondClusterRel: 1 ステップ拡張（IsCrystalBonded から ReflTransGen へ）
-- ============================================================

private def s1 : Shape := Shape.single Lc

-- (0, NE) と (0, SE) は結晶結合するので同じ結晶結合クラスタ
example : CrystalBondClusterRel s1 (0, Direction.ne) (0, Direction.se) := by
  apply Relation.ReflTransGen.single
  exact Or.inl (by decide : IsCrystalBondedInLayer s1 (0, Direction.ne) (0, Direction.se))

-- 推移性経由: NE → SE → SW
example : CrystalBondClusterRel s1 (0, Direction.ne) (0, Direction.sw) := by
  exact Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single
      (Or.inl (by decide : IsCrystalBondedInLayer s1 (0, Direction.ne) (0, Direction.se))))
    (Relation.ReflTransGen.single
      (Or.inl (by decide : IsCrystalBondedInLayer s1 (0, Direction.se) (0, Direction.sw))))

-- ============================================================
-- CrystalBondClusterRel: 対称律
-- ============================================================

example {s : Shape} {p q : QuarterPos} (h : CrystalBondClusterRel s p q) :
    CrystalBondClusterRel s q p := h.symm

example : CrystalBondClusterRel s1 (0, Direction.se) (0, Direction.ne) :=
  CrystalBondClusterRel.symm (Relation.ReflTransGen.single
    (Or.inl (by decide : IsCrystalBondedInLayer s1 (0, Direction.ne) (0, Direction.se))))

-- ============================================================
-- CrystalBondClusterRel: CW 等変性
-- ============================================================

example (s : Shape) (p q : QuarterPos) :
    CrystalBondClusterRel s.rotateCW p.rotateCW q.rotateCW ↔ CrystalBondClusterRel s p q :=
  CrystalBondClusterRel.rotateCW s p q

-- ============================================================
-- crystalBondClusterSet: メンバーシップ
-- ============================================================

example (s : Shape) (start q : QuarterPos) :
    q ∈ crystalBondClusterSet s start ↔ q.1 < s.length ∧ CrystalBondClusterRel s start q :=
  crystalBondClusterSet.mem_iff s start q

-- 範囲外は属さない
example : (99, Direction.ne) ∉ crystalBondClusterSet s1 (0, Direction.ne) := by
  rw [crystalBondClusterSet.mem_iff]; simp [s1, Shape.single]

-- 自分自身は属する（反射律 + 範囲内）
example : (0, Direction.ne) ∈ crystalBondClusterSet s1 (0, Direction.ne) := by
  rw [crystalBondClusterSet.mem_iff]
  refine ⟨?_, CrystalBondClusterRel.refl _ _⟩
  simp [s1, Shape.single]

-- 単独結晶: 隣接 SE が空なので、1 ステップの結晶結合は発生しない。
private def sOne : Shape := Shape.single Lone

example : ¬ IsCrystalBonded sOne (0, Direction.ne) (0, Direction.se) := by decide

-- ============================================================
-- crystalBondClusterSet: CW 等変性
-- ============================================================

example (s : Shape) (start : QuarterPos) :
    crystalBondClusterSet s.rotateCW start.rotateCW =
      (crystalBondClusterSet s start).image QuarterPos.rotateCW :=
  crystalBondClusterSet.rotateCW_comm s start

end Test.Kernel.CrystalBondCluster