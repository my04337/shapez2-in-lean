-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

/-!
# Test.Kernel.Cluster

`ClusterRel` / `clusterSet` の単体テスト。
反射律・対称律・1 ステップからの拡張・CW 等変性をスポット確認する。
-/

import S2IL.Kernel

open S2IL

namespace Test.Kernel.Cluster

private def Lc : Layer :=
  Layer.mk (.crystal .red) (.crystal .red) (.crystal .red) (.crystal .red)
private def Lone : Layer :=
  Layer.mk (.crystal .red) Quarter.empty Quarter.empty Quarter.empty
private def Lemp : Layer := Layer.empty

-- ============================================================
-- ClusterRel: 反射律
-- ============================================================

example (s : Shape) (p : QuarterPos) : ClusterRel s p p := ClusterRel.refl s p

-- ============================================================
-- ClusterRel: 1 ステップ拡張（IsBonded から ReflTransGen へ）
-- ============================================================

private def s1 : Shape := Shape.single Lc

-- (0, NE) と (0, SE) は結合するので同じクラスタ
example : ClusterRel s1 (0, .ne) (0, .se) := by
  apply Relation.ReflTransGen.single
  exact Or.inl (by decide : IsBondedInLayer s1 (0, .ne) (0, .se))

-- 推移性経由: NE → SE → SW
example : ClusterRel s1 (0, .ne) (0, .sw) := by
  apply Relation.ReflTransGen.head
    (Or.inl (by decide : IsBondedInLayer s1 (0, .ne) (0, .se)))
  exact Relation.ReflTransGen.single
    (Or.inl (by decide : IsBondedInLayer s1 (0, .se) (0, .sw)))

-- ============================================================
-- ClusterRel: 対称律
-- ============================================================

example {s : Shape} {p q : QuarterPos} (h : ClusterRel s p q) : ClusterRel s q p := h.symm

example : ClusterRel s1 (0, .se) (0, .ne) :=
  ClusterRel.symm (Relation.ReflTransGen.single
    (Or.inl (by decide : IsBondedInLayer s1 (0, .ne) (0, .se))))

-- ============================================================
-- ClusterRel: CW 等変性
-- ============================================================

example (s : Shape) (p q : QuarterPos) :
    ClusterRel s.rotateCW p.rotateCW q.rotateCW ↔ ClusterRel s p q :=
  ClusterRel.rotateCW s p q

-- ============================================================
-- clusterSet: メンバーシップ
-- ============================================================

example (s : Shape) (start q : QuarterPos) :
    q ∈ clusterSet s start ↔ q.1 < s.length ∧ ClusterRel s start q :=
  clusterSet.mem_iff s start q

-- 範囲外は属さない
example : (99, Direction.ne) ∉ clusterSet s1 (0, .ne) := by
  rw [clusterSet.mem_iff]; simp [s1, Shape.single]

-- 自分自身は属する（反射律 + 範囲内）
example : (0, Direction.ne) ∈ clusterSet s1 (0, .ne) := by
  rw [clusterSet.mem_iff]
  refine ⟨?_, ClusterRel.refl _ _⟩
  simp [s1, Shape.single]

-- 単独結晶: クラスタは自分のみ（隣接 SE が空のため拡張しない）
private def sOne : Shape := Shape.single Lone

example : (0, Direction.se) ∉ clusterSet sOne (0, .ne) := by
  rw [clusterSet.mem_iff]
  refine fun ⟨_, hRel⟩ => ?_
  -- ClusterRel sOne (0, .ne) (0, .se) は IsBonded がない
  have : ¬ IsBonded sOne (0, .ne) (0, .se) := by decide
  -- ReflTransGen から head を取り出す
  cases hRel with
  | refl => exact (by decide : ((0, Direction.ne) : QuarterPos) ≠ (0, Direction.se)) rfl
  | tail _ hb => exact this hb |>.elim

-- ============================================================
-- clusterSet: CW 等変性
-- ============================================================

example (s : Shape) (start : QuarterPos) :
    clusterSet s.rotateCW start.rotateCW =
      (clusterSet s start).image QuarterPos.rotateCW :=
  clusterSet.rotateCW_comm s start

end Test.Kernel.Cluster
