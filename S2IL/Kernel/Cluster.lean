-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape
import S2IL.Kernel.Transform
import S2IL.Kernel.Bond
import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Image

/-!
# S2IL.Kernel.Cluster

クラスタ表現（Phase C re-scaffold 済み, axiom-free）。
Mathlib `Relation.ReflTransGen` を関係層として利用する（architecture §1.10）。

## 公開 API

- `ClusterRel`               — 結合関係の反射推移閉包（`Relation.ReflTransGen IsBonded`）
- `ClusterRel.refl`          — 反射律（`ReflTransGen` 由来の再エクスポート）
- `ClusterRel.symm`          — 対称律（`IsBonded.symm` を経由）
- `ClusterRel.rotateCW`      — Prop 層 CW 等変性（Iff）
- `clusterSet`               — クラスタの Finset 表現（noncomputable, Classical 経由）
- `clusterSet.rotateCW_comm` — Finset CW 等変性

## 設計根拠

- 旧 `genericBfs` / `GenericReachable` は廃止。Mathlib の `Relation.ReflTransGen` で
  完全に代用し、自前 axiom を持たない。
- 等変性は Finset 等式のみで述べる（List 等式は順序依存のため禁止）。
- `clusterList` / `allClusters` 等の計算的 List API は Phase D で MAM/Shatter が必要に
  なってから追加する。

## Internal

- `S2IL.Kernel.Internal.ClusterImpl` — `clusterList` の実装（Phase D で追加予定）
-/

namespace S2IL

-- ============================================================
-- ClusterRel: IsBonded の反射推移閉包
-- ============================================================

/-- クラスタ関係: 結合の反射推移閉包。 -/
def ClusterRel (s : Shape) : QuarterPos → QuarterPos → Prop :=
  Relation.ReflTransGen (IsBonded s)

theorem ClusterRel.refl (s : Shape) (p : QuarterPos) : ClusterRel s p p :=
  Relation.ReflTransGen.refl

theorem ClusterRel.symm {s : Shape} {p q : QuarterPos}
    (h : ClusterRel s p q) : ClusterRel s q p := by
  unfold ClusterRel at *
  -- IsBonded は対称なので ReflTransGen も対称。
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbond ih =>
      exact Relation.ReflTransGen.head hbond.symm ih

-- ============================================================
-- CW 等変性（Prop 層）
-- ============================================================

/-- `ClusterRel` の CW 等変性。Iff 形で述べる。 -/
theorem ClusterRel.rotateCW (s : Shape) (p q : QuarterPos) :
    ClusterRel s.rotateCW p.rotateCW q.rotateCW ↔ ClusterRel s p q := by
  unfold ClusterRel
  constructor
  · -- backward direction: lift along rotateCCW
    intro h
    have hlift :
        Relation.ReflTransGen (IsBonded s) p.rotateCW.rotateCCW q.rotateCW.rotateCCW :=
      h.lift QuarterPos.rotateCCW (fun a b hab => by
        -- IsBonded s.rotateCW a b → IsBonded s a.rotateCCW b.rotateCCW
        have key : IsBonded s.rotateCW a.rotateCCW.rotateCW b.rotateCCW.rotateCW
                    ↔ IsBonded s a.rotateCCW b.rotateCCW :=
          IsBonded.rotateCW s a.rotateCCW b.rotateCCW
        have := key.mp (by simpa [QuarterPos.rotateCW_rotateCCW] using hab)
        exact this)
    simpa [QuarterPos.rotateCCW_rotateCW] using hlift
  · -- forward direction: lift along rotateCW
    intro h
    exact h.lift QuarterPos.rotateCW (fun a b hab =>
      (IsBonded.rotateCW s a b).mpr hab)

/-- `ClusterRel` の 180° 等変性（CW を 2 段重ねた系）。 -/
theorem ClusterRel.rotateCW_two (s : Shape) (p q : QuarterPos) :
    ClusterRel s.rotateCW.rotateCW p.rotateCW.rotateCW q.rotateCW.rotateCW ↔
      ClusterRel s p q := by
  rw [ClusterRel.rotateCW, ClusterRel.rotateCW]

/-- `ClusterRel` の CCW 等変性（CW を 3 段重ねた系）。 -/
theorem ClusterRel.rotateCW_three (s : Shape) (p q : QuarterPos) :
    ClusterRel s.rotateCW.rotateCW.rotateCW p.rotateCW.rotateCW.rotateCW
        q.rotateCW.rotateCW.rotateCW ↔ ClusterRel s p q := by
  rw [ClusterRel.rotateCW, ClusterRel.rotateCW, ClusterRel.rotateCW]

-- ============================================================
-- Finset 表現（noncomputable）
-- ============================================================

/-- `start` を含むクラスタの Finset 表現。`allValid` を carrier とした filter。 -/
noncomputable def clusterSet (s : Shape) (start : QuarterPos) : Finset QuarterPos :=
  letI := Classical.decPred (ClusterRel s start)
  (QuarterPos.allValid s).toFinset.filter (ClusterRel s start)

theorem clusterSet.mem_iff (s : Shape) (start q : QuarterPos) :
    q ∈ clusterSet s start ↔ q.1 < s.length ∧ ClusterRel s start q := by
  classical
  unfold clusterSet
  simp [Finset.mem_filter, List.mem_toFinset, QuarterPos.mem_allValid]

/-- クラスタ集合の CW 等変性（Finset 等式）。 -/
theorem clusterSet.rotateCW_comm (s : Shape) (start : QuarterPos) :
    clusterSet s.rotateCW start.rotateCW =
      (clusterSet s start).image QuarterPos.rotateCW := by
  classical
  ext q
  rw [clusterSet.mem_iff, Finset.mem_image]
  constructor
  · rintro ⟨hMem, hRel⟩
    refine ⟨q.rotateCCW, ?_, QuarterPos.rotateCW_rotateCCW q⟩
    rw [clusterSet.mem_iff]
    refine ⟨?_, ?_⟩
    · -- q.rotateCCW.1 = q.1 < s.rotateCW.length = s.length
      have : q.rotateCCW.1 = q.1 := QuarterPos.rotateCCW_fst q
      rw [this]
      simpa [Shape.rotateCW] using hMem
    · -- ClusterRel s start q.rotateCCW
      have hRel' : ClusterRel s.rotateCW start.rotateCW q.rotateCCW.rotateCW := by
        simpa [QuarterPos.rotateCW_rotateCCW] using hRel
      exact (ClusterRel.rotateCW s start q.rotateCCW).mp hRel'
  · rintro ⟨p, hp, rfl⟩
    rw [clusterSet.mem_iff] at hp
    obtain ⟨hpMem, hpRel⟩ := hp
    refine ⟨?_, ?_⟩
    · -- p.rotateCW.1 = p.1 < s.length = s.rotateCW.length
      have : p.rotateCW.1 = p.1 := rfl
      rw [this]
      simpa [Shape.rotateCW] using hpMem
    · exact (ClusterRel.rotateCW s start p).mpr hpRel

end S2IL
