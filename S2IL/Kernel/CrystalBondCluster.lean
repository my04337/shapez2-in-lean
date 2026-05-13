-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape
import S2IL.Kernel.Transform
import S2IL.Kernel.CrystalBond
import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Image

/-!
# S2IL.Kernel.CrystalBondCluster

結晶結合クラスタ表現。
Mathlib `Relation.ReflTransGen` を関係層として利用する（architecture §1.10）。

## 公開 API

- `CrystalBondClusterRel`               — 結晶結合関係の反射推移閉包（`Relation.ReflTransGen IsCrystalBonded`）
- `CrystalBondClusterRel.refl`          — 反射律（`ReflTransGen` 由来の再エクスポート）
- `CrystalBondClusterRel.symm`          — 対称律（`IsCrystalBonded.symm` を経由）
- `CrystalBondClusterRel.rotateCW`      — Prop 層 CW 等変性（Iff）
- `crystalBondClusterSet`               — 結晶結合クラスタの Finset 表現（noncomputable, Classical 経由）
- `crystalBondClusterSet.rotateCW_comm` — Finset CW 等変性

## 設計根拠

- Mathlib の `Relation.ReflTransGen` で実装し、自前 axiom を持たない。
- 等変性は Finset 等式のみで述べる（List 等式は順序依存のため禁止）。
- `crystalBondClusterList` / `allCrystalBondClusters` 等の計算的 List API は 今後 MAM/Shatter が必要になってから追加する。

## Internal

- `S2IL.Kernel.Internal.CrystalBondClusterImpl` — `crystalBondClusterList` の実装（今後追加予定）
-/

namespace S2IL

-- ============================================================
-- CrystalBondClusterRel: IsCrystalBonded の反射推移閉包
-- ============================================================

/-- 結晶結合クラスタ関係: 結晶結合の反射推移閉包。 -/
def CrystalBondClusterRel (s : Shape) : QuarterPos → QuarterPos → Prop :=
  Relation.ReflTransGen (IsCrystalBonded s)

theorem CrystalBondClusterRel.refl (s : Shape) (p : QuarterPos) :
    CrystalBondClusterRel s p p :=
  Relation.ReflTransGen.refl

theorem CrystalBondClusterRel.symm {s : Shape} {p q : QuarterPos}
    (h : CrystalBondClusterRel s p q) : CrystalBondClusterRel s q p := by
  unfold CrystalBondClusterRel at *
  -- IsCrystalBonded は対称なので ReflTransGen も対称。
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbond ih =>
      exact Relation.ReflTransGen.head hbond.symm ih

-- ============================================================
-- CW 等変性（Prop 層）
-- ============================================================

/-- `CrystalBondClusterRel` の CW 等変性。Iff 形で述べる。 -/
theorem CrystalBondClusterRel.rotateCW (s : Shape) (p q : QuarterPos) :
    CrystalBondClusterRel s.rotateCW p.rotateCW q.rotateCW ↔
      CrystalBondClusterRel s p q := by
  unfold CrystalBondClusterRel
  constructor
  · -- backward direction: lift along rotateCCW
    intro h
    have hlift :
        Relation.ReflTransGen (IsCrystalBonded s) p.rotateCW.rotateCCW q.rotateCW.rotateCCW :=
      h.lift QuarterPos.rotateCCW (fun a b hab => by
        -- IsCrystalBonded s.rotateCW a b → IsCrystalBonded s a.rotateCCW b.rotateCCW
        have key : IsCrystalBonded s.rotateCW a.rotateCCW.rotateCW b.rotateCCW.rotateCW
                    ↔ IsCrystalBonded s a.rotateCCW b.rotateCCW :=
          IsCrystalBonded.rotateCW s a.rotateCCW b.rotateCCW
        have := key.mp (by simpa [QuarterPos.rotateCW_rotateCCW] using hab)
        exact this)
    simpa [QuarterPos.rotateCCW_rotateCW] using hlift
  · -- forward direction: lift along rotateCW
    intro h
    exact h.lift QuarterPos.rotateCW (fun a b hab =>
      (IsCrystalBonded.rotateCW s a b).mpr hab)

/-- `CrystalBondClusterRel` の 180° 等変性（CW の 2 段重ね系）。 -/
theorem CrystalBondClusterRel.rotate180 (s : Shape) (p q : QuarterPos) :
    CrystalBondClusterRel s.rotateCW.rotateCW p.rotateCW.rotateCW q.rotateCW.rotateCW ↔
      CrystalBondClusterRel s p q := by
  rw [CrystalBondClusterRel.rotateCW, CrystalBondClusterRel.rotateCW]

/-- `CrystalBondClusterRel` の CCW 等変性（CW の 3 段重ね系）。 -/
theorem CrystalBondClusterRel.rotateCCW (s : Shape) (p q : QuarterPos) :
    CrystalBondClusterRel s.rotateCW.rotateCW.rotateCW p.rotateCW.rotateCW.rotateCW
        q.rotateCW.rotateCW.rotateCW ↔ CrystalBondClusterRel s p q := by
  rw [CrystalBondClusterRel.rotateCW, CrystalBondClusterRel.rotateCW,
    CrystalBondClusterRel.rotateCW]

-- ============================================================
-- Finset 表現（noncomputable）
-- ============================================================

/-- `start` を含む結晶結合クラスタの Finset 表現。`allValid` を carrier とした filter。 -/
noncomputable def crystalBondClusterSet (s : Shape) (start : QuarterPos) : Finset QuarterPos :=
  letI := Classical.decPred (CrystalBondClusterRel s start)
  (QuarterPos.allValid s).toFinset.filter (CrystalBondClusterRel s start)

theorem crystalBondClusterSet.mem_iff (s : Shape) (start q : QuarterPos) :
    q ∈ crystalBondClusterSet s start ↔ q.1 < s.length ∧ CrystalBondClusterRel s start q := by
  classical
  unfold crystalBondClusterSet
  simp [Finset.mem_filter, List.mem_toFinset, QuarterPos.mem_allValid]

/-- 結晶結合クラスタ集合の CW 等変性（Finset 等式）。 -/
theorem crystalBondClusterSet.rotateCW_comm (s : Shape) (start : QuarterPos) :
    crystalBondClusterSet s.rotateCW start.rotateCW =
      (crystalBondClusterSet s start).image QuarterPos.rotateCW := by
  classical
  ext q
  rw [crystalBondClusterSet.mem_iff, Finset.mem_image]
  constructor
  · rintro ⟨hMem, hRel⟩
    refine ⟨q.rotateCCW, ?_, QuarterPos.rotateCW_rotateCCW q⟩
    rw [crystalBondClusterSet.mem_iff]
    refine ⟨?_, ?_⟩
    · -- q.rotateCCW.1 = q.1 < s.rotateCW.length = s.length
      have : q.rotateCCW.1 = q.1 := QuarterPos.rotateCCW_fst q
      rw [this]
      simpa [Shape.rotateCW] using hMem
    · -- CrystalBondClusterRel s start q.rotateCCW
      have hRel' : CrystalBondClusterRel s.rotateCW start.rotateCW q.rotateCCW.rotateCW := by
        simpa [QuarterPos.rotateCW_rotateCCW] using hRel
      exact (CrystalBondClusterRel.rotateCW s start q.rotateCCW).mp hRel'
  · rintro ⟨p, hp, rfl⟩
    rw [crystalBondClusterSet.mem_iff] at hp
    obtain ⟨hpMem, hpRel⟩ := hp
    refine ⟨?_, ?_⟩
    · -- p.rotateCW.1 = p.1 < s.length = s.rotateCW.length
      have : p.rotateCW.1 = p.1 := rfl
      rw [this]
      simpa [Shape.rotateCW] using hpMem
    · exact (CrystalBondClusterRel.rotateCW s start p).mpr hpRel

end S2IL