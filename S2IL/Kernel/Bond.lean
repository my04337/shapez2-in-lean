-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape
import S2IL.Kernel.Cluster
import S2IL.Kernel.Transform

/-!
# S2IL.Kernel.Bond

結晶結合条件（Phase C re-scaffold 済み）。
Prop/Bool 二層規約（architecture §1.11）に従い `IsBonded` を Prop 層 primitive、
`isBonded` を Bool 層派生とする。

## 公開 API

- `IsBonded` / `IsBondedInLayer` / `IsBondedCrossLayer` — Prop 層
- `isBonded` / `isBondedInLayer` / `isBondedCrossLayer` — Bool 層（`decide`）
- `IsBonded.symm` / `IsBonded.rotateCW` — 対称性・CW 等変性
- `ClusterRel` — `Relation.ReflTransGen IsBonded` による到達可能性

## Internal

- `S2IL.Kernel.Internal.BondImpl`         — 結合判定の実装補助
- `S2IL.Kernel.Internal.Rotate180Lemmas` — 回転と setDir/getDir の可換性系
-/

namespace S2IL

/-- 同レイヤ内結合（Prop 層）。 -/
axiom IsBondedInLayer : Shape → QuarterPos → QuarterPos → Prop

/-- 上下レイヤ間結合（Prop 層）。 -/
axiom IsBondedCrossLayer : Shape → QuarterPos → QuarterPos → Prop

/-- 結合関係（Prop 層）: 同レイヤ内結合 ∨ 上下レイヤ間結合。 -/
axiom IsBonded : Shape → QuarterPos → QuarterPos → Prop

/-- 決定可能性。 -/
axiom instDecidableIsBonded (s : Shape) (p q : QuarterPos) :
    Decidable (IsBonded s p q)
noncomputable instance (s : Shape) (p q : QuarterPos) : Decidable (IsBonded s p q) :=
  instDecidableIsBonded s p q

/-- Bool 層（派生）。 -/
noncomputable def isBonded (s : Shape) (p q : QuarterPos) : Bool :=
  @decide (IsBonded s p q) (instDecidableIsBonded s p q)

/-- 橋渡し。 -/
theorem isBonded.iff (s : Shape) (p q : QuarterPos) :
    isBonded s p q = true ↔ IsBonded s p q := by
  simp [isBonded]

/-- 対称性。 -/
axiom IsBonded.symm (s : Shape) (p q : QuarterPos) :
    IsBonded s p q → IsBonded s q p

/-- CW 等変性。 -/
axiom IsBonded.rotateCW (s : Shape) (p q : QuarterPos) :
    IsBonded s.rotateCW p.rotateCW q.rotateCW ↔ IsBonded s p q

-- NOTE: `IsBonded.rotate180` / `IsBonded.rotateCCW` は Phase C で
-- 1 行系として追加する。

/-- クラスタ関係: `IsBonded` の反射推移閉包。 -/
def ClusterRel (s : Shape) (p q : QuarterPos) : Prop :=
  Relation.ReflTransGen (IsBonded s) p q

end S2IL
