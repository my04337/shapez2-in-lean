-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel

/-!
# S2IL.Operations.Settled

Settled (安定状態、B-3) 判定（Phase C re-scaffold 済み）。
Prop/Bool 二層規約（architecture §1.11）に従う。

## 公開 API

- `IsSettled : Shape → Prop`（Prop 層 primitive）
- `isSettled : Shape → Bool`（Bool 層、`decide` 派生）
- 回転・正規化による保存性
-/

namespace S2IL

/-- シェイプが安定状態（浮遊単位なし）であることを表す述語。 -/
axiom IsSettled : Shape → Prop

/-- `IsSettled` の決定可能性。 -/
axiom instDecidableIsSettled : DecidablePred IsSettled
noncomputable instance : DecidablePred IsSettled := instDecidableIsSettled

/-- `IsSettled` の Bool 版（派生）。 -/
noncomputable def isSettled (s : Shape) : Bool :=
  @decide (IsSettled s) (instDecidableIsSettled s)

/-- 橋渡し。 -/
theorem isSettled.iff (s : Shape) : isSettled s = true ↔ IsSettled s := by
  simp [isSettled]

namespace IsSettled

/-- `IsSettled` は CW 回転で保存される。 -/
axiom rotateCW {s : Shape} : IsSettled s → IsSettled (Shape.rotateCW s)

/-- `IsSettled` は 180° 回転で保存される（CW の系）。 -/
theorem rotate180 {s : Shape} (h : IsSettled s) : IsSettled s.rotate180 := by
  simp [Shape.rotate180_eq_rotateCW_rotateCW]
  exact IsSettled.rotateCW (IsSettled.rotateCW h)

/-- `IsSettled` は CCW 回転で保存される（CW の系）。 -/
theorem rotateCCW {s : Shape} (h : IsSettled s) : IsSettled s.rotateCCW := by
  simp [Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW]
  exact IsSettled.rotateCW (IsSettled.rotateCW (IsSettled.rotateCW h))

/-- 正規化は `IsSettled` を保存する。 -/
axiom normalize {s : Shape} :
    IsSettled s → IsSettled (Shape.normalize s)

end IsSettled

end S2IL
