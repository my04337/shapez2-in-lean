-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel

/-!
# S2IL.Operations.Settled

Settled (安定状態、B-3) 判定。浮遊単位が存在しないことで特徴づけられる。

## 公開 API

- `IsSettled : Shape → Prop`
- `isSettled : Shape → Bool`（決定可能版）
- 回転・正規化による保存性
-/

namespace S2IL

/-- シェイプが安定状態（浮遊単位なし）であることを表す述語。 -/
axiom IsSettled : Shape → Prop

/-- `IsSettled` の決定可能バージョン。 -/
axiom isSettled : Shape → Bool

axiom isSettled_iff (s : Shape) : isSettled s = true ↔ IsSettled s

namespace IsSettled

/-- `IsSettled` は CW 回転で保存される。 -/
axiom rotateCW {s : Shape} : IsSettled s → IsSettled s.rotateCW

/-- `IsSettled` は 180° 回転で保存される（CW の系）。 -/
theorem rotate180 {s : Shape} (h : IsSettled s) : IsSettled s.rotate180 := by
  simp [Shape.rotate180_eq_rotateCW_rotateCW]
  exact IsSettled.rotateCW (IsSettled.rotateCW h)

/-- `IsSettled` は CCW 回転で保存される（CW の系）。 -/
theorem rotateCCW {s : Shape} (h : IsSettled s) : IsSettled s.rotateCCW := by
  simp [Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW]
  exact IsSettled.rotateCW (IsSettled.rotateCW (IsSettled.rotateCW h))

/-- 正規化は `IsSettled` を保存する。 -/
axiom normalize {s s' : Shape} :
    s.normalize = some s' → IsSettled s → IsSettled s'

end IsSettled

end S2IL
