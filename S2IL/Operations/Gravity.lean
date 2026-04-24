-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel
import S2IL.Operations.Settled

/-!
# S2IL.Operations.Gravity

落下機構 (B-1)。構造結合と接地判定による浮遊単位の検出と落下。

## 公開 API

- `gravity : Shape → Option Shape` — メイン落下処理
- `gravity_isSettled` — 出力は `IsSettled`
- `gravity_rotateCW_comm` — CW 等変性

## 単一チェーン原則

CW 等変性のみ axiom、180° / CCW は 1 行系。

## 制約

- Wave Gravity モデルにより `layerCount ≤ 5` 制約は解消済み
  （falling.md §7.6 / §10.4 参照）
- Phase D で `gravity` の終端性・GroundingMono 系統を整備予定
-/

namespace S2IL

axiom Shape.gravity : Shape → Option Shape

/-- `gravity` の出力（存在する場合）は `IsSettled`。 -/
axiom Shape.gravity_isSettled {s s' : Shape} :
    s.gravity = some s' → IsSettled s'

/-- `gravity` と CW 回転は可換。 -/
axiom Shape.gravity_rotateCW_comm (s : Shape) :
    (s.gravity).map Shape.rotateCW = s.rotateCW.gravity

/-- `gravity` と 180° 回転は可換（CW の系）。 -/
theorem Shape.gravity_rotate180_comm (s : Shape) :
    (s.gravity).map Shape.rotate180 = s.rotate180.gravity := by
  show (s.gravity).map (fun x => x.rotateCW.rotateCW) = s.rotateCW.rotateCW.gravity
  rw [show (fun x : Shape => x.rotateCW.rotateCW) =
        Shape.rotateCW ∘ Shape.rotateCW from rfl,
      ← Option.map_map, Shape.gravity_rotateCW_comm,
      Shape.gravity_rotateCW_comm]

/-- `gravity` と CCW 回転は可換（CW の系）。 -/
theorem Shape.gravity_rotateCCW_comm (s : Shape) :
    (s.gravity).map Shape.rotateCCW = s.rotateCCW.gravity := by
  show (s.gravity).map (fun x => x.rotateCW.rotateCW.rotateCW)
        = s.rotateCW.rotateCW.rotateCW.gravity
  rw [show (fun x : Shape => x.rotateCW.rotateCW.rotateCW) =
        Shape.rotateCW ∘ Shape.rotateCW ∘ Shape.rotateCW from rfl,
      ← Option.map_map, ← Option.map_map,
      Shape.gravity_rotateCW_comm, Shape.gravity_rotateCW_comm,
      Shape.gravity_rotateCW_comm]

end S2IL
