-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel

/-!
# S2IL.Operations.Common

操作共通ユーティリティ。

## 公開 API

- `Shape.truncate.rotateCW_comm` / `rotate180_comm` / `rotateCCW_comm`
  — `Shape.truncate` と回転の可換性
- `Shape.bottomLayer.rotateCW_comm` / `rotate180_comm` / `rotateCCW_comm`
  — `Shape.bottomLayer` と回転の可換性
-/

namespace S2IL

-- ============================================================
-- Shape.truncate と回転の可換性
-- ============================================================

/-- `truncate` は CW 回転と可換。 -/
theorem Shape.truncate.rotateCW_comm (s : Shape) (config : GameConfig) :
    (Shape.truncate s config).rotateCW = Shape.truncate s.rotateCW config := by
  show (s.take config.maxLayers).map Layer.rotateCW
        = (s.map Layer.rotateCW).take config.maxLayers
  rw [List.map_take]

/-- `truncate` は 180° 回転と可換（CW の系）。 -/
theorem Shape.truncate.rotate180_comm (s : Shape) (config : GameConfig) :
    (Shape.truncate s config).rotate180 = Shape.truncate s.rotate180 config := by
  simp [Shape.rotate180_eq_rotateCW_rotateCW, Shape.truncate.rotateCW_comm]

/-- `truncate` は CCW 回転と可換（CW の系）。 -/
theorem Shape.truncate.rotateCCW_comm (s : Shape) (config : GameConfig) :
    (Shape.truncate s config).rotateCCW = Shape.truncate s.rotateCCW config := by
  simp [Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW, Shape.truncate.rotateCW_comm]

-- ============================================================
-- Shape.bottomLayer と回転の可換性
-- ============================================================

/-- `bottomLayer` は CW 回転と可換: `s.rotateCW.bottomLayer = s.bottomLayer.rotateCW`。 -/
theorem Shape.bottomLayer.rotateCW_comm (s : Shape) :
    s.rotateCW.bottomLayer = s.bottomLayer.rotateCW := by
  cases s with
  | nil =>
    -- Layer.empty.rotateCW = Layer.empty
    show Layer.empty = Layer.empty.rotateCW
    funext d; simp [Layer.empty, Layer.rotateCW]
  | cons l _ =>
    rfl

/-- `bottomLayer` は 180° 回転と可換（CW の系）。 -/
theorem Shape.bottomLayer.rotate180_comm (s : Shape) :
    s.rotate180.bottomLayer = s.bottomLayer.rotate180 := by
  show (s.rotateCW.rotateCW).bottomLayer = s.bottomLayer.rotateCW.rotateCW
  rw [Shape.bottomLayer.rotateCW_comm, Shape.bottomLayer.rotateCW_comm]

/-- `bottomLayer` は CCW 回転と可換（CW の系）。 -/
theorem Shape.bottomLayer.rotateCCW_comm (s : Shape) :
    s.rotateCCW.bottomLayer = s.bottomLayer.rotateCCW := by
  show (s.rotateCW.rotateCW.rotateCW).bottomLayer = s.bottomLayer.rotateCW.rotateCW.rotateCW
  rw [Shape.bottomLayer.rotateCW_comm, Shape.bottomLayer.rotateCW_comm,
      Shape.bottomLayer.rotateCW_comm]

end S2IL
