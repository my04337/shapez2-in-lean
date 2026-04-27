-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

/-!
# Test.Shape.GameConfig

`GameConfig` プリセットと `Shape.truncate` のテスト。
-/

import S2IL.Shape

open S2IL

namespace Test.Shape.GameConfig

-- ============================================================
-- presets
-- ============================================================

#guard GameConfig.vanilla4.maxLayers == 4
#guard GameConfig.vanilla5.maxLayers == 5
#guard GameConfig.stress8.maxLayers == 8

example : GameConfig.vanilla4.maxLayers > 0 := GameConfig.vanilla4.maxLayers_pos
example : GameConfig.stress8.maxLayers > 0 := GameConfig.stress8.maxLayers_pos

-- ============================================================
-- Shape.truncate
-- ============================================================

private def L : Layer :=
  Layer.mk (.crystal .red) (.crystal .green) (.crystal .blue) (.crystal .white)
private def s5 : Shape := [L, L, L, L, L]
private def s2 : Shape := [L, L]

-- 上限以下なら不変
example : Shape.truncate s2 GameConfig.vanilla4 = s2 :=
  Shape.truncate.of_le s2 GameConfig.vanilla4 (by decide)
example : Shape.truncate s5 GameConfig.vanilla5 = s5 :=
  Shape.truncate.of_le s5 GameConfig.vanilla5 (by decide)

-- 上限を超えると切り詰め
#guard (Shape.truncate s5 GameConfig.vanilla4).layerCount == 4
#guard (Shape.truncate s5 GameConfig.stress8).layerCount == 5

-- layerCount_le
example : (Shape.truncate s5 GameConfig.vanilla4).layerCount ≤ 4 :=
  Shape.truncate.layerCount_le s5 GameConfig.vanilla4

-- idempotent
example (s : Shape) (cfg : GameConfig) :
    Shape.truncate (Shape.truncate s cfg) cfg = Shape.truncate s cfg :=
  Shape.truncate.idempotent s cfg

end Test.Shape.GameConfig
