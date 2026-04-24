-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.Types

/-!
# S2IL.Shape.GameConfig

ゲーム設定（最大レイヤ数など）と `Shape.truncate`。

## 公開 API

- `GameConfig` — ゲーム設定構造
- `GameConfig.vanilla4` / `vanilla5` / `stress8`
- `Shape.truncate` — レイヤ数制限に応じた切り詰め
-/

namespace S2IL

/-- ゲーム設定。 -/
axiom GameConfig : Type

namespace GameConfig
axiom maxLayers : GameConfig → Nat
axiom vanilla4 : GameConfig
axiom vanilla5 : GameConfig
axiom stress8 : GameConfig
end GameConfig

/-- シェイプをゲーム設定のレイヤ上限で切り詰める。 -/
axiom Shape.truncate : Shape → GameConfig → Shape

/-- 切り詰め後のレイヤ数は上限以下。 -/
axiom Shape.truncate_layerCount_le (s : Shape) (config : GameConfig) :
    (s.truncate config).layerCount ≤ config.maxLayers

/-- 既に上限以下のシェイプに対する切り詰めは恒等。 -/
axiom Shape.truncate_of_le (s : Shape) (config : GameConfig) :
    s.layerCount ≤ config.maxLayers → s.truncate config = s

/-- 切り詰めは冪等。 -/
axiom Shape.truncate_idempotent (s : Shape) (config : GameConfig) :
    (s.truncate config).truncate config = s.truncate config

end S2IL
