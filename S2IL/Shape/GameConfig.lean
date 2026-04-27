-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.Types

/-!
# S2IL.Shape.GameConfig

ゲーム設定（最大レイヤ数）と `Shape.truncate`。Phase C 完了形。

## 公開 API

- `GameConfig` — `structure` で `maxLayers : Nat` と `0 < maxLayers` の証明を保持
- `GameConfig.vanilla4` / `vanilla5` / `stress8` — 具体プリセット
- `Shape.truncate` — `List.take` ベースで上限以下に切り詰める
- 関連定理: `truncate.layerCount_le` / `truncate.of_le` / `truncate.idempotent`
-/

namespace S2IL

/-- ゲームモードの設定。レイヤ数上限を保持する。 -/
structure GameConfig where
  /-- レイヤ数上限。 -/
  maxLayers : Nat
  /-- 上限は 1 以上。 -/
  maxLayers_pos : 0 < maxLayers

namespace GameConfig

/-- バニラ通常モード（Normal / Hard）の 4 レイヤ設定。 -/
def vanilla4 : GameConfig := ⟨4, by omega⟩

/-- バニラ Insane モードの 5 レイヤ設定。 -/
def vanilla5 : GameConfig := ⟨5, by omega⟩

/-- ストレステスト用の 8 レイヤ設定。 -/
def stress8 : GameConfig := ⟨8, by omega⟩

end GameConfig

namespace Shape

/-- シェイプを `config.maxLayers` 以下に切り詰める。
    0 層を許容するため `List.take` で十分。 -/
def truncate (s : Shape) (config : GameConfig) : Shape :=
  s.take config.maxLayers

/-- 切り詰め後のレイヤ数は上限以下。 -/
@[simp] theorem truncate.layerCount_le (s : Shape) (config : GameConfig) :
    (truncate s config).layerCount ≤ config.maxLayers := by
  simp [truncate, layerCount, List.length_take]
  omega

/-- 上限以下のシェイプに対する切り詰めは恒等。 -/
theorem truncate.of_le (s : Shape) (config : GameConfig)
    (h : s.layerCount ≤ config.maxLayers) :
    truncate s config = s := by
  simp [truncate, layerCount] at *
  exact List.take_of_length_le h

/-- 切り詰めは冪等。 -/
@[simp] theorem truncate.idempotent (s : Shape) (config : GameConfig) :
    truncate (truncate s config) config = truncate s config := by
  simp [truncate, List.take_take]

end Shape

end S2IL
