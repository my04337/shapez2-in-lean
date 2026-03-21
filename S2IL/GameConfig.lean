-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.Shape

/-!
# GameConfig (ゲーム設定)

ゲームモードに応じたレイヤ数上限を管理する型クラス。

## 概要

Shapez2 ではゲームモードによってシェイプのレイヤ数上限が異なる:
- バニラ (通常): 4 レイヤ
- バニラ (5レイヤモード): 5 レイヤ
- Mod: 任意のレイヤ数

積層などの操作では一時的に上限を超えるレイヤが発生しうるため、
操作中は上限を無視し、操作完了後に `truncate` でレイヤ数を制限する。

## 使い方

```lean
-- デフォルト: 4レイヤ
#eval (Shape.truncate (config := GameConfig.vanilla4) someShape).layerCount

-- 5レイヤモード
#eval (Shape.truncate (config := GameConfig.vanilla5) someShape).layerCount
```
-/

/-- ゲームモードの設定。レイヤ数上限を定義する -/
class GameConfig where
    /-- シェイプのレイヤ数上限 -/
    maxLayers : Nat
    /-- レイヤ数上限は 1 以上 -/
    maxLayers_pos : 0 < maxLayers

namespace GameConfig

/-- バニラ (通常) の 4 レイヤ設定 -/
instance vanilla4 : GameConfig where
    maxLayers := 4
    maxLayers_pos := by omega

/-- バニラの 5 レイヤ設定 -/
def vanilla5 : GameConfig where
    maxLayers := 5
    maxLayers_pos := by omega

end GameConfig

namespace Shape

/-- シェイプのレイヤ数を `maxLayers` 以下に切り詰める。
    上限を超えた上位レイヤは除去される -/
def truncate (s : Shape) (config : GameConfig) : Shape :=
    let kept := s.upper.take (config.maxLayers - 1)
    ⟨s.bottom, kept⟩

/-- truncate 後のレイヤ数は maxLayers 以下 -/
theorem truncate_layerCount_le (s : Shape) (config : GameConfig) :
        (s.truncate config).layerCount ≤ config.maxLayers := by
    simp [truncate, layerCount]
    have h := config.maxLayers_pos
    omega

/-- レイヤ数が上限以下のシェイプに truncate を適用しても変わらない -/
theorem truncate_of_le (s : Shape) (config : GameConfig)
        (h : s.layerCount ≤ config.maxLayers) :
        s.truncate config = s := by
    simp [truncate, layerCount] at *
    rw [List.take_of_length_le]
    omega

/-- truncate は冪等である -/
theorem truncate_idempotent (s : Shape) (config : GameConfig) :
        (s.truncate config).truncate config = s.truncate config := by
    apply truncate_of_le
    exact truncate_layerCount_le s config

end Shape
