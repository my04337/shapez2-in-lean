-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.Shape

/-!
# GameConfig (ゲーム設定)

ゲームモードに応じたレイヤ数上限を管理する構造体。

## 概要

Shapez2 ではゲームモードによってシェイプのレイヤ数上限が異なる:
- バニラ (通常 / Normal・Hard): 4 レイヤ
- バニラ (Insane): 5 レイヤ
- Mod: 任意のレイヤ数

積層などの操作では一時的に上限を超えるレイヤが発生しうるため、
操作中は上限を無視し、操作完了後に `truncate` でレイヤ数を制限する。

`GameConfig` は型クラスではなく構造体として定義されており、
関数に明示的に渡す設計になっている。これにより同一ファイル内で
複数のゲームモードを同時に扱えるほか、任意のレイヤ数での
証明やテストが可能になる。

## プリセット

| プリセット | レイヤ数 | 用途 |
|---|---|---|
| `GameConfig.vanilla4` | 4 | 通常モード (Normal / Hard) |
| `GameConfig.vanilla5` | 5 | 高難度モード (Insane) |
| `GameConfig.stress8` | 8 | ストレステスト専用 |

## 使い方

```lean
-- 4レイヤモード
#eval (Shape.truncate someShape GameConfig.vanilla4).layerCount

-- 5レイヤモード
#eval (Shape.truncate someShape GameConfig.vanilla5).layerCount

-- カスタム (Mod 等)
def myConfig : GameConfig := GameConfig.mk 8 (by omega)
#eval (Shape.truncate someShape myConfig).layerCount
```
-/

/-- ゲームモードの設定。レイヤ数上限を定義する -/
structure GameConfig where
    /-- シェイプのレイヤ数上限 -/
    maxLayers : Nat
    /-- レイヤ数上限は 1 以上 -/
    maxLayers_pos : 0 < maxLayers

namespace GameConfig

/-- バニラ (通常 / Normal・Hard) の 4 レイヤ設定 -/
def vanilla4 : GameConfig where
    maxLayers := 4
    maxLayers_pos := by omega

/-- バニラ (Insane) の 5 レイヤ設定 -/
def vanilla5 : GameConfig where
    maxLayers := 5
    maxLayers_pos := by omega

/-- ストレステスト用の 8 レイヤ設定
    層ごとの力業 (`cases`) が不可能な規模で性質を検証するために使用する -/
def stress8 : GameConfig where
    maxLayers := 8
    maxLayers_pos := by omega

end GameConfig

namespace Shape

/-- `take` が非空リスト・正の長さで非空を保つ補助定理 -/
private theorem take_ne_nil_of_ne_nil_pos (l : List α) (n : Nat)
        (hl : l ≠ []) (hn : 0 < n) : l.take n ≠ [] := by
    intro h
    rw [List.take_eq_nil_iff] at h
    rcases h with rfl | rfl
    · omega
    · exact hl rfl

/-- シェイプのレイヤ数を `maxLayers` 以下に切り詰める。
    上限を超えた上位レイヤは除去される -/
def truncate (s : Shape) (config : GameConfig) : Shape where
    layers := s.layers.take config.maxLayers
    layers_ne := take_ne_nil_of_ne_nil_pos s.layers config.maxLayers s.layers_ne config.maxLayers_pos

/-- truncate 後のレイヤ数は maxLayers 以下 -/
theorem truncate_layerCount_le (s : Shape) (config : GameConfig) :
        (s.truncate config).layerCount ≤ config.maxLayers := by
    simp only [truncate, layerCount, List.length_take]
    omega

/-- レイヤ数が上限以下のシェイプに truncate を適用しても変わらない -/
theorem truncate_of_le (s : Shape) (config : GameConfig)
        (h : s.layerCount ≤ config.maxLayers) :
        s.truncate config = s := by
    ext1
    exact List.take_of_length_le h

/-- truncate は冪等である -/
theorem truncate_idempotent (s : Shape) (config : GameConfig) :
        (s.truncate config).truncate config = s.truncate config := by
    ext1; simp only [truncate, List.take_take, Std.le_refl, Nat.min_eq_left]

end Shape
