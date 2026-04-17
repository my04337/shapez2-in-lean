# GameConfig（ゲーム設定）の設計方針

`GameConfig` は**構造体**であり、レイヤ数上限を必要とする関数には**明示的に引数として渡す**。
型クラス (`class`) やデフォルト引数 (`inferInstance`) は使用しない。

```lean
-- ✅ 正しい使い方: 明示的に config を渡す
Shape.stack bottom top GameConfig.vanilla4
s.pinPush GameConfig.vanilla5

-- ❌ 避けるべき使い方: デフォルト引数に頼る
Shape.stack bottom top  -- config を省略しない
```

## プリセット

| 定義 | レイヤ数 | 用途 |
|---|---|---|
| `GameConfig.vanilla4` | 4 | 通常モード (Normal / Hard) |
| `GameConfig.vanilla5` | 5 | 高難度モード (Insane) |
| `GameConfig.stress8` | 8 | ストレステスト専用 |

カスタム設定は `GameConfig.mk n proof` で自由に構築できる。
