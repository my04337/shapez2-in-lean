# `mono` — 単調性補題による不等式分解

**カテゴリ**: 特化 | **定義元**: `Mathlib.Tactic.Monotonicity.mono` | **ソース**: Mathlib

## 概要
`mono` は `@[mono]` 属性が付与された単調性補題を用いて、不等式ゴールを分解するタクティク。`a + b ≤ c + d` のようなゴールを `a ≤ c` と `b ≤ d` に分解する。`gcongr` と類似するが、`mono` は Mathlib の古いスタイルの単調性フレームワークに基づく。

## ゴールパターン

**適用前**
```lean
⊢ a + b ≤ c + d
```

**適用後**
```lean
⊢ a ≤ c
⊢ b ≤ d
```

## 構文
```lean
mono                   -- @[mono] 補題で不等式を分解
mono left              -- 左側のみ分解
mono right             -- 右側のみ分解
mono with h            -- 追加仮定を指定
```

## 必須 import
```lean
import Mathlib.Tactic.Monotonicity
```

## オプション一覧
| 構文 | 意味 |
|---|---|
| `mono` | 自動で単調性補題を適用 |
| `mono left` | 左引数のみに着目 |
| `mono right` | 右引数のみに着目 |

## Pros
- 不等式の自動分解が直感的
- `@[mono]` で独自の単調性補題を登録可能
- left / right で分解方向を制御できる

## Cons
- `gcongr` の方が新しく、多くの場面で推奨される
- `@[mono]` 補題の登録数は `@[gcongr]` より少ない傾向
- 複雑な不等式では手動補題適用が必要になる場合がある
- Mathlib 依存

## コードサンプル

### サンプル 1: 加法の単調性
```lean
import Mathlib.Tactic.Monotonicity

example (a b c d : Nat) (h1 : a ≤ b) (h2 : c ≤ d) :
    a + c ≤ b + d := by
  mono
  -- mono が h1, h2 を自動的に使って全ゴールを閉じる
```

### サンプル 2: 部分的な分解
```lean
import Mathlib.Tactic.Monotonicity
import Mathlib.Data.Nat.Defs

example (a b c : Nat) (h : a ≤ b) :
    a + c ≤ b + c := by
  mono
  -- mono が h を自動的に使ってゴールを閉じる
```

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `gcongr` | 後継版 | より広範な不等式分解。新規コードでは推奨 |
| `congr` | 等式版 | 等式の構造的分解に |
| `positivity` | 正値性 | `0 ≤ expr` や `0 < expr` の証明に |

## 参照
- [Mathlib4 ドキュメント — mono](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Monotonicity/Basic.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
