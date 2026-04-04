# `gcongr` — 不等式の一般化合同分解

**カテゴリ**: 特化 | **定義元**: `Mathlib.Tactic.GCongr.tacticGcongr__` | **ソース**: Mathlib

## 概要
`gcongr` は不等式ゴールを構造的に分解する「一般化合同」タクティク。`congr` が等式を分解するのに対し、`gcongr` は `≤`, `<`, `⊆` 等の不等式を分解する。`@[gcongr]` 属性が付いた単調性補題を用いて、不等式の両辺を対応する部分に分解し、サブゴールを生成する。

## ゴールパターン

**適用前**
```lean
⊢ f a + g a ≤ f b + g b
```

**適用後**
```lean
⊢ f a ≤ f b
⊢ g a ≤ g b
```

## 構文
```lean
gcongr              -- 不等式を構造的に分解
gcongr _ + _        -- パターン指定で分解箇所を明示
gcongr with x       -- バインド変数名を指定
```

## 必須 import
```lean
import Mathlib.Tactic.GCongr
```

## オプション一覧
| 構文 | 意味 |
|---|---|
| `gcongr` | 自動で分解箇所を推定 |
| `gcongr _ + _` | 加算の両辺を分解 |
| `gcongr _ * _` | 乗算の両辺を分解 |
| `gcongr with x hx` | 量化子のバインド変数名を指定 |

## Pros
- 不等式の構造的分解を自動化
- `congr` と対称的な使用感で学習しやすい
- パターン指定で分解箇所を制御可能
- `@[gcongr]` で独自の単調性補題を登録可能

## Cons
- `@[gcongr]` 補題が未登録の演算には使えない
- 非単調な関数（例: 減算）では意図しない分解になりうる
- パターン指定なしだと過剰に分解される場合がある

## コードサンプル

### サンプル 1: 加法の不等式分解
```lean
import Mathlib.Tactic.GCongr

example (a b c d : Nat) (hab : a ≤ b) (hcd : c ≤ d) :
    a + c ≤ b + d := by
  gcongr
  -- gcongr が hab, hcd を自動的に使って全ゴールを閉じる
```

### サンプル 2: パターン指定
```lean
import Mathlib.Tactic.GCongr

example (a b c : Nat) (h : a ≤ b) (hc : 0 ≤ c) :
    a * c ≤ b * c := by
  gcongr
  -- gcongr が h, hc を自動的に使って全ゴールを閉じる
```

### サンプル 3: べき乗の不等式
```lean
import Mathlib.Tactic.GCongr

example (a b : Nat) (h : a ≤ b) (n : Nat) : a ^ n ≤ b ^ n := by
  gcongr
  -- gcongr が h を自動的に使ってゴールを閉じる
```

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `gcongr?` | 使用した補題を提案する |
| `gcongr_discharger` | `gcongr` の内部ディスチャージャをカスタマイズ |

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `congr` | 等式合同 | 等式の構造分解に |
| `mono` | 単調性 | `@[mono]` 補題ベースの単調性証明 |
| `rel` | 関係分解 | 関係的推論に |
| `positivity` | 正値性 | `0 ≤ expr` や `0 < expr` の証明に |

## 参照
- [Mathlib4 ドキュメント — gcongr](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/GCongr/Core.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
