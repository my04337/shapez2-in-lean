# `rify` — 整数/自然数ゴールを実数ゴールに変換

**カテゴリ**: キャスト | **定義元**: `Mathlib.Tactic.Rify.rify` | **ソース**: Mathlib

## 概要
`rify` は `Nat` や `Int` 上のゴール・仮定を `ℝ`（実数）へキャストするタクティク。実数上の `nlinarith` / `polyrith` / `norm_num` を使いたい場合に利用する。`@[rify_simps]` 属性の補題を使ってキャストを正規化する。`zify` / `qify` と同様のインターフェースを持つ。

## ゴールパターン

**適用前**
```lean
n : Nat
⊢ n * n ≥ 0
```

**適用後**
```lean
n : Nat
⊢ (↑n : ℝ) * ↑n ≥ 0
```

## 構文
```lean
rify                    -- ゴールを ℤ/ℕ → ℝ に変換
rify at h               -- 仮定 h を変換
rify at h ⊢             -- 仮定 h とゴール両方
rify at *               -- 全仮定とゴールを変換
rify [lemma]            -- 追加の補題を使用して simp
```

## 必須 import
```lean
import Mathlib.Tactic.Rify
```

## オプション一覧
| 構文 | 意味 |
|---|---|
| `at h` | 仮定 h に適用 |
| `at *` | 全仮定とゴールに適用 |
| `[h₁, h₂]` | 追加の simp 補題を使用 |

## Pros
- `nlinarith` / `polyrith` 等の実数向けタクティクと組み合わせやすい
- 平方根や指数を含む証明で実数へのキャストが自然
- `zify` / `qify` と同一のインターフェースで学習コストが低い

## Cons
- Mathlib 依存
- 多くの場合 `zify` + `omega` で十分であり、`rify` は不要
- 実数特有の完備性を使わない場合はキャストが冗長

## コードサンプル

### サンプル 1: rify + nlinarith
```lean
import Mathlib.Tactic.Rify
import Mathlib.Tactic.Linarith

example (n : Nat) : n ^ 2 + n ≥ n := by
  rify
  -- ⊢ (↑n : ℝ) ^ 2 + ↑n ≥ ↑n
  nlinarith [sq_nonneg (↑n : ℝ)]
```

### サンプル 2: 不等式の仮定変換
```lean
import Mathlib.Tactic.Rify
import Mathlib.Tactic.Linarith

example (a b : Nat) (h : a ≤ b) : (↑a : ℝ) ≤ ↑b := by
  rify at h
  -- h : (↑a : ℝ) ≤ ↑b ⊢ (↑a : ℝ) ≤ ↑b
  exact h
```

### サンプル 3: zify と rify の使い分け
```lean
import Mathlib.Tactic.Rify

example (n : Nat) : (↑(n + 1) : ℝ) > 0 := by
  rify
  -- ⊢ (↑n : ℝ) + 1 > 0
  positivity
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `zify` | ℕ → ℤ | 整数で十分な場合（Nat 減算回避） |
| `qify` | ℤ/ℕ → ℚ | 有理数で十分な場合 |
| `push_cast` | キャスト分配 | 手動でキャストの位置を制御 |
| `norm_cast` | キャスト正規化 | キャスト等式の正規化 |
| `nlinarith` | 非線形算術 | `rify` 後に非線形不等式を閉じる |
| `positivity` | 非負/正値 | `rify` 後に正値性を示す |

## 参照
- [Mathlib4 ドキュメント — Rify](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Rify.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
