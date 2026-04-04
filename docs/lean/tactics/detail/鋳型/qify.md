# `qify` — 整数/自然数ゴールを有理数ゴールに変換

**カテゴリ**: キャスト | **定義元**: `Mathlib.Tactic.Qify.qify` | **ソース**: Mathlib

## 概要
`qify` は `Nat` や `Int` 上のゴール・仮定を `ℚ`（有理数）へキャストするタクティク。整数除算の切り捨てが問題になる場合や、有理数上の `field_simp` / `ring` を使いたい場合に `qify` で有理数に持ち上げる。`@[qify_simps]` 属性の補題を使ってキャストを正規化する。

## ゴールパターン

**適用前**
```lean
a b : Int
h : b ≠ 0
⊢ a / b * b + a % b = a
```

**適用後**
```lean
a b : Int
h : (↑b : ℚ) ≠ 0
⊢ ↑a / ↑b * ↑b + ↑a % ↑b = ↑a
```

## 構文
```lean
qify                    -- ゴールを ℤ/ℕ → ℚ に変換
qify at h               -- 仮定 h を変換
qify at h ⊢             -- 仮定 h とゴール両方
qify at *               -- 全仮定とゴールを変換
qify [lemma]            -- 追加の補題を使用して simp
```

## 必須 import
```lean
import Mathlib.Tactic.Qify
```

## オプション一覧
| 構文 | 意味 |
|---|---|
| `at h` | 仮定 h に適用 |
| `at *` | 全仮定とゴールに適用 |
| `[h₁, h₂]` | 追加の simp 補題を使用 |

## Pros
- 整数除算の切り捨て問題を回避できる
- `field_simp` / `ring` で有理数上の等式を閉じられる
- `zify` と組み合わせて `ℕ → ℤ → ℚ` の段階的キャストも可能

## Cons
- Mathlib 依存
- 有理数まで持ち上げる必要がない場合は `zify` で十分
- キャストの導入で項が複雑になる場合がある

## コードサンプル

### サンプル 1: 基本的な qify
```lean
import Mathlib.Tactic.Qify

example (a b c : Int) (h : a ≤ b + c) : ((↑a : ℚ) ≤ ↑b + ↑c) := by
  qify at h ⊢
  exact_mod_cast h
```

### サンプル 2: zify → qify の段階的変換
```lean
import Mathlib.Tactic.Qify
import Mathlib.Tactic.Zify

example (n : Nat) : n ≤ n + 1 := by
  qify
  -- ⊢ (↑n : ℚ) ≤ ↑n + 1
  linarith
```

### サンプル 3: 仮定のキャスト
```lean
import Mathlib.Tactic.Qify

example (a b : Nat) (h : a ≤ b) : (↑a : ℚ) ≤ ↑b := by
  qify at h
  -- h : (↑a : ℚ) ≤ ↑b ⊢ (↑a : ℚ) ≤ ↑b
  exact h
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `zify` | ℕ → ℤ | 整数で十分な場合 |
| `rify` | ℤ/ℕ → ℝ | 実数が必要な場合 |
| `push_cast` | キャスト分配 | 手動でキャストの位置を制御 |
| `norm_cast` | キャスト正規化 | キャスト等式の正規化 |
| `field_simp` | 分母消去 | `qify` 後に分数を消去 |

## 参照
- [Mathlib4 ドキュメント — Qify](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Qify.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
