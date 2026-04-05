# `zify` — 自然数ゴールを整数ゴールに変換

**カテゴリ**: キャスト / 線形算術 | **定義元**: `Mathlib.Tactic.Zify.zify` | **ソース**: Mathlib

## 概要
`zify` は `Nat` 上のゴールや仮定を `Int` へキャストするタクティク。`Nat` の飽和減算 (`a - b = max (a - b) 0`) が原因で `omega` や `linarith` が直接使えない場合、`zify` で `Int` に持ち上げてからこれらのタクティクに渡す典型的なパターンがある。`@[zify_simps]` 属性の補題を使ってキャストを正規化する。

## ゴールパターン

**適用前**
```lean
a b : Nat
h : b ≤ a
⊢ a - b + b = a
```

**適用後**
```lean
a b : Nat
h : (↑b : Int) ≤ ↑a
⊢ ↑a - ↑b + ↑b = ↑a
```

## 構文
```lean
zify                    -- ゴールを ℕ → ℤ に変換
zify at h               -- 仮定 h を変換
zify at h ⊢             -- 仮定 h とゴール両方
zify at *               -- 全仮定とゴールを変換
zify [lemma]            -- 追加の補題を使用して simp
```

## 必須 import
```lean
import Mathlib.Tactic.Zify
```

## オプション一覧
| 構文 | 意味 |
|---|---|
| `at h` | 仮定 h に適用 |
| `at *` | 全仮定とゴールに適用 |
| `[h₁, h₂]` | 追加の simp 補題を使用 |

## Pros
- `Nat` の飽和減算問題を回避できる
- `omega` / `linarith` との相性が良い（`zify ; omega` のパターン）
- 不等式の仮定も自動的にキャストされる

## Cons
- Mathlib 依存のため Lean4 core のみでは使えない
- キャストの導入でゴールが大きくなる場合がある
- `Nat.sub_add_cancel` 等の直接的な補題で解ける場合は冗長

## コードサンプル

### サンプル 1: zify + omega の典型パターン
```lean
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Linarith

example (a b : Nat) (h : b ≤ a) : a - b + b = a := by
  zify [h]
  -- ⊢ ↑a - ↑b + ↑b = ↑a （Int 上の等式）
  omega
```

### サンプル 2: 不等式の変換
```lean
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Linarith

example (n : Nat) (h : n ≥ 3) : n - 2 ≥ 1 := by
  zify at h ⊢
  -- h : (↑n : Int) ≥ 3 ⊢ ↑n - 2 ≥ 1
  omega
```

### サンプル 3: 仮定の変換
```lean
import Mathlib.Tactic.Zify

example (a b c : Nat) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  zify at *
  -- h₁ : (↑a : Int) ≤ ↑b, h₂ : (↑b : Int) ≤ ↑c ⊢ (↑a : Int) ≤ ↑c
  omega
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `qify` | ℤ/ℕ → ℚ | 有理数が必要な場合 |
| `rify` | ℤ/ℕ → ℝ | 実数が必要な場合 |
| `push_cast` | キャスト分配 | 手動でキャストの位置を制御 |
| `omega` | 線形算術 | `zify` 後に算術ゴールを閉じる |
| `norm_cast` | キャスト正規化 | キャスト等式の正規化 |

## 参照
- [Mathlib4 ドキュメント — Zify](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Zify.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
