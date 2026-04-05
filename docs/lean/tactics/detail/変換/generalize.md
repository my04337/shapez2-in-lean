# `generalize` — 部分式を新しい変数に一般化する

**カテゴリ**: 変換 | **定義元**: `Lean.Parser.Tactic.generalize` | **ソース**: Lean4 core

---

## 概要

`generalize` はゴール中の特定の部分式を新しい自由変数に置き換え、ゴールをより一般的な形にするタクティクである。
帰納法の適用前にゴールを一般化したり、具体的な式を抽象化して証明を進めるために使用する。
`generalize h : e = x` の形で、元の等式を仮定として保持することもできる。

---

## ゴールパターン

**適用前**
```lean
⊢ List.length [1, 2, 3] ≥ 0
```

**適用後（`generalize List.length [1, 2, 3] = n`）**
```lean
⊢ n ≥ 0
```

---

## 構文

```lean
generalize e = x
generalize h : e = x
generalize e = x at h₁ h₂
```

- `e`: 一般化する部分式
- `x`: 新しい変数名
- `h`: 元の等式 `e = x` を保持する仮定名（省略可）

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `generalize e = x` | `e` を `x` に一般化する |
| `generalize h : e = x` | `e` を `x` に一般化し、`h : e = x` を仮定に追加する |
| `generalize e = x at h₁ h₂` | 仮定 `h₁`, `h₂` 中の `e` も `x` に置き換える |

---

## Pros（使うべき場面）

- 帰納法（`induction`）の前にゴールを一般化して帰納法仮説を強化する
- 具体的な計算結果を抽象変数に置き換えて一般的な性質から証明を導ける
- `h : e = x` で元の情報を保持できるため、後で具体値に戻せる

---

## Cons（注意・失敗ケース）

- 一般化しすぎるとゴールが証明不能になる場合がある（情報の喪失）
- `h : e = x` を付けずに一般化すると元の情報が失われ、復元できない
- 依存型がある場合、型エラーが発生することがある

---

## コードサンプル

### サンプル 1: 基本的な一般化

```lean
example : List.length [1, 2, 3] ≥ 0 := by
  -- ⊢ List.length [1, 2, 3] ≥ 0
  generalize List.length [1, 2, 3] = n
  -- ⊢ n ≥ 0
  omega
```

### サンプル 2: 等式を保持する一般化

```lean
example : 2 + 3 = 5 := by
  -- ⊢ 2 + 3 = 5
  generalize h : 2 + 3 = n
  -- h : 2 + 3 = n
  -- ⊢ n = 5
  omega
```

### サンプル 3: 帰納法の前準備

```lean
example (l : List Nat) : (l ++ []).length = l.length := by
  -- ⊢ (l ++ []).length = l.length
  generalize h : l.length = n
  -- h : l.length = n
  -- ⊢ (l ++ []).length = n
  simp [h]
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `revert` | 逆操作 | 仮定をゴールに戻す。`generalize` で導入した変数を ∀ に戻す場合 |
| `induction` | 後続 | `generalize` で一般化した後に帰納法を適用する典型パターン |
| `set` | 類似 | `set` は局所定義を導入しつつ書き換え等式も提供する。Mathlib |
| `subst` | 復元 | `generalize h : e = x` で保持した等式を使って代入を戻す |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
