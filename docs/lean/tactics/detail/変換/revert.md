# `revert` — 仮定をゴールに戻す（`intro` の逆操作）

**カテゴリ**: 変換 | **定義元**: `Lean.Parser.Tactic.revert` | **ソース**: Lean4 core

---

## 概要

`revert` は仮定（hypothesis）をコンテキストからゴールに戻すタクティクで、`intro` の逆操作にあたる。
仮定 `h : P` をリバートすると、ゴールが `P → Q` の形に変化する。
帰納法の前にゴールを一般化したり、`induction` の帰納法仮説を強化するために使われる。

---

## ゴールパターン

**適用前**
```lean
h : P
⊢ Q
```

**適用後（`revert h`）**
```lean
⊢ P → Q
```

---

## 構文

```lean
revert h
revert h₁ h₂ h₃
```

複数の仮定を同時にリバートできる。依存関係がある仮定は自動的にリバートされる。

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `revert h` | 仮定 `h` をゴールに戻す |
| `revert h₁ h₂` | 複数の仮定を同時にゴールに戻す |

---

## Pros（使うべき場面）

- `induction` の前にゴールを一般化し、帰納法仮説を強化するための基本操作
- 仮定をゴールに組み込むことで、`intro` のタイミングを制御できる
- 依存する仮定が自動的にリバートされるため、順序を気にしなくてよい

---

## Cons（注意・失敗ケース）

- リバートした仮定に依存する他の仮定も自動リバートされるため、予期しないゴール変化が起きうる
- リバートしすぎるとゴールが複雑になり、かえって証明が困難になる場合がある
- `generalize` の方が適切な場合もある（具体的な式を変数に置き換えたいとき）

---

## コードサンプル

### サンプル 1: 基本的なリバート

```lean
example (n : Nat) (h : n > 0) : n ≥ 1 := by
  -- n : Nat, h : n > 0
  -- ⊢ n ≥ 1
  revert h
  -- n : Nat
  -- ⊢ n > 0 → n ≥ 1
  omega
```

### サンプル 2: 帰納法の前準備

```lean
example (n m : Nat) : n + m = m + n := by
  -- n m : Nat
  -- ⊢ n + m = m + n
  revert m
  -- n : Nat
  -- ⊢ ∀ (m : Nat), n + m = m + n
  induction n with
  | zero => simp
  | succ n ih => intro m; omega
```

### サンプル 3: 複数仮定の同時リバート

```lean
example (a b : Nat) (h1 : a > 0) (h2 : b > 0) : a + b > 0 := by
  -- a b : Nat, h1 : a > 0, h2 : b > 0
  revert h1 h2
  -- ⊢ a > 0 → b > 0 → a + b > 0
  omega
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `intro` | 逆操作 | `intro` はゴールの `∀` / `→` を仮定に導入する |
| `generalize` | 類似 | 部分式を新変数に一般化する。`revert` は仮定をゴールに戻す |
| `induction` | 後続 | `revert` で一般化した後に `induction` で帰納法を適用する典型パターン |
| `clear` | 仮定除去 | `clear` は仮定を完全に捨てる。`revert` はゴールに組み込む |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
