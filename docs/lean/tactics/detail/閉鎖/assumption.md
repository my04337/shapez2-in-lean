# `assumption` — 仮定からゴールを自動的に閉じる

**カテゴリ**: 閉鎖 | **定義元**: `Lean.Parser.Tactic.assumption` | **ソース**: Lean4 core

---

## 概要

`assumption` は、ローカルコンテキスト内の仮定を順に検索し、ゴールの型と一致するものが見つかればそれを使って証明を閉じるタクティクである。
内部的には各仮定に対して `exact` を試行し、最初に成功したものを採用する。
仮定の名前を覚える必要がなく、特に `cases` や `induction` で生成された多数の仮定がある場面で便利。

---

## ゴールパターン

**適用前**
```lean
h₁ : P
h₂ : Q
⊢ P
```

**適用後**
```lean
-- ゴールなし（証明完了）
```

---

## 構文

```lean
assumption
```

引数は取らない。

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `assumption` | コンテキスト内の仮定を順に検索してゴールを閉じる |

Mathlib には `assumption'` が存在し、すべてのゴールに対して `assumption` を試行する変種として使える。

---

## Pros（使うべき場面）

- 仮定名を指定せずにゴールを閉じたい場合に便利
- `cases`・`induction`・`rcases` 後に自動生成された仮定名に依存しない証明が書ける
- 短く書けるため、自明なサブゴールの処理に最適

---

## Cons（注意・失敗ケース）

- 一致する仮定がコンテキストにない場合は失敗する
- 型のユニフィケーションが必要な場合（メタ変数を含む仮定等）は失敗することがある
- 複数の仮定が一致する場合、どれが選ばれるかは実装依存（通常は最後に追加された仮定が優先）
- 仮定が存在するのに失敗する場合は、`exact` で明示的に指定する方が確実

---

## コードサンプル

### サンプル 1: 基本的な仮定マッチ

```lean
example (h : 2 + 2 = 4) : 2 + 2 = 4 := by
  -- h : 2 + 2 = 4
  -- ⊢ 2 + 2 = 4
  assumption
  -- ゴールなし（証明完了）
```

### サンプル 2: 複数仮定がある場合

```lean
example (h₁ : P) (h₂ : Q) (h₃ : R) : Q := by
  -- h₁ : P, h₂ : Q, h₃ : R
  -- ⊢ Q
  assumption
  -- ゴールなし（証明完了）— h₂ が使われる
```

### サンプル 3: cases 後の自動生成仮定

```lean
example (h : P ∨ Q) (hp : P → R) (hq : Q → R) : R := by
  cases h with
  | inl h =>
    -- h : P
    -- ⊢ R
    exact hp h
  | inr h =>
    -- h : Q
    -- ⊢ R
    exact hq h
```

---

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `assumption'` | 全ゴールに対して `assumption` を試行する |
| `assumption_mod_cast` | `norm_cast` でキャストを正規化した後 `assumption` を試行する |

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `exact` | 汎化 | `exact h` は仮定を明示的に指定する。`assumption` は自動検索 |
| `apply_assumption` | 拡張（Mathlib） | 仮定を `apply` として使う。ゴールが仮定の結論部に一致する場合にサブゴールを生成 |
| `assumption'` | 変種（Mathlib） | 全ゴールに対して `assumption` を試行する |
| `trivial` | 上位 | `trivial` は `assumption` を含む複数タクティクを試行する |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
