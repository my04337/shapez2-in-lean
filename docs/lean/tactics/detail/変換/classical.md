# `classical` — 古典論理のインスタンスをスコープ内で有効化

**カテゴリ**: 変換 | **定義元**: `Lean.Parser.Tactic.classical` | **ソース**: Lean4 core

---

## 概要

`classical` は `Classical.propDecidable` を低優先度のローカルインスタンスとしてスコープ内に追加するタクティクである。
これにより、`Decidable` インスタンスが定義されていない命題に対しても `by_cases`、`split`、`if` 式の分岐などが可能になる。
構成的でない命題の排中律を利用した証明が必要な場面で使用する。

---

## ゴールパターン

**適用対象**: 任意（ゴールの型に制約なし）

**適用前**
```lean
⊢ P
```

**適用後**
```lean
-- ゴールは変化しない（Decidable インスタンスがスコープに追加される）
⊢ P
```

---

## 構文

```lean
classical
<tactics>
```

`classical` の後続タクティク全体がスコープとなる。

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `classical` | `Classical.propDecidable` を低優先度で追加 |

引数は取らない。後続のタクティクブロック全体に影響する。

---

## Pros（使うべき場面）

- `Decidable` インスタンスのない命題に `by_cases` や `decide` 相当の分岐を適用できる
- 古典論理の排中律 (`em`) を暗黙的に利用可能にする
- 数学的な証明で構成的制約を緩和したい場合に有効

---

## Cons（注意・失敗ケース）

- 構成的な証明が必要な場面には不向き（計算可能性が失われる）
- `#eval` で使う関数の証明に `classical` を使うと、実行時エラーになる可能性がある
- 低優先度インスタンスのため、明示的な `Decidable` インスタンスがある場合はそちらが優先される

---

## コードサンプル

### サンプル 1: Decidable のない命題で by_cases

```lean
example (P : Prop) : P ∨ ¬P := by
  -- ⊢ P ∨ ¬P
  classical
  by_cases h : P
  -- ケース 1: h : P ⊢ P ∨ ¬P
  · exact Or.inl h
  -- ケース 2: h : ¬P ⊢ P ∨ ¬P
  · exact Or.inr h
```

### サンプル 2: if-then-else の分岐

```lean
example (P : Prop) [Decidable P] : (if P then 1 else 0) = 0 ∨ (if P then 1 else 0) = 1 := by
  -- ⊢ (if P then 1 else 0) = 0 ∨ (if P then 1 else 0) = 1
  by_cases h : P
  · simp [h]
  · simp [h]
```

### サンプル 3: 二重否定の除去

```lean
example (P : Prop) (h : ¬¬P) : P := by
  -- ⊢ P
  classical
  by_cases hp : P
  · exact hp
  · exact absurd hp h
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `by_cases` | 連携 | `classical` で `Decidable` を補った上で `by_cases` を使う |
| `by_contra` | 背理法 | 背理法。`classical` なしでも `¬` 導入は可能だが二重否定除去に必要 |
| `decide` | 決定手続き | `Decidable` が存在する命題の自動証明 |
| `tauto` | 命題論理 | 古典論理の命題を自動証明（内部で `classical` 相当を使用） |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
