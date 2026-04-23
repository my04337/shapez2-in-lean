# `intros` — 複数の変数・仮説を一括導入

**カテゴリ**: 導入 | **定義元**: `Lean.Parser.Tactic.intros` | **ソース**: Lean4 core

---

## 概要

`intros` は `intro` の一括版で、ゴール先頭の `∀` や `→` をすべて（または指定数だけ）導入する。名前を省略すると Lean が自動命名する。大量の束縛変数がある場合や、名前を気にしない仮定を素早く処理したい場合に便利。

---

## ゴールパターン

**適用前**
```lean
⊢ ∀ (a b c : Nat), a + b + c = c + b + a
```

**適用後** (`intros a b c`)
```lean
a b c : Nat
⊢ a + b + c = c + b + a
```

**適用後** (`intros`、名前省略)
```lean
a✝ b✝ c✝ : Nat
⊢ a✝ + b✝ + c✝ = c✝ + b✝ + a✝
```

---

## 構文

```lean
intros                 -- すべての ∀/→ を自動命名で導入
intros x y z           -- 名前を指定して導入
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 説明 |
|---|---|
| `intros` | ゴール先頭のすべての ∀/→ を自動命名で導入 |
| `intros x y z` | 指定した名前で順に導入 |

---

## Pros（使うべき場面）

- 仮定が多数あるとき、一度に全部導入して後で整理する運用に向く
- 名前を気にしない使い捨ての仮定を素早く処理できる
- `intro` を何回も書く手間を省ける

---

## Cons（注意・失敗ケース）

- 名前を省略すると `✝` 付きの自動命名になり、後から参照しにくい
- パターンマッチはサポートしない（`rintro` を使うこと）
- `intro` と異なり、名前なしで呼ぶとすべてを導入するため、意図せず深く導入しすぎる場合がある

---

## コードサンプル

### サンプル 1: すべて一括導入
```lean
example : ∀ (a b : Nat), a = b → b = a := by
  intros a b hab
  -- a b : Nat
  -- hab : a = b
  -- ⊢ b = a
  exact hab.symm
```

### サンプル 2: 名前省略での一括導入
```lean
example : ∀ (P Q : Prop), P → Q → P := by
  intros
  -- 自動命名された仮定がコンテキストに入る
  -- P✝ Q✝ : Prop, a✝¹ : P✝, a✝ : Q✝
  -- ⊢ P✝
  assumption
```

### サンプル 3: intro との比較
```lean
-- intro で 1 つずつ
example : ∀ (n m : Nat), n + m = m + n := by
  intro n; intro m
  exact Nat.add_comm n m

-- intros で一括
example : ∀ (n m : Nat), n + m = m + n := by
  intros n m
  exact Nat.add_comm n m
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `intro` | 基本形 | 名前を 1 つずつ明示的に付けたい場合 |
| `rintro` | 上位互換 | パターンマッチ付きで導入したい場合 |
| `revert` | 逆操作 | コンテキストの仮定をゴールに戻す |

---

## 参照
- [Lean4 公式リファレンス — intros](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#intro-intros)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
