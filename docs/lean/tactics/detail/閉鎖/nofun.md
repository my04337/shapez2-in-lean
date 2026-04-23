# `nofun` — 空の関数マッチで到達不能ケースを閉じる

**カテゴリ**: 閉鎖 | **定義元**: `Lean.Parser.Tactic.tacticNofun` | **ソース**: Lean4 core

---

## 概要

`nofun` は `exact nofun` の糖衣構文であり、ゴールが関数型 `A → B` のとき、`A` が空型（有効なコンストラクタが存在しない型）であるために到達不能であることを利用して証明を閉じる。
典型的には、`cases` や `match` の分岐で矛盾するパターンを排除する場面で使われる。
`nofun` は空のパターンマッチ `fun.` の項レベル版に対応するタクティクである。

---

## ゴールパターン

**適用前**
```lean
⊢ False → P
```

**適用後**
```lean
-- ゴールなし（証明完了）
```

---

## 構文

```lean
nofun
```

引数は取らない。

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `nofun` | `exact nofun` と等価。空のパターンマッチでゴールを閉じる |

---

## Pros（使うべき場面）

- 仮定の型が空（`Empty`、`False`、空の帰納型のケース等）で関数型ゴールが到達不能な場合に簡潔に閉じられる
- `contradiction` や `nomatch` と比べて、関数型の空パターンマッチに特化しており意図が明確
- `exact nofun` より短く書ける

---

## Cons（注意・失敗ケース）

- ゴールが関数型でない場合は失敗する
- 引数の型が空であることが明らかでない場合（型展開が必要な場合等）は失敗することがある
- 複数引数の場合、最初の引数だけでは空型と判定できないケースがある
- `contradiction` の方がより汎用的なため、単純な矛盾には `contradiction` を使う方がよい

---

## コードサンプル

### サンプル 1: False → P の証明

```lean
example : False → Nat := by
  -- ⊢ False → Nat
  nofun
  -- ゴールなし（証明完了）
```

### サンプル 2: 空の帰納型からの関数

```lean
inductive MyEmpty : Type where

example : MyEmpty → Nat := by
  -- ⊢ MyEmpty → Nat
  nofun
  -- ゴールなし（証明完了）
```

### サンプル 3: cases 後の到達不能ケース

```lean
example (h : P ∨ False) : P := by
  cases h with
  | inl hp => exact hp
  | inr hf =>
    -- hf : False
    -- ⊢ P
    exact hf.elim
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `nomatch` | 類似 | `nomatch h` は具体的な項に対する空パターンマッチ。`nofun` は関数型ゴール全体に適用 |
| `contradiction` | 汎用 | 仮定の矛盾検出全般。`nofun` より広い範囲の矛盾に対応 |
| `exact nofun` | 同義 | `nofun` は `exact nofun` の省略形 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
