# `fun_cases` — 関数定義に沿ったケース分析

**カテゴリ**: 分解 | **定義元**: `Lean.Parser.Tactic.funCases` | **ソース**: Lean4 core

---

## 概要

`fun_cases` は関数の定義構造（パターンマッチ・条件分岐）に沿ってケース分析を行うタクティクである。
`fun_induction` と異なり帰納法の仮説は生成せず、関数のマッチアームに対応するケース分割のみを行う。
関数の各分岐ケースに対応するサブゴールが生成され、それぞれのケースでの仮定が自動で追加される。
非再帰的な関数や、再帰不要なケースの証明に適する。

---

## ゴールパターン

**適用対象**: 関数適用を含む命題

**適用前**
```lean
⊢ P (f x)
```

**適用後** (`fun_cases f x`)
```lean
-- 関数 f の各マッチアームに対応するサブゴール
```

---

## 構文

```lean
fun_cases f x₁ x₂ ...         -- 関数 f の引数を指定
fun_cases f x with             -- with 節で各ケースに名前
  | case₁ args => tac₁
  | case₂ args => tac₂
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `fun_cases f x` | 関数 `f` の定義構造に沿ってケース分析 |
| `with \| case args => tac` | 各ケースに名前を付けてタクティクを指定 |

---

## Pros（使うべき場面）

- 関数の各パターンマッチケースに対応した自然なケース分割が得られる
- 条件分岐（`if`）やガード条件も含めてケースが生成される
- `cases` + `simp` の手動展開よりも簡潔で正確

---

## Cons（注意・失敗ケース）

- 帰納法の仮説は生成されない（再帰的な性質には `fun_induction` を使う）
- 関数が `@[reducible]` や `abbrev` の場合は認識できないことがある
- 関数のマッチ構造が複雑すぎるとケースが多くなる

---

## コードサンプル

### サンプル 1: Option のマッピング関数

```lean
def myMap (f : α → β) : Option α → Option β
  | none => none
  | some x => some (f x)

theorem myMap_id (o : Option α) : myMap id o = o := by
  -- ⊢ myMap id o = o
  fun_cases myMap id o with
  | case1 =>
    -- ⊢ myMap id none = none
    rfl
  | case2 x =>
    -- ⊢ myMap id (some x) = some x
    rfl
```

### サンプル 2: 条件分岐を含む関数

```lean
def clamp (n lo hi : Nat) : Nat :=
  if n < lo then lo
  else if n > hi then hi
  else n

theorem clamp_le_hi (n lo hi : Nat) (h : lo ≤ hi) :
    clamp n lo hi ≤ hi := by
  -- ⊢ clamp n lo hi ≤ hi
  fun_cases clamp n lo hi <;> omega
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `fun_induction` | 帰納法版 | 再帰関数の帰納法が必要な場合に使う |
| `cases` | データ型分解 | データ型のコンストラクタ分解 |
| `split` | if/match 分割 | ゴール中の `if`/`match` を分割 |
| `simp` | 関数展開 | 関数定義の展開による簡約 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
