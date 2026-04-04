# `fun_induction` — 再帰関数の構造に沿った帰納法

**カテゴリ**: 分解 | **定義元**: `Lean.Parser.Tactic.funInduction` | **ソース**: Lean4 core

---

## 概要

`fun_induction` は再帰関数の定義構造に沿った帰納法を自動生成するタクティクである。
通常の `induction` ではデータ型の構造に沿った帰納法しか得られないが、
`fun_induction` は関数の再帰パターン（停止条件・再帰呼び出し）に基づいたケース分割と
帰納法の仮説を生成する。
well-founded 再帰や複雑な分岐を持つ関数の性質を証明する際に特に有効。

---

## ゴールパターン

**適用対象**: 再帰関数を含む命題

**適用前**
```lean
⊢ P (f x)
```

**適用後** (`fun_induction f x`)
```lean
-- 各再帰ケースに対応するサブゴール（帰納法の仮説付き）
```

---

## 構文

```lean
fun_induction f x₁ x₂ ...       -- 関数 f の引数を指定
fun_induction f x with           -- with 節で各ケースに名前
  | case₁ args ih => tac₁
  | case₂ args ih => tac₂
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `fun_induction f x` | 関数 `f` の再帰構造に沿って帰納法を適用 |
| `with \| case args ih => tac` | 各ケースに名前を付けてタクティクを指定 |

---

## Pros（使うべき場面）

- 再帰関数の定義パターンに完全に一致するケース分割が自動で得られる
- well-founded 再帰の複雑な停止証明に対応した帰納法の仮説が生成される
- `induction` + 手動の `simp` による関数展開の組み合わせが不要になる

---

## Cons（注意・失敗ケース）

- 対象関数が `@[reducible]` や `abbrev` の場合、展開されて認識できないことがある
- 相互再帰関数には対応していない場合がある
- 関数のマッチ構造が複雑すぎると、生成されるケースが多くなり証明が煩雑になる

---

## コードサンプル

### サンプル 1: リストの長さに関する帰納法

```lean
def myLength : List α → Nat
  | [] => 0
  | _ :: xs => 1 + myLength xs

theorem myLength_append (xs ys : List α) :
    myLength (xs ++ ys) = myLength xs + myLength ys := by
  -- ⊢ myLength (xs ++ ys) = myLength xs + myLength ys
  fun_induction myLength xs with
  | case1 => simp [myLength]
  -- ⊢ myLength ys = myLength ys  （[] ++ ys = ys）
  | case2 x xs ih =>
  -- ih : myLength (xs ++ ys) = myLength xs + myLength ys
  -- ⊢ myLength (x :: xs ++ ys) = myLength (x :: xs) + myLength ys
    simp [myLength, ih]; omega
```

### サンプル 2: 除算の再帰構造に沿った帰納法

```lean
def myDiv : Nat → Nat → Nat
  | n, d => if d = 0 then 0
            else if n < d then 0
            else 1 + myDiv (n - d) d
  termination_by n => n

theorem myDiv_zero (n : Nat) : myDiv n 0 = 0 := by
  -- ⊢ myDiv n 0 = 0
  simp [myDiv]  -- d = 0 の分岐で即座に 0 となる
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `induction` | データ型帰納法 | データ型の構造に沿った帰納法。関数非依存 |
| `fun_cases` | ケース分析版 | 再帰構造のケース分析のみ（帰納法の仮説なし） |
| `cases` | 基本分解 | 1段のコンストラクタ分解 |
| `simp` | 関数展開 | 関数定義を展開して簡約する |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
