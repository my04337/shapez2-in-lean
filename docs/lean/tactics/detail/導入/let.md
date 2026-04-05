# `let` — ローカルコンテキストに透明な定義を導入

**カテゴリ**: 導入 | **定義元**: `Lean.Parser.Tactic.tacticLet_` | **ソース**: Lean4 core

---

## 概要

`let` はローカルコンテキストに**透明な**ローカル定義を追加するタクティクである。
`have` と異なり、導入された定義は `simp`、`unfold`、`dsimp` などで展開可能であり、
ゴールの簡約時に定義本体が参照される。
計算途中の値に名前を付けて再利用したい場合や、`simp` で自動展開してほしい定義に適する。

---

## ゴールパターン

**適用対象**: 任意（ゴールの型に制約なし）

**適用前**
```lean
⊢ P
```

**適用後** (`let x : T := e`)
```lean
x : T := e
⊢ P
```

---

## 構文

```lean
let x : T := e                -- 型と値を明示
let x := e                    -- 型推論に任せる
let ⟨a, b⟩ := e              -- パターンマッチで分解
let x : T := by tac            -- タクティクで値を構成
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `let x : T := e` | 名前と型を明示して透明定義を追加 |
| `let x := e` | 型推論に任せる |
| `let ⟨a, b⟩ := e` | 構造体・積をパターンで分解 |

---

## Pros（使うべき場面）

- 定義本体が透明なので、`simp`・`dsimp`・`unfold` で自動展開される
- 複雑な式に名前を付け、証明の可読性と再利用性を向上できる
- ゴールや仮定中で定義が展開されるため、計算的な証明と相性が良い

---

## Cons（注意・失敗ケース）

- 透明性のため、コンテキストが肥大化し `simp` の挙動が変わることがある
- 定義本体を隠蔽したい場合は `have` を使うべき
- `let` で導入した定義を除去するには `clear x` が必要だが、依存がある場合は除去できない

---

## コードサンプル

### サンプル 1: 透明定義の導入と展開

```lean
example : 2 + 3 = 5 := by
  -- ⊢ 2 + 3 = 5
  let x := 2 + 3
  -- x : Nat := 2 + 3
  -- ⊢ 2 + 3 = 5
  rfl
```

### サンプル 2: have との違い（透明性）

```lean
example : (fun n => n + 1) 3 = 4 := by
  -- ⊢ (fun n => n + 1) 3 = 4
  let f := fun n => n + 1
  -- f : Nat → Nat := fun n => n + 1
  -- ⊢ (fun n => n + 1) 3 = 4
  show f 3 = 4
  -- ⊢ f 3 = 4    （f は透明なので展開可能）
  rfl
```

### サンプル 3: パターンマッチによる分解

```lean
example (p : Nat × Nat) (h : p.1 + p.2 = 10) : p.1 + p.2 = 10 := by
  -- ⊢ p.1 + p.2 = 10
  let ⟨a, b⟩ := p
  -- a : Nat, b : Nat
  -- ⊢ (a, b).1 + (a, b).2 = 10
  exact h
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `have` | 不透明版 | `have` は不透明定義。展開不要な仮定の導入に適する |
| `set` | 置換付き | `set` は定義を導入しつつゴール中の式を置換する |
| `intro` | 関数引数 | `intro` は全称量化子・関数の引数を導入する |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
