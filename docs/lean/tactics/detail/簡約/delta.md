# `delta` — 定義の低レベルδ展開

**カテゴリ**: 簡約 | **定義元**: `Lean.Parser.Tactic.delta` | **ソース**: Lean 4 core

---

## 概要

`delta` は指定した名前の定義をカーネルレベルで**δ展開（delta reduction）** する。
`unfold` が equation lemma を用いてユーザフレンドリーに展開するのに対し、`delta` は
コンパイル後の内部表現をそのまま露出させる。再帰関数の場合、`WellFounded.fix` や
`brecOn` 等の内部実装が現れるため、通常は `unfold` を優先する。

`unfold` では展開できない定義や、内部表現を直接操作する必要がある高度な場面で使用する。

## ゴールパターン

**Before:**
```lean
⊢ myConst 42 = 42     -- def myConst (n : Nat) := n
```

**After:**
```lean
⊢ 42 = 42
```

**Before（再帰関数の場合）:**
```lean
⊢ myFunc x = y
```

**After:**
```lean
⊢ <WellFounded.fix による内部表現> = y
-- unfold と異なり、コンパイル済みの低レベル表現が露出する
```

## 構文

```lean
delta name
delta name₁ name₂ ...
delta name at h
delta name at *
```

## オプション一覧

| オプション | 説明 |
|---|---|
| `name` | δ展開する定義の名前。複数指定可能 |
| `at h` | 仮定 `h` に対して展開を適用する |
| `at *` | ゴールと全仮定に対して展開を適用する |

## Pros（使うべき場面）

- `unfold` が失敗する定義も展開できる（equation lemma が存在しない場合など）
- 複数の定義を一度に展開可能
- カーネルが見ている「真の定義」を確認できるためデバッグに有用
- 非再帰関数の展開は `unfold` と同等に扱いやすい

## Cons（注意・失敗ケース）

- 再帰関数を展開すると `WellFounded.fix` 等の複雑な内部表現が露出し、扱いが困難になる
- ゴールが非常に読みにくくなる場合が多い
- 展開後の式に対して通常のタクティクが適用しにくくなることがある
- ほとんどの場面で `unfold` や `simp [name]` で代替可能
- `delta` は「最後の手段」として位置づけるのが推奨

## コードサンプル

### 例 1: 非再帰的な定義のδ展開

```lean
def myId (x : Nat) : Nat := x

example : myId 10 = 10 := by
  delta myId
  -- ⊢ 10 = 10
  rfl
```

非再帰関数の場合、`delta` の結果は `unfold` と同じで読みやすい。

### 例 2: 複数の定義を同時に展開

```lean
def addOne (n : Nat) : Nat := n + 1
def addTwo (n : Nat) : Nat := addOne (addOne n)

example : addTwo 3 = 5 := by
  delta addTwo addOne
  -- ⊢ 3 + 1 + 1 = 5 — addTwo と addOne が同時に展開される
  rfl
```

`delta name₁ name₂` で複数の定義を一括展開できる。

### 例 3: unfold が失敗する場面での delta

```lean
noncomputable def myChoice (h : ∃ n : Nat, n > 0) : Nat :=
  Classical.choose h

-- unfold myChoice が失敗するケースでも delta は使える
example (h : ∃ n : Nat, n > 0) : myChoice h = Classical.choose h := by
  delta myChoice
  -- ⊢ Classical.choose h = Classical.choose h
  rfl
```

`noncomputable` 定義など、`unfold` が equation lemma を見つけられない場合に `delta` が有効。

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `unfold` | 高レベル版 | equation lemma を使った読みやすい展開。通常はこちらを優先 |
| `dsimp` | 類似 | 定義的等価による簡約。展開と簡約を同時に行う |
| `simp [name]` | 上位互換 | 展開後にさらに `@[simp]` 補題で簡約する場合 |
| `show` | 代替 | 定義的に等しい別の式をゴールとして明示する |
| `change` | 代替 | 定義的に等しい別の式にゴールを書き換える |

## 参照

- [Lean 4 Reference — The Simplifier](https://lean-lang.org/doc/reference/latest/Tactics/Simplifier/)
- [Mathlib4 ドキュメント — delta](https://leanprover-community.github.io/mathlib4_docs/Init/Tactics.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
