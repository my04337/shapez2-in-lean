# `unfold` — 定義を1段階展開する

**カテゴリ**: 簡約 | **定義元**: `Lean.Parser.Tactic.unfold` | **ソース**: Lean 4 core

---

## 概要

`unfold` は指定した名前の定義を**1段階だけ**展開する。再帰関数の場合はマッチ式まで展開される。
`simp only [name]` と異なり、`@[simp]` 属性の有無に関係なく任意の定義を展開できる。
定義の中身を確認しながら証明を進める際や、`simp` が自動で処理しない非 `@[simp]` 定義の
展開に有効。複数の名前を同時に指定可能。

## ゴールパターン

**Before:**
```lean
⊢ double 3 = 6       -- double は def double (n : Nat) := n + n
```

**After:**
```lean
⊢ 3 + 3 = 6
```

**Before:**
```lean
⊢ List.map f [] = []
```

**After:**
```lean
⊢ [] = []            -- List.map のマッチ式が展開される
```

## 構文

```lean
unfold name
unfold name₁ name₂ ...
unfold name at h
unfold name at *
```

## オプション一覧

| オプション | 説明 |
|---|---|
| `name` | 展開する定義の名前。複数指定可能 |
| `at h` | 仮定 `h` に対して展開を適用する |
| `at *` | ゴールと全仮定に対して展開を適用する |

## Pros（使うべき場面）

- 定義を1段階だけ制御しながら展開できる
- `@[simp]` 属性のない定義も展開可能
- 再帰関数のマッチ式を露出させて `split` や `cases` を適用する前処理に最適
- 定義の挙動を確認しながらステップバイステップで証明を進められる

## Cons（注意・失敗ケース）

- 再帰関数を `unfold` すると内部表現（`WellFounded.fix` 等）が露出し、読みにくくなることがある
- 複数回 `unfold` するとゴールが肥大化する
- `simp [name]` で済む場合はそちらの方が簡潔
- `unfold` は定義が存在しない名前を指定するとエラーになる
- equation lemma が生成されていない定義では失敗する場合がある

## コードサンプル

### 例 1: 単純な定義の展開

```lean
def double (n : Nat) : Nat := n + n

example : double 5 = 10 := by
  unfold double
  -- ⊢ 5 + 5 = 10
  rfl
```

`double` の定義が展開され、`5 + 5 = 10` が `rfl` で証明可能になる。

### 例 2: 再帰関数の展開とパターンマッチ

```lean
def myLength : List α → Nat
  | [] => 0
  | _ :: t => 1 + myLength t

example : myLength [1, 2, 3] = 3 := by
  unfold myLength
  -- ⊢ 1 + myLength [2, 3] = 3
  unfold myLength
  -- ⊢ 1 + (1 + myLength [3]) = 3
  unfold myLength
  -- ⊢ 1 + (1 + (1 + myLength [])) = 3
  unfold myLength
  -- ⊢ 1 + (1 + (1 + 0)) = 3
  rfl
```

再帰関数は `unfold` のたびに1段階ずつ展開される。実用上は `simp [myLength]` や `decide` の方が簡潔。

### 例 3: 仮定に対する unfold

```lean
def isPositive (n : Nat) : Prop := n > 0

example (h : isPositive 5) : 5 > 0 := by
  unfold isPositive at h
  -- h : 5 > 0
  exact h
```

`unfold ... at h` で仮定中の定義を展開し、具体的な命題に変換できる。

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `delta` | 低レベル版 | コンパイル後の内部表現を直接展開する。`unfold` で不十分な場合 |
| `dsimp only [name]` | 類似 | 定義的等価で簡約。`unfold` より整理された結果になる場合がある |
| `simp [name]` | 上位互換 | 展開後にさらに `@[simp]` 補題で簡約する場合 |
| `split` | 後続 | `unfold` でマッチ式を露出させた後にケース分割する |
| `rw [name]` | 代替 | equation lemma がある場合、特定の箇所だけ書き換え可能 |

## 参照

- [Lean 4 Reference — The Simplifier](https://lean-lang.org/doc/reference/latest/Tactics/Simplifier/)
- [Theorem Proving in Lean 4 — Tactics §5.4](https://lean-lang.org/theorem_proving_in_lean4/tactics.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
