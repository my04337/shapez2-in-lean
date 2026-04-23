# `suffices` — 中間ゴールの導入（「〜を示せば十分」）

**カテゴリ**: 変換 | **定義元**: `Lean.Parser.Tactic.tacticSuffices_` | **ソース**: Lean4 core

---

## 概要

`suffices` は「P を示せば十分である」という形で中間命題を導入するタクティクである。
`suffices h : P by tac` と書くと、まず `P` が成り立つと仮定して元のゴールを `tac` で証明し、
次に `P` 自体を証明する 2 段階の構造になる。`have` の逆順版とも言える。

---

## ゴールパターン

**適用前**
```lean
⊢ Q
```

**適用後（`suffices h : P by exact h.2`）**
```lean
-- ゴール: ⊢ P
```

---

## 構文

```lean
suffices h : P by tac
suffices h : P from expr
suffices P by tac
```

- `h`: 中間命題に付ける名前（省略可）
- `P`: 中間命題
- `tac`: `h : P` を使って元のゴールを閉じるタクティク

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `suffices h : P by tac` | `h : P` を仮定して `tac` で元ゴールを閉じ、`P` の証明に進む |
| `suffices h : P from expr` | `h : P` を使った項 `expr` で元ゴールを閉じる |
| `suffices P by tac` | 名前を省略する場合（`this` が自動で使われる） |

---

## Pros（使うべき場面）

- 証明の方針を「逆順」で記述でき、最終ステップを先に示せるため証明の流れが明確になる
- `have` と似ているが、元ゴールの閉鎖を先に書くため「何を示せば十分か」が読み手にすぐ伝わる
- 証明の論理構造をトップダウンで記述する場合に適している

---

## Cons（注意・失敗ケース）

- `by tac` 部分で元ゴールを閉じられないとエラーになる
- `have` と機能的に同等であるため、使い分けは文体的な好みによる部分が大きい
- 中間ステップが多い場合はネストが深くなりやすい

---

## コードサンプル

### サンプル 1: 基本的な使用

```lean
example (n : Nat) (h : n > 0) : n ≥ 1 := by
  -- ⊢ n ≥ 1
  suffices n > 0 by omega
  -- ⊢ n > 0
  exact h
```

### サンプル 2: 名前付き仮定

```lean
example : 2 + 2 = 4 ∧ 3 + 3 = 6 := by
  -- ⊢ 2 + 2 = 4 ∧ 3 + 3 = 6
  suffices h : 2 + 2 = 4 by exact ⟨h, by omega⟩
  -- ⊢ 2 + 2 = 4
  rfl
```

### サンプル 3: have との比較

```lean
-- suffices: 「Q を示せば十分」→ Q の証明
example (h : P → Q) (hp : P) : Q := by
  suffices hp : P by exact h hp
  -- ⊢ P
  exact hp
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `have` | 逆順 | `have` は中間命題を先に証明してから使う。`suffices` は使い方を先に示す |
| `show` | ゴール選択 | `show` はゴールの型を明示するが、新しい命題は導入しない |
| `calc` | 段階的 | 段階的な計算証明。`suffices` は 2 段階分割に向く |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
