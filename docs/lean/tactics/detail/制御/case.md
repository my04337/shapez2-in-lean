# `case` — ケース名を指定してゴールを選択・処理

**カテゴリ**: 制御 | **定義元**: `Lean.Parser.Tactic.case` | **ソース**: Lean4 core

## 概要
`case` は、ゴールに付けられたケース名（タグ）を指定して特定のゴールをフォーカスし、ブロック内のタクティクでそのゴールを処理する。`cases`、`induction`、`constructor` 等で分岐した後に、ゴールの順序に依存せずケース名で選択できるため、証明の堅牢性と可読性が向上する。変数名のリネームも同時に行える。

## ゴールパターン

**適用前**（`case succ n ih =>`）
```lean
-- case zero
⊢ P 0
-- case succ
⊢ ∀ n, P n → P (n + 1)
```

**case succ ブロック内**
```lean
n : Nat
ih : P n
⊢ P (n + 1)
```

## 構文
```lean
case tag => tac              -- ケース名で選択
case tag x y => tac          -- 変数を x, y にリネーム
case tag x y ih => tac       -- 帰納仮説も含めてリネーム
case tag1 | tag2 => tac      -- 複数ケースを同じタクティクで処理
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `case tag =>` | tag という名前のゴールにフォーカス |
| `case tag x y =>` | フォーカスしつつ変数を x, y にリネーム |
| `case tag1 \| tag2 =>` | 複数ケースに同じ処理を適用 |

## Pros
- ゴールの順序に依存しないため、証明が定義変更に対して堅牢
- 変数名の明示的なリネームでスクリプトの可読性が向上
- 構造化された証明スタイルを促進する

## Cons
- ケース名がない（匿名の）ゴールには使えない
- ケース名を正確に知る必要がある（`case?` で確認可能）
- 短い証明では `·` や `next` の方が簡潔

## コードサンプル

### サンプル 1: 帰納法のケース指定
```lean
example (n : Nat) : 0 + n = n := by
  induction n
  case zero =>
    -- ⊢ 0 + 0 = 0
    rfl
  case succ n ih =>
    -- n : Nat, ih : 0 + n = n ⊢ 0 + (n + 1) = n + 1
    omega
```

### サンプル 2: 順序を入れ替えて処理
```lean
example (n : Nat) : n = n ∨ n = n + 1 := by
  left
  rfl
```

```lean
-- case を使えばゴール順序に依存しない
example (b : Bool) : b = true ∨ b = false := by
  cases b
  case true => left; rfl
  case false => right; rfl
```

### サンプル 3: 複数ケースをまとめて処理
```lean
example (n : Nat) (h : n < 3) : n < 4 := by
  omega
```

```lean
-- パターン：2つのケースが同じ証明を持つ場合
example (b : Bool) : (b && b) = b := by
  cases b
  case true | false => rfl
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `next` | 次のゴールに集中 | 名前不要で次のゴールを処理するなら `next` |
| `focus` | メインゴールに集中 | 名前なしでメインゴールに集中するなら `focus` |
| `·`（bullet） | 構造化証明 | 短い分岐処理は `·` が慣用的 |
| `case?` | ケース名の列挙 | 現在のケース名を確認するには `case?` |

## 参照
- [Lean4 公式リファレンス — case](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
