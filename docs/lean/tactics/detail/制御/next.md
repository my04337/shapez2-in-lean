# `next` — 次のゴールにフォーカスし、変数をリネーム

**カテゴリ**: 制御 | **定義元**: `Lean.Parser.Tactic.«tacticNext_=>_»` | **ソース**: Lean4 core

## 概要
`next` は現在のメインゴール（次に処理すべきゴール）にフォーカスし、オプションで仮定や変数をリネームする。`case` と似ているが、ケース名ではなくゴールの順序で選択する点が異なる。ゴール内の束縛変数に分かりやすい名前を付けつつ処理を進めたい場合に使う。

## ゴールパターン

**適用前**（`next x hx =>`）
```lean
-- ゴール 1 (メイン)
n✝ : Nat
h✝ : n✝ > 0
⊢ P n✝
```

**next ブロック内**
```lean
x : Nat
hx : x > 0
⊢ P x
```

## 構文
```lean
next => tac              -- 次のゴールにフォーカス（リネームなし）
next x => tac            -- 変数を x にリネーム
next x hx => tac         -- 複数の変数をリネーム
next _ h => tac          -- _ で名前を省略
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `next =>` | メインゴールにフォーカス |
| `next x y =>` | ゴールの導入変数を x, y にリネーム |
| `next _ h =>` | `_` は名前を変えずにスキップ |

## Pros
- ケース名を知らなくてもゴールにフォーカスできる
- 自動生成された `n✝` 等の名前を分かりやすくリネームできる
- `case` より軽量で、構造化証明のアウトラインとして使いやすい

## Cons
- ゴールの順序に依存するため、定義変更で壊れるリスクがある
- ケース名がある場合は `case` の方が堅牢
- リネームする変数の数を間違えるとエラーになる

## コードサンプル

### サンプル 1: 帰納法でリネーム
```lean
example (n : Nat) : 0 + n = n := by
  induction n
  next =>
    -- ⊢ 0 + 0 = 0
    rfl
  next n ih =>
    -- n : Nat, ih : 0 + n = n ⊢ 0 + (n + 1) = n + 1
    omega
```

### サンプル 2: 自動生成名のリネーム
```lean
example (l : List Nat) : l.reverse.length = l.length := by
  induction l
  next => simp
  -- ⊢ [].reverse.length = [].length → simp で閉じる
  next x xs ih =>
    -- x : Nat, xs : List Nat, ih : xs.reverse.length = xs.length
    -- ⊢ (x :: xs).reverse.length = (x :: xs).length
    simp [ih]
```

### サンプル 3: cases の後に next で処理
```lean
example (o : Option Nat) : o.isSome = true → ∃ n, o = some n := by
  cases o
  next =>
    -- ⊢ none.isSome = true → ∃ n, none = some n
    intro h; simp at h
  next val =>
    -- val : Nat ⊢ (some val).isSome = true → ∃ n, some val = some n
    intro _; exact ⟨val, rfl⟩
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `case` | 名前指定でゴール選択 | ケース名で堅牢に選択するなら `case` |
| `focus` | メインゴールに集中 | リネーム不要なら `focus` で十分 |
| `·`（bullet） | 構造化証明 | 短い処理は `·` が慣用的 |
| `rename_i` | 仮定のリネーム | focus せずリネームだけしたいなら `rename_i` |

## 参照
- [Lean4 公式リファレンス — next](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
