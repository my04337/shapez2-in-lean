# `first` — 複数タクティクを順に試し、最初に成功したものを適用

**カテゴリ**: 制御 | **定義元**: `Lean.Parser.Tactic.first` | **ソース**: Lean4 core

## 概要
`first` は `|` で区切られた複数のタクティクを先頭から順に試行し、最初に成功したものの効果を適用する。すべて失敗した場合は `first` 自体が失敗する。分岐的なケースで、どのタクティクが効くか事前に分からない場合に有用。`try` と異なり、少なくとも1つは成功する必要がある。

## ゴールパターン

**適用前**（`first | exact h | rfl`）
```lean
h : P
⊢ P
```

**適用後**
```lean
-- exact h が成功し、ゴールが閉じる
```

**適用前**（すべて失敗する場合）
```lean
⊢ P
```

**適用後**
```lean
-- first 自体がエラー: all alternatives failed
```

## 構文
```lean
first | tac1 | tac2          -- tac1 を試し、失敗すれば tac2
first | tac1 | tac2 | tac3   -- 3つ以上も列挙可能
first
  | tac1
  | tac2
  | tac3                     -- 改行スタイル
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `\| tac` | 試行する各タクティクを `\|` で区切る |
| 改行スタイル | インデントされたブロックで複数行に分けて記述 |

## Pros
- 分岐を宣言的に書ける
- `cases` や `induction` 後の各ケースで共通処理を試すのに便利
- すべて失敗した場合にエラーになるため、`try` より意図を明示できる

## Cons
- 成功したタクティクがどれか、スクリプト上で分かりにくい
- 順序に依存するため、先頭のタクティクが部分的に成功すると後続を試さない
- 分岐が多すぎると可読性が低下する

## コードサンプル

### サンプル 1: 基本的な分岐
```lean
example (n : Nat) : n + 0 = n := by
  first | ring | simp | omega
  -- simp が成功し、ゴールが閉じる
```

### サンプル 2: cases 後の各ケースを統一処理
```lean
example (b : Bool) : (b && true) = b := by
  cases b
  -- ゴール 1: ⊢ (false && true) = false
  -- ゴール 2: ⊢ (true && true) = true
  all_goals first | rfl | simp
  -- 両ケースとも rfl で閉じる
```

### サンプル 3: 改行スタイルで複雑な分岐
```lean
example (n : Nat) (h : n ≤ 5) : n < 6 := by
  first
    | exact Nat.lt_of_le_of_lt h (by norm_num)
    | omega
  -- omega が成功してゴールが閉じる
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `try` | 単一タクティクの試行 | 失敗を無視したいだけなら `try` |
| `solve` | 完全解決の分岐 | ゴールの完全閉鎖が条件なら `solve` |
| `any_goals` | 全ゴールへの試行 | 各ゴールに対して試行なら `any_goals` |

## 参照
- [Lean4 公式リファレンス — first](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
