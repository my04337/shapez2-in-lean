# `focus` — メインゴールに集中し、他を一時的に隠す

**カテゴリ**: 制御 | **定義元**: `Lean.Parser.Tactic.focus` | **ソース**: Lean4 core

## 概要
`focus` はメインゴール（最初のゴール）のみを対象としてタクティクブロックを実行し、他のゴールを一時的に隠す。ブロック終了後、メインゴールが閉じていれば隠していたゴールが復元される。メインゴールが残っている場合はエラーになる。複数ゴールがある状況で、1つずつ確実に処理したい場合に使う。

## ゴールパターン

**適用前**（`focus` ブロック内）
```lean
-- ゴール 1 (メイン)
⊢ A
-- ゴール 2 (隠される)
⊢ B
```

**focus ブロック内で見えるゴール**
```lean
⊢ A
```

**ブロック完了後**
```lean
⊢ B
```

## 構文
```lean
focus
  tac1
  tac2         -- メインゴールだけ見える状態で実行

focus tac      -- 1行スタイル
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `focus` ブロック | メインゴールのみ露出。終了時にゴールが残るとエラー |

## Pros
- 複数ゴールがあっても1つずつ集中して作業できる
- 意図しないゴールへの影響を防ぐ
- スクリプトの構造を明確にし、どのゴールを処理しているか分かりやすい

## Cons
- メインゴールを閉じないとエラーになるため、途中段階では使いにくい
- 構造化モード（`·`）で十分な場合は冗長
- ゴール数が不定の場合は `case` や `next` の方が柔軟

## コードサンプル

### サンプル 1: 基本的な focus の使い方
```lean
example (ha : A) (hb : B) : A ∧ B := by
  constructor
  -- ゴール 1: ⊢ A
  -- ゴール 2: ⊢ B
  focus exact ha
  -- ゴール 1 が閉じ、ゴール 2 が復元
  -- ⊢ B
  exact hb
```

### サンプル 2: Bullet（`·`）は focus の糖衣構文
```lean
example (ha : A) (hb : B) : A ∧ B := by
  constructor
  · exact ha   -- · は focus の糖衣構文
  · exact hb
```

### サンプル 3: 複雑な証明で特定ゴールに集中
```lean
example (n : Nat) : n + 0 = n ∧ 0 + n = n := by
  constructor
  focus
    -- ⊢ n + 0 = n のみ見える
    simp
  focus
    -- ⊢ 0 + n = n のみ見える
    simp
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `·`（bullet） | focus の糖衣構文 | 短い証明では `·` が慣用的 |
| `case` | 名前指定でゴール選択 | ケース名でゴールを選択するなら `case` |
| `next` | 次のゴールに集中 | 変数名をリネームしつつ次を処理するなら `next` |
| `all_goals` | 全ゴール操作 | 共通処理を全ゴールに適用するなら `all_goals` |

## 参照
- [Lean4 公式リファレンス — focus](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
