# `all_goals` — すべてのゴールにタクティクを適用

**カテゴリ**: 制御 | **定義元**: `Lean.Parser.Tactic.allGoals` | **ソース**: Lean4 core

## 概要
`all_goals` は現在のすべてのゴールに対して指定したタクティクを順に適用し、各ゴールから生じたサブゴールを結合する。**すべてのゴールで成功する必要があり**、1つでも失敗すると `all_goals` 全体が失敗する。`constructor` や `cases` でゴールが複数に分岐した後、共通の処理をまとめて適用したい場合に有用。

## ゴールパターン

**適用前**（`all_goals simp`）
```lean
-- ゴール 1
⊢ 0 + a = a
-- ゴール 2
⊢ b + 0 = b
```

**適用後**
```lean
-- 両ゴールとも simp で閉じる
```

## 構文
```lean
all_goals tac            -- すべてのゴールに tac を適用
all_goals (tac1; tac2)   -- セミコロンで連鎖した列を適用
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `all_goals tac` | 全ゴールに tac を適用。1つでも失敗すると全体が失敗 |

## Pros
- 分岐後の重複コードを排除できる
- `simp`、`omega` 等の汎用タクティクと相性がよい
- 証明スクリプトが簡潔になる

## Cons
- 1つでも失敗するとロールバックされるため、部分的成功を許容できない
- 部分的に適用したい場合は `any_goals` の方が適切
- ゴールの順序に依存しない処理でないと予期しない結果になる

## コードサンプル

### サンプル 1: constructor 後の共通処理
```lean
example (a b : Nat) : a + 0 = a ∧ 0 + b = b := by
  constructor
  -- ゴール 1: ⊢ a + 0 = a
  -- ゴール 2: ⊢ 0 + b = b
  all_goals simp
  -- 両方 simp で閉じる
```

### サンプル 2: cases 後に omega で一括処理
```lean
example (n : Nat) (h : n < 3) : n ≤ 2 := by
  interval_cases n
  -- ゴール 1: ⊢ 0 ≤ 2
  -- ゴール 2: ⊢ 1 ≤ 2
  -- ゴール 3: ⊢ 2 ≤ 2
  all_goals omega
```

### サンプル 3: try と組み合わせて失敗を許容
```lean
example (a : Nat) (h : a = 1) : a = 1 ∧ 1 = 1 := by
  constructor
  -- ゴール 1: ⊢ a = 1
  -- ゴール 2: ⊢ 1 = 1
  all_goals (try assumption)
  -- ゴール 1 は assumption で閉じる。ゴール 2 は try で失敗を無視
  -- 残り: ⊢ 1 = 1
  rfl
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `any_goals` | 部分的成功で十分 | 成功したゴールだけ閉じたいなら `any_goals` |
| `<;>` | 直前タクティクの全サブゴールに適用 | 1つのタクティクが生成した直後のゴールに適用なら `<;>` |
| `focus` | 単一ゴールに集中 | 1つのゴールだけ操作したいなら `focus` |

## 参照
- [Lean4 公式リファレンス — all_goals](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
