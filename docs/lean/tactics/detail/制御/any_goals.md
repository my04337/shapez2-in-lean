# `any_goals` — すべてのゴールに適用し、成功したものだけ反映

**カテゴリ**: 制御 | **定義元**: `Lean.Parser.Tactic.anyGoals` | **ソース**: Lean4 core

## 概要
`any_goals` は現在のすべてのゴールに対して指定したタクティクを順に適用する。`all_goals` と異なり、**少なくとも1つのゴールで成功すればよく**、失敗したゴールはそのまま残る。すべてのゴールで失敗した場合にのみ `any_goals` 自体が失敗する。一部のゴールだけ閉じたい場合に有用。

## ゴールパターン

**適用前**（`any_goals rfl`）
```lean
-- ゴール 1
⊢ 1 = 1
-- ゴール 2
⊢ a = b
```

**適用後**
```lean
-- ゴール 1 は rfl で閉じる
-- 残りのゴール:
⊢ a = b
```

## 構文
```lean
any_goals tac            -- 成功するゴールだけ適用
any_goals (tac1; tac2)   -- タクティク列を各ゴールに適用
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `any_goals tac` | 全ゴールに tac を試し、少なくとも1つ成功すればよい |

## Pros
- 部分的に解決できるゴールだけ処理し、残りは後で対応できる
- `all_goals` + `try` の組み合わせに近いが、全滅時にエラーを出す点で安全
- スクリプトの意図（「何個か閉じたい」）が明示される

## Cons
- どのゴールが解決されたか把握しにくい
- ゴール順序に依存する場合は予期しない結果になりうる
- 全ゴール成功が必要なら `all_goals` の方が厳密

## コードサンプル

### サンプル 1: 自明なゴールだけ pick up
```lean
example (a : Nat) : a = a ∧ a + 0 = a ∧ 0 + a = a := by
  refine ⟨?_, ?_, ?_⟩
  -- ゴール 1: ⊢ a = a
  -- ゴール 2: ⊢ a + 0 = a
  -- ゴール 3: ⊢ 0 + a = a
  any_goals rfl
  -- ゴール 1 が閉じる。残り:
  -- ⊢ a + 0 = a
  -- ⊢ 0 + a = a
  all_goals simp
```

### サンプル 2: assumption で仮定に一致するゴールを閉じる
```lean
example (h₁ : P) (h₂ : Q) : P ∧ R ∧ Q := by
  refine ⟨?_, ?_, ?_⟩
  -- ゴール 1: ⊢ P
  -- ゴール 2: ⊢ R
  -- ゴール 3: ⊢ Q
  any_goals assumption
  -- ゴール 1, 3 が閉じる。残り: ⊢ R
  sorry
```

### サンプル 3: omega で数値系ゴールだけ処理
```lean
example (n : Nat) (h : n < 5) : n < 6 ∧ n ≤ 5 ∧ True := by
  refine ⟨?_, ?_, ?_⟩
  any_goals omega
  -- n < 6 と n ≤ 5 が omega で閉じる。残り: ⊢ True
  trivial
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `all_goals` | 全ゴール必須成功 | すべてのゴールで成功が必要なら `all_goals` |
| `try` | 失敗の無視 | 単一タクティクの失敗を無視するなら `try` |
| `focus` | 単一ゴールに集中 | 特定のゴールだけ作業したいなら `focus` |

## 参照
- [Lean4 公式リファレンス — any_goals](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
