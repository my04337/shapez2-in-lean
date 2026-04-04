# `on_goal` — 指定番号のゴールにタクティクを適用する

**カテゴリ**: 制御 | **定義元**: `Mathlib.Tactic.onGoal` | **ソース**: Mathlib

---

## 概要

`on_goal n => tac` は `n` 番目のゴールを一時的にメインゴールに移動し、`tac` を適用した後、元のゴール順序に戻す。`case` のようにケース名を必要とせず、番号指定でゴールを操作できる。

---

## ゴールパターン

**適用前**
```lean
-- ゴール 1: ⊢ A
-- ゴール 2: ⊢ B
-- ゴール 3: ⊢ C
```

**適用後**（`on_goal 2 => exact hB`）
```lean
-- ゴール 1: ⊢ A
-- ゴール 2: ⊢ C
```

---

## 構文

```lean
on_goal n => tac
```

- `n`: 1-indexed のゴール番号

---

## 必須 import

```lean
import Mathlib.Tactic.Core
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `on_goal n => tac` | `n` 番目のゴールに `tac` を適用 |

---

## Pros（使うべき場面）

- ケース名なしでゴール番号により precise に操作できる
- `pick_goal` と違いゴール順序を維持したまま操作
- 中間のゴールだけ処理したい場合に便利

---

## Cons（注意・失敗ケース）

- ゴール番号はタクティクの追加・削除で変動するため脆弱
- `case` のようにケース名で安定的に指定する方が推奨
- Mathlib import が必要

---

## コードサンプル

### サンプル 1: 2番目のゴールを処理

```lean
import Mathlib.Tactic.Core

example : True ∧ True ∧ True := by
  refine ⟨?_, ?_, ?_⟩
  on_goal 2 => exact trivial
  all_goals trivial
```

### サンプル 2: 特定ゴールに simp

```lean
import Mathlib.Tactic.Core

example (n : Nat) : n = n ∧ 0 + n = n := by
  constructor
  on_goal 2 => simp
  rfl
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `pick_goal` | ゴール移動 | メインゴールに移動するなら `pick_goal` |
| `case` | ケース名指定 | 名前で安定的に指定するなら `case` |
| `swap` | 1↔2 入替 | 先頭2つの入替なら `swap` |
| `rotate_left` | 回転 | 全体を回転するなら `rotate_left` |

---

## 参照

- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
