# `pick_goal` — 指定番号のゴールをメインに移動する

**カテゴリ**: 制御 | **定義元**: `Mathlib.Tactic.pickGoal` | **ソース**: Mathlib

---

## 概要

`pick_goal n` は `n` 番目のゴールをメインゴール（先頭）に移動する。`rotate_left` がリスト全体を回転するのに対し、`pick_goal` は指定ゴールだけを先頭に引き上げる。負の数を指定すると末尾から数える。

---

## ゴールパターン

**適用前**
```lean
-- ゴール 1: ⊢ A
-- ゴール 2: ⊢ B
-- ゴール 3: ⊢ C
```

**適用後**（`pick_goal 3`）
```lean
-- ゴール 1: ⊢ C
-- ゴール 2: ⊢ A
-- ゴール 3: ⊢ B
```

---

## 構文

```lean
pick_goal n
pick_goal -n
```

- `n`: 正の数で先頭から、負の数で末尾からカウント

---

## 必須 import

```lean
import Mathlib.Tactic.Core
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `pick_goal n` | `n` 番目のゴールを先頭に移動 |
| `pick_goal -1` | 最後のゴールを先頭に移動 |

---

## Pros（使うべき場面）

- 後方のゴールを先に処理したい場合
- `rotate_left` では他のゴール順序も変わるが `pick_goal` は 1 つだけ移動
- 負の数でのカウントにより末尾のゴールを簡単に指定可能

---

## Cons（注意・失敗ケース）

- ゴール番号が動的に変わるため脆弱
- `case` による名前指定の方が安定
- Mathlib import が必要

---

## コードサンプル

### サンプル 1: 3番目のゴールを先頭に

```lean
import Mathlib.Tactic.Core

example : True ∧ True ∧ True := by
  refine ⟨?_, ?_, ?_⟩
  pick_goal 3
  -- 3番目のゴール ⊢ True が先頭に
  all_goals trivial
```

### サンプル 2: 末尾ゴールの指定

```lean
import Mathlib.Tactic.Core

example : True ∧ True := by
  refine ⟨?_, ?_⟩
  pick_goal -1
  all_goals trivial
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `on_goal` | ゴール指定 | 移動せずその場で適用するなら `on_goal` |
| `swap` | 先頭2つ入替 | 先頭2つの入替なら `swap` |
| `rotate_left` | 回転 | 全体を左回転するなら `rotate_left` |
| `case` | 名前指定 | 名前で安定的に指定するなら `case` |

---

## 参照

- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
