# `rotate_left` — ゴールリストを左に回転する

**カテゴリ**: 制御 | **定義元**: `Lean.Parser.Tactic.rotateLeft` | **ソース**: Lean4 core

---

## 概要

`rotate_left n` はゴールリストを左に `n` 回回転する。先頭の `n` 個のゴールがリストの末尾に移動する。`n` を省略すると 1 回回転。後方のゴールを先に処理したい場合のゴール順序変更に使う。

---

## ゴールパターン

**適用前**
```lean
-- ゴール 1: ⊢ A
-- ゴール 2: ⊢ B
-- ゴール 3: ⊢ C
```

**適用後**（`rotate_left`）
```lean
-- ゴール 1: ⊢ B
-- ゴール 2: ⊢ C
-- ゴール 3: ⊢ A
```

---

## 構文

```lean
rotate_left
rotate_left n
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `rotate_left` | 1 回左回転 |
| `rotate_left n` | `n` 回左回転 |

---

## Pros（使うべき場面）

- 後方のゴールを先に処理したい場合
- Lean4 core 組み込みで import 不要
- `swap` の一般化版として使える

---

## Cons（注意・失敗ケース）

- ゴール番号が変わるため後続の番号指定で混乱しうる
- `case` によるケース名指定の方が安定的
- 回転数が大きいとゴール順の把握が困難

---

## コードサンプル

### サンプル 1: 基本的な回転

```lean
example : True ∧ (1 = 1) := by
  constructor
  -- ⊢ True, ⊢ 1 = 1
  rotate_left
  -- ⊢ 1 = 1, ⊢ True
  · rfl
  · trivial
```

### サンプル 2: n 回回転

```lean
example : True ∧ True ∧ True := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left 2
  -- 3番目のゴールが先頭に
  all_goals trivial
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `rotate_right` | 右回転 | 逆方向の回転 |
| `swap` | 1↔2 入替 | 先頭2つの入替なら `swap` |
| `pick_goal` | 指定移動 | 1 つだけ移動するなら `pick_goal` |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
