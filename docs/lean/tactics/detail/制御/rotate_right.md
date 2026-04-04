# `rotate_right` — ゴールリストを右に回転する

**カテゴリ**: 制御 | **定義元**: `Lean.Parser.Tactic.rotateRight` | **ソース**: Lean4 core

---

## 概要

`rotate_right n` はゴールリストを右に `n` 回回転する。末尾の `n` 個のゴールがリストの先頭に移動する。`rotate_left` の逆操作。

---

## ゴールパターン

**適用前**
```lean
-- ゴール 1: ⊢ A
-- ゴール 2: ⊢ B
-- ゴール 3: ⊢ C
```

**適用後**（`rotate_right`）
```lean
-- ゴール 1: ⊢ C
-- ゴール 2: ⊢ A
-- ゴール 3: ⊢ B
```

---

## 構文

```lean
rotate_right
rotate_right n
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `rotate_right` | 1 回右回転 |
| `rotate_right n` | `n` 回右回転 |

---

## Pros（使うべき場面）

- 最後のゴールを先に処理したい場合
- `rotate_left` の逆操作
- core 組み込みで import 不要

---

## Cons（注意・失敗ケース）

- `rotate_left` と同様にゴール順序の把握が困難になりうる
- `case` の方が安定的
- 回転数が大きいと混乱する

---

## コードサンプル

### サンプル 1: 基本的な右回転

```lean
example : (1 = 1) ∧ True := by
  constructor
  rotate_right
  -- 最後のゴール ⊢ True が先頭に
  · trivial
  · rfl
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `rotate_left` | 左回転 | 逆方向の回転 |
| `swap` | 1↔2 入替 | 先頭2つなら `swap` |
| `pick_goal` | 指定移動 | 特定ゴールを先頭に移動 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
