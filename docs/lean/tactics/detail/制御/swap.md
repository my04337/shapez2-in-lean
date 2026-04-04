# `swap` — 先頭2つのゴールを入れ替える

**カテゴリ**: 制御 | **定義元**: `Lean.Parser.Tactic.tacticSwap` | **ソース**: Lean4 core

---

## 概要

`swap` はゴールリストの先頭2つのゴールの順序を入れ替える。`rotate_left 1` と同等だが、より直感的な名前で最も頻繁なゴール入替操作を表現する。

---

## ゴールパターン

**適用前**
```lean
-- ゴール 1: ⊢ A
-- ゴール 2: ⊢ B
```

**適用後**
```lean
-- ゴール 1: ⊢ B
-- ゴール 2: ⊢ A
```

---

## 構文

```lean
swap
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

特になし。

---

## Pros（使うべき場面）

- 2番目のゴールを先に処理したい場合の最も簡潔な記法
- core 組み込みで import 不要
- `constructor` 後に 2 番目のゴールを先に処理するイディオム

---

## Cons（注意・失敗ケース）

- ゴールが 1 つしかない場合は実質 no-op
- 3 つ以上のゴール入替には `rotate_left` や `pick_goal` を使う
- `case` の方が安定的

---

## コードサンプル

### サンプル 1: 基本的な入替

```lean
example : (1 = 1) ∧ True := by
  constructor
  -- ⊢ 1 = 1, ⊢ True
  swap
  -- ⊢ True, ⊢ 1 = 1
  · trivial
  · rfl
```

### サンプル 2: constructor 後の入替

```lean
example : True ∧ (2 + 2 = 4) := by
  constructor
  swap
  · rfl
  · trivial
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `rotate_left` | 一般化版 | n 回回転するなら `rotate_left` |
| `rotate_right` | 逆回転 | 逆方向の回転 |
| `pick_goal` | 指定移動 | 任意のゴールを先頭へ |
| `case` | 名前指定 | 名前でゴールを選択 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
