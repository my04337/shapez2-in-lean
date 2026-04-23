# `conv_rhs` — 等式右辺に conv フォーカス

**カテゴリ**: 書換 | **定義元**: `Mathlib.Tactic.Conv` | **ソース**: Mathlib

---

## 概要

`conv_rhs => ...` は等式ゴール `⊢ lhs = rhs` の右辺にのみ `conv` ブロックのフォーカスを絞るショートカットである。右辺だけを書き換えたい場合、`conv in` を使うよりも簡潔に記述できる。

---

## ゴールパターン

**適用前**
```lean
⊢ f a = g b
```

**conv_rhs 内のフォーカス**
```lean
| g b
```

---

## 構文

```lean
conv_rhs => tactic_seq
```

---

## 必須 import

```lean
import Mathlib.Tactic.Conv
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `conv_rhs => rw [h]` | 右辺で `h` を適用 |
| `conv_rhs => simp` | 右辺を簡約 |

---

## Pros（使うべき場面）

- 等式の右辺だけを変形したい場合
- 左辺を変えずに右辺を目標形に近づけたい場合
- `conv_lhs` との対称的な使用

---

## Cons（注意・失敗ケース）

- ゴールが `=` でない場合は使えない
- Mathlib import が必要
- 左辺は `conv_lhs` を使う

---

## コードサンプル

### サンプル 1: 右辺の書き換え

```lean
import Mathlib.Tactic.Conv

example (h : b = a) : a = b := by
  conv_rhs => rw [h]
```

### サンプル 2: 右辺の正規化

```lean
import Mathlib.Tactic.Conv

-- conv_rhs で右辺の a を ← h で b に書き換え
example (a b : Int) (h : b = a) : b * 2 = a * 2 := by
  conv_rhs => rw [← h]
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `conv_lhs` | 左辺版 | 左辺にフォーカスするなら `conv_lhs` |
| `conv` | 汎用版 | 任意の位置にフォーカス |
| `rw` | 直接書換 | 位置指定不要なら `rw` |

---

## 参照

- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
