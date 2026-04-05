# `conv_lhs` — 等式左辺に conv フォーカス

**カテゴリ**: 書換 | **定義元**: `Mathlib.Tactic.Conv` | **ソース**: Mathlib

---

## 概要

`conv_lhs => ...` は等式ゴール `⊢ lhs = rhs` の左辺にのみ `conv` ブロックのフォーカスを絞るショートカットである。`conv in` よりも簡潔に左辺だけを書き換えたい場合に使う。

---

## ゴールパターン

**適用前**
```lean
⊢ f a = g b
```

**conv_lhs 内のフォーカス**
```lean
| f a
```

---

## 構文

```lean
conv_lhs => tactic_seq
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
| `conv_lhs => rw [h]` | 左辺で `h` を適用 |
| `conv_lhs => ring_nf` | 左辺を正規化 |
| `conv_lhs => arg 1; rw [h]` | 左辺の第1引数を書換 |

---

## Pros（使うべき場面）

- 等式の左辺だけを変形したい場合
- `conv in lhs => ...` の簡潔な代替
- `simp` を片側にだけ適用したい場合

---

## Cons（注意・失敗ケース）

- ゴールが `=` でない場合は使えない（`≤` 等は `conv` を使う）
- Mathlib import が必要
- 右辺は `conv_rhs` を使う

---

## コードサンプル

### サンプル 1: 左辺の書き換え

```lean
import Mathlib.Tactic.Conv

-- 型注釈で型クラス推論を補助する
example (a b c : Nat) (h : a = b) : a + c = b + c := by
  conv_lhs => rw [h]
```

### サンプル 2: 左辺の書き換え（Int）

```lean
import Mathlib.Tactic.Conv

example (a b : Int) (h : a = b) : (a + 1) * 2 = (b + 1) * 2 := by
  conv_lhs => rw [h]
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `conv_rhs` | 右辺版 | 右辺にフォーカスするなら `conv_rhs` |
| `conv` | 汎用版 | 任意の位置にフォーカス |
| `rw` | 直接書換 | 位置指定不要なら `rw` |

---

## 参照

- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
