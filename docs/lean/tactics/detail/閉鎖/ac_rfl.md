# `ac_rfl` — 結合律・交換律による等式の証明

**カテゴリ**: 閉鎖 | **定義元**: `Mathlib.Tactic.acRfl` | **ソース**: Mathlib

---

## 概要

`ac_rfl` は結合律（associativity）と交換律（commutativity）のみで等しくなる等式を自動的に証明するタクティクである。
演算子が `Comm` および `Assoc` インスタンスを持つ場合に使用可能。
項の並び替え・括弧の付け替えだけで一致する等式を一発で閉じられる。
`ring` や `abel` より軽量で、AC 正規化に特化している。

---

## ゴールパターン

**適用対象**: 結合律と交換律で一致する等式

**適用前**
```lean
⊢ a + b + c = c + a + b
```

**適用後**
```lean
-- ゴールなし（証明完了）
```

---

## 構文

```lean
ac_rfl
```

引数は取らない。

---

## 必須 import

```lean
import Mathlib.Tactic.NormNum   -- ac_rfl を含む
-- または
import Mathlib.Tactic.Ring      -- 間接的に含む
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `ac_rfl` | AC 正規化で等式を閉じる |

オプションはない。

---

## Pros（使うべき場面）

- 並び替えだけで一致する等式を `ring` より軽量に閉じられる
- `simp [add_comm, add_assoc]` の繰り返しを 1 ワードで置き換えられる
- 可換モノイド・可換群の等式で特に有効

---

## Cons（注意・失敗ケース）

- AC 以外の等式変換（分配則、逆元、`0` の性質等）は扱えない
- `Comm` または `Assoc` インスタンスがない演算では失敗する
- 乗法と加法が混在する等式には `ring` を使う必要がある

---

## コードサンプル

### サンプル 1: 加法の並び替え

```lean
example (a b c : Nat) : a + b + c = c + (b + a) := by
  -- ⊢ a + b + c = c + (b + a)
  ac_rfl
  -- ゴールなし（証明完了）
```

### サンプル 2: 乗法の並び替え

```lean
example (a b c : Int) : a * b * c = c * a * b := by
  -- ⊢ a * b * c = c * a * b
  ac_rfl
  -- ゴールなし（証明完了）
```

### サンプル 3: 集合の和の並び替え

```lean
import Mathlib.Data.Set.Basic

example (s t u : Set α) : s ∪ t ∪ u = u ∪ s ∪ t := by
  -- ⊢ s ∪ t ∪ u = u ∪ s ∪ t
  ac_rfl
  -- ゴールなし（証明完了）
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `rfl` | 部分的 | 構文的に完全一致する場合のみ。AC 正規化は行わない |
| `ring` | 上位互換 | 加乗の分配則や逆元も含む環の正規化 |
| `abel` | 加法版 | 可換群の正規化。減算・負の数も扱える |
| `comm` | 交換のみ | 単一の交換律適用。2 項の入れ替えだけの場合 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
