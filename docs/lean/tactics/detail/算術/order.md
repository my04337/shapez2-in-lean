# `order` — 半順序・全順序の自動証明

**カテゴリ**: 算術 | **定義元**: `Mathlib.Tactic.Order.tacticOrder_` | **ソース**: Mathlib

---

## 概要

`order` は `Preorder` / `PartialOrder` / `LinearOrder` における順序関係のゴールを自動的に閉じる。仮定中の `≤`、`<`、`=` を組み合わせてゴールを導出する。反射律・推移律・反対称律などの順序公理を自動的に適用する。
`omega` や `linarith` が数値算術に特化しているのに対し、`order` は抽象的な順序構造に対して動作する。

## ゴールパターン

**Before:**
```lean
α : Type*
inst : PartialOrder α
a : α
⊢ a ≤ a
```

**After:**
```lean
-- ゴールが閉じる（no goals）
```

**Before:**
```lean
α : Type*
inst : Preorder α
a b c : α
h₁ : a ≤ b
h₂ : b ≤ c
⊢ a ≤ c
```

**After:**
```lean
-- ゴールが閉じる（no goals）
```

## 構文

```lean
order
```

## 必須 import

```lean
import Mathlib.Tactic.Order
```

## Pros（使うべき場面）

- 抽象的な順序構造（任意の `Preorder` / `PartialOrder` / `LinearOrder`）で動作
- 反射律 (`le_refl`)・推移律 (`le_trans`)・反対称律 (`le_antisymm`) を自動適用
- `<` と `≤` の混合した仮定を統一的に処理
- 具体的な数値型に限定されない汎用的な順序推論

## Cons（注意・失敗ケース）

- 具体的な数値計算（`3 ≤ 5` など）は `omega` や `norm_num` の方が適切
- 算術演算（加算・乗算）を含む不等式は対象外 → `linarith` / `nlinarith` を使うこと
- 複雑な順序推論では仮定が十分でないと失敗する
- `min` / `max` の推論には直接対応しない場合がある

## コードサンプル

### 例 1: 反射律

```lean
import Mathlib.Tactic.Order

-- ⊢ a ≤ a
example [PartialOrder α] (a : α) : a ≤ a := by
  order
```

半順序の反射律 `le_refl` を自動適用する。

### 例 2: 推移律

```lean
import Mathlib.Tactic.Order

-- h₁ : a ≤ b, h₂ : b ≤ c ⊢ a ≤ c
example [Preorder α] (a b c : α) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  order
```

仮定から推移律を適用してゴールを閉じる。

### 例 3: 厳密不等式と非厳密不等式の組み合わせ

```lean
import Mathlib.Tactic.Order

-- h₁ : a < b, h₂ : b ≤ c ⊢ a < c
example [Preorder α] (a b c : α) (h₁ : a < b) (h₂ : b ≤ c) : a < c := by
  order
```

`<` と `≤` を組み合わせた推論を自動処理する。

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `omega` | 補完 | `Nat` / `Int` の線形算術に特化。数値型なら `omega` を優先 |
| `linarith` | 補完 | 算術演算を含む線形不等式。`order` より適用範囲が広いが型制約が厳しい |
| `le_trans` / `lt_trans` | 基盤 | 個別の順序補題。`order` が失敗する場合に手動で適用 |
| `exact?` | フォールバック | `order` が失敗した場合に適切な補題を検索する |
| `gcongr` | 補完 | 関数適用を保つ不等式（`f a ≤ f b`）の証明に使用 |

## 参照

- [Mathlib4 docs — order](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Order.html)

---

> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
