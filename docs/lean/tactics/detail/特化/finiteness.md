# `finiteness` — @[finiteness] 補題で有限性を証明する

**カテゴリ**: 特化 | **定義元**: `Mathlib.Tactic.Finiteness` | **ソース**: Mathlib

---

## 概要

`finiteness` は `@[finiteness]` 属性が付いた補題を使って、集合の有限性（`Set.Finite`、`Finset` 関連）や測度の有限性（`MeasureTheory.Measure.FiniteAt` 等）を自動的に証明するタクティクである。

---

## ゴールパターン

**適用前**
```lean
⊢ Set.Finite s
```

**適用後**: `@[finiteness]` 補題で閉鎖

---

## 構文

```lean
finiteness
```

---

## 必須 import

```lean
import Mathlib.Tactic.Finiteness
```

---

## オプション一覧

特になし。`@[finiteness]` タグ付き補題を自動探索する。

---

## Pros（使うべき場面）

- `Set.Finite` の証明を自動化
- 測度の有限性の証明
- `@[finiteness]` 補題の組み合わせで構造的に証明

---

## Cons（注意・失敗ケース）

- 適切な `@[finiteness]` 補題がないと失敗
- Mathlib import が必要
- `Fintype` と `Set.Finite` の使い分けに注意

---

## コードサンプル

### サンプル 1: 有限集合の証明

```lean
import Mathlib.Tactic.Finiteness
import Mathlib.Data.Set.Finite.Basic

example : Set.Finite (∅ : Set Nat) := by
  finiteness
```

### サンプル 2: 和集合の有限性

```lean
import Mathlib.Tactic.Finiteness
import Mathlib.Data.Set.Finite.Basic

example (hs : Set.Finite s) (ht : Set.Finite t) : Set.Finite (s ∪ t) := by
  finiteness
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `exact?` | 補題検索 | 該当補題を手動で探す場合 |
| `infer_instance` | インスタンス | `Fintype` インスタンスの推論 |
| `decide` | 決定可能 | 有限型上の決定可能命題 |

---

## 参照

- [Mathlib4 ドキュメント — Finiteness](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Finiteness.html)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
