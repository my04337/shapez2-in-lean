# `split_ands` — And を繰り返し分割する

**カテゴリ**: 導入 | **定義元**: `Mathlib.Tactic.splitAnds` | **ソース**: Mathlib

---

## 概要

`split_ands` はゴール `⊢ A ∧ B ∧ C ∧ ...` を再帰的に分割し、各 conjunct をサブゴールにする。`constructor` を繰り返し適用するのと同等だが、1 行で全ての `∧` を分割できる。`refine ⟨?_, ?_, ?_⟩` の代替として使える。

---

## ゴールパターン

**適用前**
```lean
⊢ A ∧ B ∧ C
```

**適用後**
```lean
⊢ A
⊢ B
⊢ C
```

---

## 構文

```lean
split_ands
```

---

## 必須 import

```lean
import Mathlib.Tactic.Core
```

---

## オプション一覧

特になし。

---

## Pros（使うべき場面）

- 多数の `∧` を 1 行で分割
- `constructor` の繰り返しを自動化
- `<;>` と組み合わせて一括処理

---

## Cons（注意・失敗ケース）

- `∧` のみ対象（`∨`やその他の帰納型は非対象）
- Mathlib import が必要
- 2-3 個の `∧` なら `constructor` で十分

---

## コードサンプル

### サンプル 1: 複数 And の分割

```lean
import Mathlib.Tactic.Core

example : True ∧ True ∧ True := by
  split_ands <;> trivial
```

### サンプル 2: 名前付きケースとの組み合わせ

```lean
import Mathlib.Tactic.Core

example : (1 = 1) ∧ True ∧ (2 = 2) := by
  split_ands
  · rfl
  · trivial
  · rfl
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `constructor` | 1 段階版 | `∧` を 1 回分割 |
| `refine ⟨?_, ?_⟩` | パターン版 | プレースホルダーで分割 |
| `and_iff_right` | 短縮 | 片方が自明な場合 |

---

## 参照

- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
