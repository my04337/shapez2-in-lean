# `tauto_set` — 集合の命題論理的解決

**カテゴリ**: 自動化 | **定義元**: `Mathlib.Tactic.TautoSet` | **ソース**: Mathlib

---

## 概要

`tauto_set` は集合に関する命題論理的なゴール（和集合、共通集合、補集合、包含関係等の組み合わせ）を自動的に証明するタクティクである。集合操作を論理結合子に変換し、命題論理で閉じる。

---

## ゴールパターン

**適用前**
```lean
⊢ s ∩ t ⊆ s
```

**適用後**: 自動閉鎖

---

## 構文

```lean
tauto_set
```

---

## 必須 import

```lean
import Mathlib.Tactic.TautoSet
```

---

## オプション一覧

特になし。

---

## Pros（使うべき場面）

- 集合の包含関係・等式の命題論理的証明
- `∩`, `∪`, `ᶜ`, `⊆` の組み合わせの自動処理
- `ext` + `simp` で冗長になる証明の簡潔化

---

## Cons（注意・失敗ケース）

- 命題論理で閉じない場合（量化子が絡む等）は失敗
- Mathlib import が必要
- 集合以外のゴールには無効

---

## コードサンプル

### サンプル 1: 基本的な包含

```lean
import Mathlib.Tactic.TautoSet

variable {α : Type} (s t : Set α)

example : s ∩ t ⊆ s := by
  tauto_set
```

### サンプル 2: 和集合と共通集合

```lean
import Mathlib.Tactic.TautoSet

variable {α : Type} (s t u : Set α)

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) := by
  tauto_set
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `tauto` | 命題論理版 | 一般命題の命題論理的証明 |
| `simp` | 汎用簡約 | 集合補題で簡約 |
| `ext` | 外延性 | 集合の等式を要素レベルに分解 |

---

## 参照

- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
