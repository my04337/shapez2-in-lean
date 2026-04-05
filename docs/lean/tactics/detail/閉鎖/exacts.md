# `exacts` — 候補リストから exact を試行する

**カテゴリ**: 閉鎖 | **定義元**: `Mathlib.Tactic.exacts` | **ソース**: Mathlib

---

## 概要

`exacts [e₁, e₂, ...]` は指定した項のリストを順に `exact` で試行し、最初に成功したもので ゴールを閉じるタクティクである。`first [exact e₁, exact e₂, ...]` の糖衣構文。

---

## ゴールパターン

**適用前**
```lean
h₁ : P
h₂ : Q
⊢ P
```

**適用後**（`exacts [h₁, h₂]`）: `h₁` でゴール閉鎖

---

## 構文

```lean
exacts [e₁, e₂, e₃]
```

---

## 必須 import

```lean
import Mathlib.Tactic.Core
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `exacts [e₁, e₂]` | `e₁`, `e₂` を順に `exact` で試行 |

---

## Pros（使うべき場面）

- 複数の候補からゴールを閉じる場合に 1 行で試行
- `first` + `exact` の簡潔な代替

---

## Cons（注意・失敗ケース）

- 全候補が失敗すると全体が失敗
- `assumption` で十分な場合はそちらが簡潔
- Mathlib import が必要

---

## コードサンプル

### サンプル 1: 基本的な使い方

```lean
import Mathlib.Tactic.Core

-- constructor で 2 ゴールを作り、exacts で一括適用
example (h₁ : True) (h₂ : 1 = 1) : True ∧ 1 = 1 := by
  constructor
  exacts [h₁, h₂]
```

### サンプル 2: 複数ゴールへの一括適用

```lean
import Mathlib.Tactic.Core

example (h : 1 = 1) : 1 = 1 ∧ True := by
  constructor
  exacts [h, trivial]
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `exact` | 単一版 | 1 つの項でゴールを閉じる |
| `assumption` | 仮定探索 | 仮定から自動選択するなら |
| `first` | 汎用分岐 | 任意のタクティクを順に試行 |

---

## 参照

- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
