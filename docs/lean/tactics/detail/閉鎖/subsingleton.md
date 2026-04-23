# `subsingleton` — Subsingleton 型の等式を証明する

**カテゴリ**: 閉鎖 | **定義元**: `Mathlib.Tactic.Subsingleton.subsingleton` | **ソース**: Mathlib

---

## 概要

`subsingleton` は `Subsingleton α`（要素が高々 1 つの型）のインスタンスを利用して、任意の `a b : α` に対する `a = b` を証明するタクティクである。`Prop`、`Unit`、`PUnit` 等の subsingleton 型に対する等式を即座に閉じる。

---

## ゴールパターン

**適用前**
```lean
⊢ a = b  -- a b : α where Subsingleton α
```

**適用後**: ゴール閉鎖

---

## 構文

```lean
subsingleton
```

---

## 必須 import

```lean
import Mathlib.Tactic.Subsingleton
```

---

## オプション一覧

特になし。

---

## Pros（使うべき場面）

- `Subsingleton` 型の等式を即座に証明
- 証明の等式（`Prop` の HEq 等）の簡潔な処理
- `proof_irrel` の一般化

---

## Cons（注意・失敗ケース）

- `Subsingleton` インスタンスがない型には適用不可
- Mathlib import が必要
- 多くの場合 `rfl` や `trivial` で十分

---

## コードサンプル

### サンプル 1: Unit 型の等式

```lean
import Mathlib.Tactic.Subsingleton

example (a b : Unit) : a = b := by
  subsingleton
```

### サンプル 2: Prop の等式

```lean
import Mathlib.Tactic.Subsingleton

example (h₁ h₂ : 1 = 1) : h₁ = h₂ := by
  subsingleton
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `rfl` | 反射律 | 定義的に等しい場合 |
| `trivial` | 簡易閉鎖 | 基本的なゴールの閉鎖 |
| `congr` | 合同分解 | 引数ごとの分解 |

---

## 参照

- [Mathlib4 ドキュメント — Subsingleton](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Subsingleton.html)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
