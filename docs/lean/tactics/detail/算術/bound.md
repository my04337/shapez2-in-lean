# `bound` — @[bound] 補題で不等式を証明する

**カテゴリ**: 算術 | **定義元**: `Mathlib.Tactic.Bound` | **ソース**: Mathlib

---

## 概要

`bound` は `@[bound]` 属性が付いた補題を使って不等式ゴールを自動的に証明するタクティクである。単調性補題や非負性補題を組み合わせ、`linarith` や `positivity` では処理しにくい非線形不等式の証明に強い。

---

## ゴールパターン

**適用前**
```lean
⊢ 0 ≤ f x * g y
```

**適用後**: `@[bound]` 補題で閉鎖

---

## 構文

```lean
bound
```

---

## 必須 import

```lean
import Mathlib.Tactic.Bound
```

---

## オプション一覧

特になし。自動的に `@[bound]` 属性の補題を探索する。

---

## Pros（使うべき場面）

- 非負性・単調性を組み合わせた不等式の証明
- `positivity` が失敗する複合的な不等式
- `@[bound]` タグ付き補題の自動適用

---

## Cons（注意・失敗ケース）

- 適切な `@[bound]` 補題がないと何もできない
- Mathlib import が必要
- 線形不等式なら `linarith` / `omega` の方が確実

---

## コードサンプル

### サンプル 1: 基本的な不等式

```lean
import Mathlib.Tactic.Bound

example (x : Nat) : 0 ≤ x := by
  bound
```

### サンプル 2: positivity との比較

```lean
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Positivity

-- bound: @[bound] 補題ベース（単調性・非負性）
-- positivity: 正値性の構造的証明
example (x : Nat) : 0 ≤ x * x := by
  bound
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `positivity` | 正値性証明 | 0 < / 0 ≤ の構造的証明 |
| `linarith` | 線形不等式 | 線形な不等式の組み合わせ |
| `omega` | 整数算術 | 整数の線形算術 |
| `norm_num` | 数値計算 | 具体的数値の評価 |

---

## 参照

- [Mathlib4 ドキュメント — Bound](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Bound.html)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
