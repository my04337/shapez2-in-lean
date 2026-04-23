# `trans` — 推移律でゴールを分割する

**カテゴリ**: 変換 | **定義元**: `Batteries.Tactic.tacticTrans___` | **ソース**: Batteries

---

## 概要

`trans` は推移的な関係 `t ~ u` を中間項 `s` を経由して `t ~ s` と `s ~ u` の 2 つのサブゴールに分割するタクティクである。
等式（`=`）、不等式（`≤`, `<`）、その他 `@[trans]` 属性を持つ関係に適用できる。
`trans s` のように中間項を明示的に指定するか、省略して推論に任せる。

---

## ゴールパターン

**適用前**
```lean
⊢ a = c
```

**適用後（`trans b`）**
```lean
-- ゴール 1: ⊢ a = b
-- ゴール 2: ⊢ b = c
```

---

## 構文

```lean
trans
trans middle
```

- `middle`: 中間項（省略するとメタ変数が生成される）

---

## 必須 import

Batteries に含まれるため、Mathlib を使用していれば追加 import 不要。
Lean4 core 単体の場合:

```lean
import Batteries.Tactic.Trans
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `trans` | 中間項を推論に任せて分割する |
| `trans e` | 中間項 `e` を指定して分割する |

---

## Pros（使うべき場面）

- 等式や不等式を段階的に証明する際の基本操作
- `calc` ブロックを使うほどではない短い推移律の適用に適している
- 等式以外にも `@[trans]` 属性の関係（`≤`, `<`, 整除関係など）に使える

---

## Cons（注意・失敗ケース）

- 中間項を省略するとユニフィケーションに失敗する場合がある
- 3 段階以上の推移律は `calc` ブロックの方が可読性が高い
- ゴールが `@[trans]` 属性を持たない関係の場合は失敗する

---

## コードサンプル

### サンプル 1: 等式の分割

```lean
example (h1 : a = b) (h2 : b = c) : a = c := by
  -- ⊢ a = c
  trans b
  -- ゴール 1: ⊢ a = b
  -- ゴール 2: ⊢ b = c
  · exact h1
  · exact h2
```

### サンプル 2: 不等式の推移律

```lean
example (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  -- ⊢ a ≤ c
  trans b
  -- ゴール 1: ⊢ a ≤ b
  -- ゴール 2: ⊢ b ≤ c
  · exact h1
  · exact h2
```

### サンプル 3: 中間項を省略

```lean
example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  -- ⊢ a = c
  trans
  -- ゴール 1: ⊢ a = ?middle
  -- ゴール 2: ⊢ ?middle = c
  · exact h1
  · exact h2
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `calc` | 拡張 | 複数ステップの推移的証明には `calc` の方が可読性が高い |
| `symm` | 対称律 | `symm` は対称性、`trans` は推移律で相補的 |
| `Eq.trans` | 項レベル | `exact h1.trans h2` のようにドット記法で使用可能 |
| `le_trans` | 特化版 | `≤` 専用の推移律補題 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
