# `fapply` — サブゴール順序固定の apply

**カテゴリ**: 補題適用 | **定義元**: `Lean.Elab.Tactic.evalApply` | **ソース**: Lean4 core

---

## 概要

`fapply h` は `apply h` と同様に `h` をゴールに適用するが、全てのサブゴール（推論可能な引数を含む）を明示的にサブゴールとして生成し、メタ変数の統合による自動解決を行わない。引数の順序が重要な場合や、自動推論に任せたくない場合に使う。

---

## ゴールパターン

**適用前**
```lean
⊢ Q
-- h : P₁ → P₂ → Q
```

**適用後**（`fapply h`）
```lean
⊢ P₁
⊢ P₂
```

---

## 構文

```lean
fapply h
fapply h arg₁ arg₂
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `fapply h` | 全引数をサブゴールとして生成 |
| `fapply h a` | 一部を埋めて残りをサブゴール化 |

---

## Pros（使うべき場面）

- メタ変数の自動統合を避けたい場合
- サブゴールの順序を固定したい場合
- `apply` が間違った統合をする場合の代替

---

## Cons（注意・失敗ケース）

- 推論可能な引数もサブゴールになるため冗長になる場合がある
- 多くの場合は `apply` で十分
- `refine` でプレースホルダを制御する方が柔軟な場合も

---

## コードサンプル

### サンプル 1: 基本的な使用

```lean
example (h : ∀ n : Nat, n = n → True) : True := by
  fapply h
  · exact 42
  · rfl
```

### サンプル 2: apply との違い

```lean
-- apply: 推論可能な引数は自動統合
-- fapply: 全引数がサブゴールに
example (h : ∀ (n : Nat), n = n → True) : True := by
  fapply h 0
  rfl
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `apply` | 標準版 | 自動推論に任せるなら `apply` |
| `exact` | 完全適用 | 引数が全て揃っているなら `exact` |
| `refine` | プレースホルダ版 | `?_` で制御するなら `refine` |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
