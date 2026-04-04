# `rel` — @[gcongr] で関係を分解する

**カテゴリ**: 特化 | **定義元**: `Mathlib.Tactic.GCongr` | **ソース**: Mathlib

---

## 概要

`rel [h₁, h₂]` は `@[gcongr]` 属性付きの単調性補題を使って、不等式や順序関係を構成要素に分解するタクティクである。`gcongr` の別構文で、提供する補題を明示的に指定して関係式を分解する。

---

## ゴールパターン

**適用前**
```lean
⊢ f a ≤ f b
```

**適用後**（`rel [h]` で `h : a ≤ b`）
```lean
（閉鎖）
```

---

## 構文

```lean
rel [h₁, h₂]
```

---

## 必須 import

```lean
import Mathlib.Tactic.GCongr
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `rel [h₁]` | 仮定 `h₁` を使って関係を分解 |
| `rel [h₁, h₂]` | 複数仮定で順に分解 |

---

## Pros（使うべき場面）

- 単調関数の不等式を引数の不等式に分解
- `gcongr` と同じ効果を明示的な補題指定で
- `linarith` が非線形で失敗する場合の代替

---

## Cons（注意・失敗ケース）

- `@[gcongr]` 補題がないと失敗
- 線形不等式なら `linarith` / `omega` の方が確実
- Mathlib import が必要

---

## コードサンプル

### サンプル 1: 基本的な使用

```lean
import Mathlib.Tactic.GCongr

-- 型注釈で型推論を补助する
example (a b c : Nat) (h : a ≤ b) : a + c ≤ b + c := by
  rel [h]
```

### サンプル 2: 複数の不等式

```lean
import Mathlib.Tactic.GCongr

-- 型注釈で型推論を补助する
example (a b c d : Nat) (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  rel [h₁, h₂]
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `gcongr` | 自動版 | 自動で単調性補題を探すなら `gcongr` |
| `linarith` | 線形版 | 線形不等式なら `linarith` |
| `omega` | 整数版 | 整数線形算術なら `omega` |
| `mono` | 旧版 | `rel`/`gcongr` の前身 |

---

## 参照

- [Mathlib4 ドキュメント — GCongr](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/GCongr.html)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
