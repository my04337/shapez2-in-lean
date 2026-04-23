# `substs` — 指定した仮定リストに subst を適用する

**カテゴリ**: 変換 | **定義元**: `Mathlib.Tactic.Substs.substs` | **ソース**: Mathlib

---

## 概要

`substs h₁ h₂ ...` は指定した等式仮定に対し、順番に `subst` を適用する Mathlib タクティクである。`subst h₁; subst h₂` のように複数回書く代わりに 1 行にまとめられる。`subst_eqs` のように全自動ではなく、対象を明示的に制御できる。

---

## ゴールパターン

**適用前**
```lean
a b : Nat
h₁ : a = 1
h₂ : b = 2
⊢ a + b = 3
```

**適用後**（`substs h₁ h₂`）
```lean
⊢ 1 + 2 = 3
```

---

## 構文

```lean
substs h₁ h₂ h₃
```

- 等式仮定を順に指定。先に指定した仮定から `subst` される

---

## 必須 import

```lean
import Mathlib.Tactic.Substs
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `substs h₁ h₂` | `h₁`, `h₂` の順に `subst` を適用 |

---

## Pros（使うべき場面）

- 消去する仮定を明示的に制御でき、意図が明確
- `subst_eqs` では消去順序が原因で失敗するケースを回避できる
- 複数の `subst` を 1 行にまとめられる

---

## Cons（注意・失敗ケース）

- Mathlib import が必要
- `subst` と同じ制約（変数等式のみ対象）
- 全自動で良い場合は `subst_eqs` の方が簡潔

---

## コードサンプル

### サンプル 1: 順序指定で消去

```lean
import Mathlib.Tactic.Substs

example (a b : Nat) (h₁ : a = 1) (h₂ : b = 2) : a + b = 3 := by
  substs h₁ h₂
  rfl
```

### サンプル 2: 単一仮定

```lean
import Mathlib.Tactic.Substs

example (n : Nat) (h : n = 0) : n = 0 := by
  substs h
  rfl
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `subst` | 単一版 | 1 つだけなら `subst` |
| `subst_eqs` | 全自動版 | 全等式を一括消去するなら `subst_eqs` |
| `subst_vars` | 変数等式一括 | 変数等式のみ一括なら `subst_vars` |

---

## 参照

- [Mathlib4 ドキュメント — Substs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Substs.html)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
