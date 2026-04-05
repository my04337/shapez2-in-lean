# `symm` — 対称性を適用してゴールを反転する

**カテゴリ**: 変換 | **定義元**: `Lean.Parser.Tactic.symm` | **ソース**: Lean4 core

---

## 概要

`symm` は `@[symm]` 属性が付与された対称性補題を適用するタクティクである。
典型的には等式 `a = b` を `b = a` に反転する。
`Iff`（`↔`）など `@[symm]` 属性を持つ他の関係にも適用可能。
`at h` で仮定に対しても使用できる。

---

## ゴールパターン

**適用前**
```lean
⊢ a = b
```

**適用後**
```lean
⊢ b = a
```

---

## 構文

```lean
symm
symm at h
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `symm` | ゴールに対称性を適用する |
| `symm at h` | 仮定 `h` に対称性を適用する |

---

## Pros（使うべき場面）

- 等式の向きが合わない場合に、1 ステップで反転できる
- `Eq.symm` を手動で書くより簡潔で宣言的
- `@[symm]` 属性を持つ任意の関係（`Iff`, カスタム同値関係等）に対応

---

## Cons（注意・失敗ケース）

- ゴールが `@[symm]` 属性を持たない関係の場合は失敗する
- 不等式（`<`, `≤`）には適用できない（対称的でないため）
- `rw [eq_comm]` でも同等の効果が得られるため、好みの問題になる場合がある

---

## コードサンプル

### サンプル 1: 等式の反転

```lean
example (h : a = b) : b = a := by
  -- ⊢ b = a
  symm
  -- ⊢ a = b
  exact h
```

### サンプル 2: 仮定の反転

```lean
example (h : b = a) : a = b := by
  -- h : b = a
  -- ⊢ a = b
  symm at h
  -- h : a = b
  exact h
```

### サンプル 3: Iff の反転

```lean
example (h : P ↔ Q) : Q ↔ P := by
  -- ⊢ Q ↔ P
  symm
  -- ⊢ P ↔ Q
  exact h
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `rw [eq_comm]` | 代替 | 等式の反転は `rw [eq_comm]` でも可能 |
| `trans` | 推移律 | `symm` は対称性、`trans` は推移律。組み合わせて使う |
| `congr` | 構造分解 | 等式の両辺の構造を分解する。`symm` は向きの反転のみ |
| `Eq.symm` | 項レベル | `exact h.symm` のようにドット記法で項レベルで使用 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
