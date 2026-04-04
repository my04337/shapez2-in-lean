# `calc` — 段階的な計算証明

**カテゴリ**: 変換 | **定義元**: `Lean.calcTactic` | **ソース**: Lean4 core

---

## 概要

`calc` は等式・不等式の連鎖を段階的に記述する計算証明ブロックである。
各ステップで推移律（transitivity）を自動適用し、中間式を経由して最終的な等式・不等式を証明する。
数学的な計算を自然な形で記述できるため、可読性の高い証明が書ける。

---

## ゴールパターン

**適用前**
```lean
⊢ a = d
```

**適用後（`calc a = b := ... _ = c := ... _ = d := ...`）**
```lean
-- 各ステップが個別のサブゴールになる
```

---

## 構文

```lean
calc
  lhs₁ rel₁ rhs₁ := proof₁
  _ rel₂ rhs₂ := proof₂
  _ rel₃ rhs₃ := proof₃
```

- 各行の `_` は前行の右辺を参照する
- `rel` は `=`, `≤`, `<`, `≥`, `>` など `@[trans]` 属性を持つ関係

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `_ = rhs := proof` | 等式ステップ |
| `_ ≤ rhs := proof` | 不等式ステップ（`≤`, `<` の混合も可） |
| `_ = rhs := by tac` | タクティクによるステップ証明 |

---

## Pros（使うべき場面）

- 数学的な等式変形を段階的に記述でき、証明の流れが非常に明瞭
- 等式と不等式を混合できる（例: `a = b`, `b ≤ c`, `c < d` の連鎖）
- 各ステップが独立したサブゴールになるため、デバッグが容易

---

## Cons（注意・失敗ケース）

- `@[trans]` 属性の推移律が登録されていない関係には使えない
- 中間式の右辺を手動で書く必要がある（自動推論されない）
- 単純な `rw` チェインで済む場合は `calc` は冗長

---

## コードサンプル

### サンプル 1: 等式の連鎖

```lean
example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  calc a = b := h1
    _ = c := h2
```

### サンプル 2: 算術計算

```lean
example (n : Nat) : (n + 1) * 2 = 2 * n + 2 := by
  calc (n + 1) * 2
    _ = n * 2 + 1 * 2 := by ring
    _ = 2 * n + 2 := by ring
```

### サンプル 3: 等式と不等式の混合

```lean
example (a b : Nat) (h1 : a = b) (h2 : b ≤ b + 1) : a ≤ b + 1 := by
  calc a = b := h1
    _ ≤ b + 1 := h2
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `trans` | 要素 | `trans` は 1 ステップの推移律適用。`calc` は複数ステップの連鎖 |
| `rw` | 代替 | 単純な等式書き換えの連鎖は `rw [h1, h2, ...]` の方が簡潔 |
| `ring` | ステップ証明 | `calc` 内のステップで環の計算を自動証明する |
| `omega` | ステップ証明 | `calc` 内のステップで線形算術を自動証明する |
| `linarith` | ステップ証明 | `calc` 内のステップで線形不等式を自動証明する |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Theorem Proving in Lean 4 — Calculational Proofs](https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html#calculational-proofs)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
