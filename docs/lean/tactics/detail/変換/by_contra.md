# `by_contra` — 背理法によるゴール変換

**カテゴリ**: 変換 | **定義元**: `Lean.Parser.Tactic.byContra` | **ソース**: Lean4 core

---

## 概要

`by_contra` は背理法（proof by contradiction）を適用するタクティクである。
ゴール `⊢ P` に対して `by_contra h` を使うと、仮定に `h : ¬P` が追加されゴールが `⊢ False` に変わる。
古典論理（`Classical.em`）を暗黙的に使用するため、構成的証明が不要な場面で有効。

---

## ゴールパターン

**適用前**
```lean
⊢ P
```

**適用後（`by_contra h`）**
```lean
h : ¬P
⊢ False
```

---

## 構文

```lean
by_contra h
by_contra
```

- `h`: 否定仮定 `¬P` に付ける名前（省略すると自動で名付けられる）

---

## 必須 import

Lean4 core 組み込みのため不要。ただし古典論理（`Classical`）が必要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `by_contra h` | `h : ¬P` を仮定に追加し、ゴールを `False` にする |
| `by_contra` | 名前を省略（自動命名） |

---

## Pros（使うべき場面）

- 直接証明が困難な命題を、否定を仮定して矛盾を導く形に変換できる
- 排中律を前提とした古典的推論が自然に記述できる
- 特に不等式や存在命題の否定を扱う場合に有効

---

## Cons（注意・失敗ケース）

- 古典論理を使うため、構成的証明が必要な場面では使えない
- `by_contra` 後に矛盾を導くのが困難な場合、証明が行き詰まりやすい
- `push_neg` と組み合わせないと `¬P` の扱いが煩雑になることがある

---

## コードサンプル

### サンプル 1: 基本的な背理法

```lean
example (n : Nat) (h : n ≠ 0) : n ≥ 1 := by
  -- ⊢ n ≥ 1
  by_contra h_neg
  -- h_neg : ¬n ≥ 1
  -- ⊢ False
  omega
```

### サンプル 2: 排中律を利用

```lean
example (p : Prop) [Decidable p] : p ∨ ¬p := by
  -- ⊢ p ∨ ¬p
  by_contra h
  -- h : ¬(p ∨ ¬p)
  -- ⊢ False
  push_neg at h
  exact h.1 h.2
```

### サンプル 3: 不等式の証明

```lean
example (a b : Nat) (h : a + b > 0) : a > 0 ∨ b > 0 := by
  -- ⊢ a > 0 ∨ b > 0
  by_contra h_neg
  -- h_neg : ¬(a > 0 ∨ b > 0)
  -- ⊢ False
  push_neg at h_neg
  omega
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `exfalso` | 前段 | ゴールを `False` に変換するだけ（否定仮定は追加しない） |
| `push_neg` | 後続 | `by_contra` 後の `¬P` を量化子の内側に押し込む |
| `contradiction` | 閉鎖 | 仮定同士の矛盾を自動検出して `False` を導く |
| `contrapose` | 対偶 | 背理法ではなく対偶 `¬Q → ¬P` に変換する |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
