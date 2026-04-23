# `push_neg` — 否定を量化子・結合子の内側に押し込む

**カテゴリ**: 変換 | **定義元**: `Mathlib.Tactic.PushNeg.tacticPush_neg_` | **ソース**: Mathlib

---

## 概要

`push_neg` は否定（`¬`）を量化子（`∀`, `∃`）や論理結合子（`∧`, `∨`, `→`）の内側に押し込み、
否定を正規化するタクティクである。例えば `¬∀ x, P x` を `∃ x, ¬P x` に変換する。
`by_contra` の後に使うのが典型的なパターンである。

---

## ゴールパターン

**適用前**
```lean
⊢ ¬∀ x, P x
```

**適用後**
```lean
⊢ ∃ x, ¬P x
```

---

## 構文

```lean
push_neg
push_neg at h
push_neg at h₁ h₂ ⊢
push_neg at *
```

---

## 必須 import

```lean
import Mathlib.Tactic.PushNeg
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `push_neg` | ゴールの否定を内側に押し込む |
| `push_neg at h` | 仮定 `h` の否定を内側に押し込む |
| `push_neg at *` | ゴールと全仮定に適用する |

---

## Pros（使うべき場面）

- `by_contra` 後の `¬P` を扱いやすい形に変換できる
- ド・モルガンの法則や量化子の否定を自動適用するため手動での変換が不要
- 不等式の否定（`¬(a < b)` → `b ≤ a`）にも対応する

---

## Cons（注意・失敗ケース）

- Mathlib のインポートが必要（Lean4 core 単体では使えない）
- 否定の正規化が期待と異なる形になる場合がある
- 複雑なネスト構造では一度で完全に正規化されないことがある

---

## コードサンプル

### サンプル 1: 全称の否定を存在に変換

```lean
import Mathlib.Tactic.PushNeg

example : ¬∀ n : Nat, n > 0 := by
  -- ⊢ ¬∀ n : Nat, n > 0
  push_neg
  -- ⊢ ∃ n, n ≤ 0
  exact ⟨0, le_refl 0⟩
```

### サンプル 2: 仮定の否定を正規化

```lean
import Mathlib.Tactic.PushNeg

example (a b c : Nat) (h : ¬(a < b ∨ b < c)) : a ≥ b ∧ b ≥ c := by
  -- h : ¬(a < b ∨ b < c)
  push_neg at h
  -- h : a ≥ b ∧ b ≥ c
  exact h
```

### サンプル 3: by_contra + push_neg パターン

```lean
import Mathlib.Tactic.PushNeg

example (n : Nat) (h : n ≠ 0) : n > 0 := by
  -- ⊢ n > 0
  by_contra h_neg
  -- h_neg : ¬n > 0
  push_neg at h_neg
  -- h_neg : n ≤ 0
  omega
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `by_contra` | 前段 | 背理法で `¬P` を仮定に入れた後、`push_neg` で正規化する |
| `simp` | 代替 | `simp only [not_forall, not_exists]` で部分的に代用可能 |
| `contrapose` | 別手法 | 対偶変換。`push_neg` + `by_contra` の代替になる場合がある |
| `tauto` | 自動化 | 命題論理レベルなら `tauto` で自動証明できる場合がある |

---

## 参照

- [Mathlib4 ドキュメント — push_neg](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/PushNeg.html)
- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
