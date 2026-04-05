# `filter_upwards` — フィルタ所属ゴールの ∀ 形式への変換

**カテゴリ**: 特化 | **定義元**: `Mathlib.Tactic.filterUpwards` | **ソース**: Mathlib

---

## 概要

`filter_upwards` はフィルタ（`Filter`）の所属ゴール `s ∈ f` や `∀ᶠ x in f, P x` を、
使用する仮定のフィルタ集合の共通部分上での `∀` 命題に変換するタクティクである。
フィルタの単調性（`Filter.mem_of_superset`）と有限交叉（`Filter.inter_mem`）を自動適用し、
最終的に `∀ x, (仮定の条件) → (ゴールの条件)` の形に帰着する。
測度論・位相・解析で頻出するフィルタ論法の定型証明を簡潔にする。

---

## ゴールパターン

**適用対象**: `s ∈ f` または `∀ᶠ x in f, P x` 形式のゴール

**適用前**
```lean
h₁ : ∀ᶠ x in f, P x
h₂ : ∀ᶠ x in f, Q x
⊢ ∀ᶠ x in f, P x ∧ Q x
```

**適用後** (`filter_upwards [h₁, h₂]`)
```lean
-- x : α, hP : P x, hQ : Q x
-- ⊢ P x ∧ Q x
```

---

## 構文

```lean
filter_upwards                    -- 仮定なしで単調性のみ
filter_upwards [h₁, h₂, ...]     -- 仮定のフィルタ集合を使用
filter_upwards [h₁] with x hx    -- intro パターン付き
```

---

## 必須 import

```lean
import Mathlib.Order.Filter.Basic
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `filter_upwards` | 仮定なしでフィルタの単調性を適用 |
| `filter_upwards [h₁, h₂]` | 仮定のフィルタ集合の交叉上で帰着 |
| `filter_upwards [h₁] with x hx` | `intro` パターンを指定 |
| `filter_upwards [h₁] using tac` | 帰着後にタクティクを適用 |

---

## Pros（使うべき場面）

- フィルタ論法の定型的な証明手順を自動化する
- `Filter.inter_mem` + `Filter.mem_of_superset` + `intro` の組み合わせを 1 行で実現
- `with` を使って導入変数名を直接指定できる

---

## Cons（注意・失敗ケース）

- フィルタ固有のタクティクなので、フィルタ以外の文脈では使えない
- 仮定のフィルタが一致しない場合は失敗する
- 帰着後のゴールが自明でない場合は追加のタクティクが必要

---

## コードサンプル

### サンプル 1: 2 つの条件の結合

```lean
import Mathlib.Order.Filter.Basic

example {f : Filter α} {P Q : α → Prop}
    (hP : ∀ᶠ x in f, P x) (hQ : ∀ᶠ x in f, Q x) :
    ∀ᶠ x in f, P x ∧ Q x := by
  -- ⊢ ∀ᶠ x in f, P x ∧ Q x
  filter_upwards [hP, hQ] with x hp hq
  -- x : α, hp : P x, hq : Q x
  -- ⊢ P x ∧ Q x
  exact ⟨hp, hq⟩
```

### サンプル 2: 単調性による帰着

```lean
import Mathlib.Order.Filter.Basic

example {f : Filter α} {P Q : α → Prop}
    (h : ∀ᶠ x in f, P x) (hpq : ∀ x, P x → Q x) :
    ∀ᶠ x in f, Q x := by
  -- ⊢ ∀ᶠ x in f, Q x
  filter_upwards [h] with x hx
  -- x : α, hx : P x
  -- ⊢ Q x
  exact hpq x hx
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `apply Filter.mem_of_superset` | 手動版 | `filter_upwards` の内部で使われる操作を手動で行う |
| `intro` | 後処理 | `filter_upwards` 後の `∀` を手動で導入 |
| `simp` | 簡約 | フィルタ補題の簡約に使う |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
