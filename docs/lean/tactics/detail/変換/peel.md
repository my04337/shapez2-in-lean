# `peel` — 量化子の外側を剥がす

**カテゴリ**: 変換 | **定義元**: `Mathlib.Tactic.Peel.peel` | **ソース**: Mathlib

---

## 概要

`peel` は仮定とゴールの最外層の量化子（`∀`、`∃`）や含意（`→`）を同時に剥がすタクティクである。
仮定 `h : ∀ x, P x` とゴール `⊢ ∀ x, Q x` がある場合、
`peel h` で両方から `∀ x` を除去し、`h' : P x ⊢ Q x` の形に帰着する。
量化子のネストが深い命題の証明で、`intro` と `specialize` の繰り返しを 1 行に圧縮できる。

---

## ゴールパターン

**適用対象**: `∀`、`∃`、`→` を含む命題

**適用前**
```lean
h : ∀ x, P x → Q x
⊢ ∀ x, P x → R x
```

**適用後** (`peel h with x hpq`)
```lean
x : α
hpq : P x → Q x
hp : P x            -- → を剥がした場合
⊢ R x
```

---

## 構文

```lean
peel h                          -- h とゴールの量化子を一致させて剥がす
peel h with x₁ x₂ ...          -- 導入変数名を指定
peel n h                        -- n 層分だけ剥がす
```

---

## 必須 import

```lean
import Mathlib.Tactic.Peel
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `peel h` | `h` とゴールの最外層量化子を剥がす |
| `peel h with x₁ x₂ ...` | 導入変数名を指定して剥がす |
| `peel n h` | `n` 層分の量化子を剥がす |

---

## Pros（使うべき場面）

- `∀` や `∃` のネストした命題を効率的に分解できる
- `intro` + `specialize` + `obtain` の手動チェーンを 1 行に圧縮
- 仮定とゴールの構造が類似している場合に特に有効

---

## Cons（注意・失敗ケース）

- 仮定とゴールの量化子構造が対応していない場合は失敗する
- `∃` の場合、witness が仮定から取得されるため、異なる witness を使いたい場合は不向き
- 剥がし過ぎるとゴールが不自然な形になることがある

---

## コードサンプル

### サンプル 1: ∀ の剥がし

```lean
import Mathlib.Tactic.Peel

example (h : ∀ n : Nat, n + 0 = n) : ∀ n : Nat, n = n + 0 := by
  -- ⊢ ∀ n, n = n + 0
  peel h with n hn
  -- n : Nat, hn : n + 0 = n
  -- ⊢ n = n + 0
  omega
```

### サンプル 2: ∃ の剥がし

```lean
import Mathlib.Tactic.Peel

example (h : ∃ n : Nat, n > 5) : ∃ n : Nat, n > 3 := by
  -- ⊢ ∃ n, n > 3
  peel h with n hn
  -- n : Nat, hn : n > 5
  -- ⊢ n > 3
  omega
```

### サンプル 3: 複数層の剥がし

```lean
import Mathlib.Tactic.Peel

example (h : ∀ x : Nat, ∀ y : Nat, x + y = y + x) :
    ∀ x : Nat, ∀ y : Nat, y + x = x + y := by
  -- ⊢ ∀ x y, y + x = x + y
  peel h with x y hxy
  -- x y : Nat, hxy : x + y = y + x
  -- ⊢ y + x = x + y
  omega
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `intro` | 手動導入 | ゴールの `∀` を 1 つずつ手動で剥がす |
| `specialize` | 仮定の特殊化 | 仮定の `∀` に具体値を代入する |
| `obtain` | 存在分解 | `∃` の仮定を分解する |
| `apply` | 含意適用 | ゴールの含意の先頭を仮定で埋める |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
