# `contrapose` — ゴールを対偶に変換する

**カテゴリ**: 変換 | **定義元**: `Mathlib.Tactic.Contrapose.contrapose` | **ソース**: Mathlib

---

## 概要

`contrapose` はゴール `P → Q` を対偶 `¬Q → ¬P` に変換するタクティクである。
仮定 `h : P` が存在する場合、ゴールが `⊢ Q` であれば `h : ¬Q` に変わりゴールが `⊢ ¬P` になる。
`contrapose!` は変換後にさらに `push_neg` を自動適用する便利バリアントである。

---

## ゴールパターン

**適用前**
```lean
h : P
⊢ Q
```

**適用後（`contrapose`）**
```lean
h : ¬Q
⊢ ¬P
```

---

## 構文

```lean
contrapose
contrapose!
contrapose! h
```

---

## 必須 import

```lean
import Mathlib.Tactic.Contrapose
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `contrapose` | ゴールを対偶に変換する |
| `contrapose!` | 対偶変換後に `push_neg` を自動適用する |
| `contrapose! h` | 仮定 `h` を指定して対偶変換する |

---

## Pros（使うべき場面）

- 直接証明より対偶の方が容易な場合に、証明を劇的に簡潔にできる
- `contrapose!` で `push_neg` まで一度に行えるため、手順が減る
- 背理法（`by_contra`）より論理的に軽量（`False` を経由しない）

---

## Cons（注意・失敗ケース）

- Mathlib のインポートが必要
- ゴールが `P → Q` の形（仮定に `P` がある状態で `⊢ Q`）でないと適用できない
- 否定が二重否定として残ることがあり、`push_neg` や `simp` で整理が必要

---

## コードサンプル

### サンプル 1: 基本的な対偶変換

```lean
import Mathlib.Tactic.Contrapose

example (n : Nat) : n ≠ 0 → 0 < n := by
  contrapose
  -- ⊢ ¬(0 < n) → n = 0
  push_neg
  -- ⊢ n = 0 → n = 0
  intro h; omega
```

### サンプル 2: contrapose! で push_neg を自動適用

```lean
import Mathlib.Tactic.Contrapose

example (n : Nat) : n ≥ 1 → n ≠ 0 := by
  contrapose!
  -- ⊢ n = 0 → n < 1
  intro h
  omega
```

### サンプル 3: 含意の対偶

```lean
import Mathlib.Tactic.Contrapose

example (a b : Nat) (h : a ≤ b) : a = 0 ∨ b ≥ 1 := by
  -- h : a ≤ b
  -- ⊢ a = 0 ∨ b ≥ 1
  by_contra h_neg
  push_neg at h_neg
  omega
```

---

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `contrapose!` | 対偶変換後に `push_neg` を自動適用する |

## 関連タクティク
| `push_neg` | 後続 | `contrapose` 後の否定を正規化。`contrapose!` は自動で適用 |
| `tauto` | 自動化 | 命題論理レベルの対偶は `tauto` で自動証明可能な場合がある |

---

## 参照

- [Mathlib4 ドキュメント — contrapose](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Contrapose.html)
- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
