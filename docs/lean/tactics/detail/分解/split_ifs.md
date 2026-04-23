# `split_ifs` — if-then-else の一括展開

**カテゴリ**: 分解 | **定義元**: `Lean.Parser.Tactic.splitIfs` | **ソース**: Lean4 core

## 概要
`split_ifs` はゴールおよび仮定中のすべての `if-then-else` 式を一括で展開し、各条件の真偽の組み合わせに対応するサブゴールを生成する。`split` が最初の if/match のみを分割するのに対し、`split_ifs` は再帰的にすべての if 式を処理する。各分岐で条件が仮定として追加される。

## ゴールパターン

**適用前**（`split_ifs`）
```lean
⊢ (if p then (if q then a else b) else c) = d
```

**適用後**
```lean
-- ケース 1:
h₁ : p
h₂ : q
⊢ a = d

-- ケース 2:
h₁ : p
h₂ : ¬q
⊢ b = d

-- ケース 3:
h₁ : ¬p
⊢ c = d
```

## 構文
```lean
split_ifs                       -- ゴール中のすべての if を展開
split_ifs at h                  -- 仮定 h 中のすべての if を展開
split_ifs with h₁ h₂           -- 条件仮定に名前を付ける
split_ifs at h₁ h₂ ⊢           -- 複数の仮定とゴールを同時処理
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `split_ifs` | ゴール中のすべての if 式を展開 |
| `at h` | 仮定 h 中の if 式を展開 |
| `with h₁ h₂ ...` | 各条件の仮定に名前を付ける |
| `at h₁ h₂ ⊢` | 複数の仮定とゴールを同時に処理 |

## Pros
- ネストした if 式を一度に展開でき、`split` を繰り返す手間が不要
- 各分岐に条件が仮定として自動追加される
- `simp` と組み合わせて条件分岐の多い証明を効率的に処理可能

## Cons
- if 式が多いと $2^n$ 個のサブゴールが生成され、証明が爆発する
- すべての if を展開するため、一部だけ分割したい場合は `split` が適切
- 条件間の依存関係がある場合、不要なケースも生成される

## コードサンプル

### サンプル 1: ネストした if の展開
```lean
example (p q : Prop) [Decidable p] [Decidable q]
    (a b c d : Nat) :
    (if p then (if q then a else b) else c) ≥ 0 := by
  split_ifs
  -- 3つのサブゴール（すべて ⊢ _ ≥ 0）
  all_goals omega
```

### サンプル 2: 条件仮定に名前を付ける
```lean
example (n : Nat) : (if n = 0 then 1 else n) ≠ 0 := by
  split_ifs with h
  · -- h : n = 0 ⊢ 1 ≠ 0
    omega
  · -- h : ¬n = 0 ⊢ n ≠ 0
    exact h
```

### サンプル 3: 仮定中の if を展開
```lean
example (p : Prop) [Decidable p] (a b : Nat) (h : (if p then a else b) = 0) : a = 0 ∨ b = 0 := by
  split_ifs at h with h₁
  · -- h₁ : p, h : a = 0 ⊢ a = 0 ∨ b = 0
    left; exact h
  · -- h₁ : ¬p, h : b = 0 ⊢ a = 0 ∨ b = 0
    right; exact h
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `split` | 最初の if/match のみ分割 | 一つの if/match だけ処理したい場合 |
| `by_cases` | 排中律で分岐 | `Decidable` でない命題での分岐 |
| `simp` | 簡約 | 条件分岐後の簡約処理 |

## 参照
- [Lean4 公式リファレンス — split_ifs](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#split)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
