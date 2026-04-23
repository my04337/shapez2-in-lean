# `split` — if/match 式のサブゴール分割

**カテゴリ**: 分解 | **定義元**: `Lean.Parser.Tactic.split` | **ソース**: Lean4 core

## 概要
`split` はゴールまたは仮定中の `if-then-else` や `match` 式を条件ごとのサブゴールに分割する。`Decidable` な条件に基づき、各分岐を個別に証明できる。`split_ifs` がすべての if 式を一括展開するのに対し、`split` は最初の if/match のみを分割する。

## ゴールパターン

**適用前**（`split`）
```lean
⊢ (if p then a else b) = c
```

**適用後**
```lean
-- ケース 1:
h✝ : p
⊢ a = c

-- ケース 2:
h✝ : ¬p
⊢ b = c
```

**match 式の場合**（`split`）
```lean
⊢ (match n with | 0 => a | n + 1 => b) = c
```

**適用後**
```lean
-- ケース 1:
⊢ a = c

-- ケース 2:
n✝ : Nat
⊢ b = c
```

## 構文
```lean
split                           -- ゴール中の最初の if/match を分割
split at h                      -- 仮定 h 中の if/match を分割
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `split` | ゴール中の最初の if/match を分割 |
| `split at h` | 仮定 `h` 中の if/match を分割 |

## Pros
- if/match 式を明示的に条件分岐に展開できる
- 各分岐に条件が仮定として追加されるため、証明しやすい
- `simp` では簡約しきれない条件分岐の処理に有効

## Cons
- 最初の if/match のみ分割するため、複数ある場合は繰り返し必要
- すべての if 式を一括処理したい場合は `split_ifs` の方が効率的
- `Decidable` でない条件には適用できない

## コードサンプル

### サンプル 1: if-then-else の分割
```lean
example (n : Nat) : (if n = 0 then 1 else n) > 0 := by
  split
  · -- h✝ : n = 0 ⊢ 1 > 0
    omega
  · -- h✝ : ¬n = 0 ⊢ n > 0
    omega
```

### サンプル 2: match 式の分割
```lean
example (o : Option Nat) : (match o with | none => 0 | some n => n + 1) ≥ 0 := by
  split
  · -- ⊢ 0 ≥ 0
    omega
  · -- n✝ : Nat ⊢ n✝ + 1 ≥ 0
    omega
```

### サンプル 3: 仮定中の if を分割
```lean
example (p : Prop) [Decidable p] (a b c : Nat) (h : (if p then a else b) = c) (hp : p) : a = c := by
  split at h
  · -- h : a = c ⊢ a = c
    exact h
  · -- h✝ : ¬p ⊢ a = c
    contradiction
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `split_ifs` | if 式の一括展開 | 複数の if 式をまとめて処理したい場合 |
| `cases` | 帰納型の場合分け | 帰納型コンストラクタの分岐 |
| `by_cases` | 排中律での分岐 | 命題レベルで `p ∨ ¬p` の分岐 |

## 参照
- [Lean4 公式リファレンス — split](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#split)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
