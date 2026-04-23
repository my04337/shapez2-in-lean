# `by_cases` — 古典論理による場合分け

**カテゴリ**: 分解 | **定義元**: `Classical.«tacticBy_cases_:_»` | **ソース**: Lean4 core (Classical)

## 概要
`by_cases` は命題 `p` に対して `p ∨ ¬p`（排中律）を適用し、`p` が成り立つ場合と成り立たない場合の2つのサブゴールに分割する。古典論理に基づくため、`Decidable` インスタンスが不要で任意の命題に使える。

## ゴールパターン

**適用前**（`by_cases h : p`）
```lean
⊢ Q
```

**適用後**
```lean
-- ケース 1（正）:
h : p
⊢ Q

-- ケース 2（負）:
h : ¬p
⊢ Q
```

## 構文
```lean
by_cases h : p            -- p か ¬p で場合分け、仮定名 h
by_cases p                -- 仮定名を省略（自動命名）
```

## 必須 import
Lean4 core 組み込み（`Classical` は自動で利用可能）。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `h : p` | 仮定 `h` に `p` または `¬p` を束縛 |
| `p` | 仮定名を省略 |

## Pros
- 任意の命題に適用でき、`Decidable` インスタンスが不要
- 排中律を明示的に使うため、証明の意図が明確
- 2つのケースに単純に分割するため構造が分かりやすい

## Cons
- 古典論理に依存するため、構成的証明が求められる場面では不適切
- 分割がつねに2ケースなので、多分岐にはネストが深くなる
- `Decidable` な命題であれば `split` や `split_ifs` の方が効率的

## コードサンプル

### サンプル 1: 自然数が 0 か否かの場合分け
```lean
example (n : Nat) : n = 0 ∨ n ≥ 1 := by
  by_cases h : n = 0
  · -- h : n = 0 ⊢ n = 0 ∨ n ≥ 1
    left; exact h
  · -- h : ¬n = 0 ⊢ n = 0 ∨ n ≥ 1
    right; omega
```

### サンプル 2: リストの空判定
```lean
example (xs : List α) : xs = [] ∨ xs.length ≥ 1 := by
  by_cases h : xs = []
  · -- h : xs = [] ⊢ xs = [] ∨ xs.length ≥ 1
    left; exact h
  · -- h : ¬xs = [] ⊢ xs = [] ∨ xs.length ≥ 1
    right
    cases xs with
    | nil => contradiction
    | cons _ _ => simp
```

### サンプル 3: 偶奇の場合分け
```lean
example (n : Nat) : n % 2 = 0 ∨ n % 2 = 1 := by
  by_cases h : n % 2 = 0
  · left; exact h
  · right; omega
```

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `by_cases!` | 型クラスインスタンスをより積極的に探索する |

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `cases` | 帰納型の場合分け | 帰納型のコンストラクタで分岐する場合 |
| `split` | if/match 分割 | ゴール中の if/match を分割する場合 |
| `by_contra` | 背理法 | ¬Q を仮定して矛盾を導く場合 |

## 参照
- [Lean4 公式リファレンス — by_cases](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#by_cases)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
