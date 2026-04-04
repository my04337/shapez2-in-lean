# `induction` — 構造的帰納法

**カテゴリ**: 分解 | **定義元**: `Lean.Parser.Tactic.induction` | **ソース**: Lean4 core

## 概要
`induction` は帰納型の値に対して構造的帰納法を適用し、各コンストラクタに対応するサブゴールと帰納法の仮説（induction hypothesis）を自動生成する。`cases` との違いは、再帰的コンストラクタで帰納法の仮説 `ih` が得られる点。`with` 節で各ケースに名前を付け、個別にタクティクを適用する。

## ゴールパターン

**適用前**（`induction n with ...`）
```lean
n : Nat
⊢ P n
```

**適用後**
```lean
-- ケース zero:
⊢ P 0

-- ケース succ:
n✝ : Nat
ih : P n✝
⊢ P (n✝ + 1)
```

## 構文
```lean
induction n                          -- n に帰納法を適用
induction n with                     -- with 節で各ケースに名前
  | zero => tac₁
  | succ n ih => tac₂
induction n generalizing x           -- x を一般化してから帰納法
induction n using Nat.recAux         -- カスタム再帰子を指定
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `with \| con args => tac` | 各コンストラクタの名前・帰納法仮説・タクティクを指定 |
| `generalizing x` | 帰納法の前に `x` を全称化し仮説を強める |
| `using rec` | デフォルトでなくカスタム再帰子を使用 |

## Pros
- 帰納法の仮説が自動で生成されるため、再帰的性質の証明に不可欠
- `with` 節で各ケースを明確に分離でき、可読性が高い
- `generalizing` で仮説の強化が容易

## Cons
- `generalizing` を忘れると帰納法の仮説が弱くなり証明できない場合がある
- 複数の値に同時に帰納法を適用するのは困難（mutual induction が必要）
- `cases` で十分な場面では冗長

## コードサンプル

### サンプル 1: リストの長さに関する帰納法
```lean
theorem length_append (xs ys : List α) : (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    -- ih : (xs ++ ys).length = xs.length + ys.length
    -- ⊢ (x :: xs ++ ys).length = (x :: xs).length + ys.length
    simp [ih]; omega
```

### サンプル 2: generalizing を使った帰納法
```lean
theorem List.reverse_reverse (xs : List α) : xs.reverse.reverse = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    -- ih : xs.reverse.reverse = xs
    simp [List.reverse_cons, ih]
```

### サンプル 3: Nat の帰納法
```lean
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
    -- ⊢ 0 + 0 = 0
    rfl
  | succ n ih =>
    -- ih : 0 + n = n
    -- ⊢ 0 + (n + 1) = n + 1
    omega
```

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `induction'` | Lean 3 互換の induction（Mathlib） |

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `cases` | 場合分けのみ | 帰納法の仮説が不要な場合 |
| `rcases` | 再帰的分解 | 仮定の構造分解 |
| `fun_induction` | 関数帰納法 | 関数定義に基づく帰納法が必要な場合 |

## 参照
- [Lean4 公式リファレンス — induction](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#tactic-ref-inductive)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
