# `fin_cases` — 有限型の全要素列挙

**カテゴリ**: 分解 | **定義元**: `Mathlib.Tactic.FinCases.finCasesStx` | **ソース**: Mathlib

## 概要
`fin_cases` は有限型（`Fin n`, `Bool`, 有限な帰納型など）の変数について、すべての具体値を列挙してサブゴールに分割する。`cases` と異なり、`Fin n` のような型で `n` が具体的な数値のとき、各値 `0, 1, ..., n-1` を自動的に列挙する。`Fintype` インスタンスを持つ任意の型に適用可能。

## ゴールパターン

**適用前**（`fin_cases h`）
```lean
h : Fin 3
⊢ P h
```

**適用後**
```lean
-- ケース 1: ⊢ P ⟨0, _⟩
-- ケース 2: ⊢ P ⟨1, _⟩
-- ケース 3: ⊢ P ⟨2, _⟩
```

## 構文
```lean
fin_cases h                     -- 仮定 h の型を全要素で列挙
fin_cases h with a, b, c        -- 各ケースに名前を付ける
```

## 必須 import
```lean
import Mathlib.Tactic.FinCases
```

## オプション一覧
| 構文 | 意味 |
|---|---|
| `fin_cases h` | 仮定 h に束縛された有限型の全要素で場合分け |
| `with a, b, ...` | 各ケースに名前を付ける |

## Pros
- `Fin n` の全ケース列挙を自動化し、手動での場合分けが不要
- `decide` と組み合わせて有限型上の性質を完全に検証可能
- `Bool`, `Fin n`, カスタム有限型など広い範囲に適用可能

## Cons
- `n` が大きいと大量のサブゴールが生成され、証明が冗長になる
- `n` が変数（具体的な値でない）場合は適用不可
- Mathlib 依存のため、Lean4 core のみのプロジェクトでは使えない

## コードサンプル

### サンプル 1: Fin 3 の全列挙
```lean
example (i : Fin 3) : i.val < 5 := by
  fin_cases i
  -- 3つのサブゴール:
  -- ⊢ 0 < 5
  -- ⊢ 1 < 5
  -- ⊢ 2 < 5
  all_goals omega
```

### サンプル 2: Bool の全列挙
```lean
example (b : Bool) : (b && true) = b := by
  fin_cases b
  -- ケース false: ⊢ (false && true) = false
  · rfl
  -- ケース true: ⊢ (true && true) = true
  · rfl
```

### サンプル 3: 有界な自然数
```lean
example (n : Nat) (h : n < 3) : n * n < 10 := by
  interval_cases n
  -- ⊢ 0 * 0 < 10 / ⊢ 1 * 1 < 10 / ⊢ 2 * 2 < 10
  all_goals omega
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `interval_cases` | 整数範囲の列挙 | 上下界から範囲を列挙する場合 |
| `cases` | 帰納型の場合分け | コンストラクタ単位の分岐 |
| `decide` | 決定可能な命題 | 列挙後の各ケースを自動証明 |

## 参照
- [Mathlib4 — FinCases](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/FinCases.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
