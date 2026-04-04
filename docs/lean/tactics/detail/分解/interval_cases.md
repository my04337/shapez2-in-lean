# `interval_cases` — 整数・自然数の範囲列挙

**カテゴリ**: 分解 | **定義元**: `Mathlib.Tactic.IntervalCases.intervalCases` | **ソース**: Mathlib

## 概要
`interval_cases` はコンテキスト中の上界・下界の仮定（`a ≤ n`, `n < b` など）から変数の取りうる値を自動的に列挙し、各具体値に対するサブゴールを生成する。`fin_cases` が `Fin n` 型に特化しているのに対し、`interval_cases` は `Nat` や `Int` の変数に対して仮定から範囲を推定する。

## ゴールパターン

**適用前**（`interval_cases n`）
```lean
n : Nat
h₁ : 2 ≤ n
h₂ : n < 5
⊢ P n
```

**適用後**
```lean
-- ケース 1: ⊢ P 2
-- ケース 2: ⊢ P 3
-- ケース 3: ⊢ P 4
```

## 構文
```lean
interval_cases n                -- 変数 n の範囲を仮定から推定して列挙
interval_cases                  -- 適用可能な変数を自動検出
```

## 必須 import
```lean
import Mathlib.Tactic.IntervalCases
```

## オプション一覧
| 構文 | 意味 |
|---|---|
| `interval_cases n` | 変数 n の上下界を仮定から推定して列挙 |
| `interval_cases` | 適用可能な変数を自動で選択 |

## Pros
- 上下界の仮定から自動的に範囲を検出し列挙する
- `omega` と組み合わせて算術的な性質を簡潔に証明できる
- `Nat` と `Int` の両方に対応

## Cons
- 上界・下界の仮定がコンテキストに明示されていないと適用不可
- 範囲が広すぎると大量のサブゴールが生成される
- Mathlib 依存のため、core のみのプロジェクトでは使えない

## コードサンプル

### サンプル 1: 自然数の範囲列挙
```lean
example (n : Nat) (h₁ : 1 ≤ n) (h₂ : n ≤ 3) : n * n ≤ 9 := by
  interval_cases n
  -- ⊢ 1 * 1 ≤ 9
  -- ⊢ 2 * 2 ≤ 9
  -- ⊢ 3 * 3 ≤ 9
  all_goals omega
```

### サンプル 2: 範囲を利用した分岐証明
```lean
example (n : Nat) (h₁ : 0 < n) (h₂ : n < 4) : n = 1 ∨ n = 2 ∨ n = 3 := by
  interval_cases n
  -- ⊢ 1 = 1 ∨ 1 = 2 ∨ 1 = 3
  · left; rfl
  -- ⊢ 2 = 1 ∨ 2 = 2 ∨ 2 = 3
  · right; left; rfl
  -- ⊢ 3 = 1 ∨ 3 = 2 ∨ 3 = 3
  · right; right; rfl
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `fin_cases` | 有限型の全列挙 | `Fin n` 型の変数を列挙する場合 |
| `omega` | 線形算術 | 列挙後の各ケースの算術証明 |
| `mod_cases` | 剰余での場合分け | `n % m` の値で分岐する場合 |

## 参照
- [Mathlib4 — IntervalCases](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/IntervalCases.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
