# `solve_by_elim` — 仮定と補題の前方・後方推論による自動証明

**カテゴリ**: 自動化 | **定義元**: `Lean.Parser.Tactic.solveByElim` | **ソース**: Lean4 core

## 概要
`solve_by_elim` はローカル仮定と指定された補題を繰り返し `apply` / `exact` して、ゴールを閉じることを試みる。バックトラッキング付きの深さ優先探索で、仮定の組み合わせで到達可能な証明を自動的に構成する。追加の補題セットを渡すことで探索範囲を拡張できる。

## ゴールパターン

**適用前**
```lean
h₁ : P → Q
h₂ : Q → R
hp : P
⊢ R
```

**適用後**: ゴールが閉じる（`h₂ (h₁ hp)` を自動構成）

## 構文
```lean
solve_by_elim                     -- ローカル仮定のみで探索
solve_by_elim using [lem₁, lem₂]  -- 追加補題を使用して探索（Lean4 構文）
solve_by_elim (config := { maxDepth := 8 })  -- 探索深度を指定
```

## 必須 import
Lean4 core 組み込み。追加 import 不要。

## Pros
- 仮定のチェインで到達可能な証明を自動構成
- `using` で外部補題を追加でき、柔軟に探索範囲を拡張
- `apply` / `exact` の繰り返しで書くべき証明を自動化
- `aesop` より軽量で、仮定ベースの推論に特化

## Cons
- デフォルトの探索深度に制限がある（深い推論チェインでは `maxDepth` 調整が必要）
- ローカル仮定に依存するため、必要な補題が仮定にないと失敗
- `simp` や `rw` のような書き換えは行わない
- 探索空間が大きくなると遅い

## コードサンプル

### サンプル 1: 仮定のチェインで推論
```lean
-- h₁ : A → B, h₂ : B → C, ha : A
-- ⊢ C
example (h₁ : A → B) (h₂ : B → C) (ha : A) : C := by
  solve_by_elim
```

### サンプル 2: using で外部補題を追加
```lean
-- h₁ : P → Q, h₂ : Q → R, h : P
-- ⊢ R
example (h₁ : P → Q) (h₂ : Q → R) (h : P) : R := by
  solve_by_elim [h₁, h₂]
```

### サンプル 3: 型クラスインスタンスの解決
```lean
-- h : ∀ {α : Type} [inst : DecidableEq α], α → α → Bool
-- ⊢ Nat → Nat → Bool
example (h : ∀ {α : Type} [inst : DecidableEq α], α → α → Bool) :
    Nat → Nat → Bool := by
  solve_by_elim
```

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `assumption` | 単一仮定 | 仮定がそのまま一致する場合 |
| `exact` | 直接適用 | 証明項が分かっている場合 |
| `apply` | 単一適用 | 一段だけ適用する場合 |
| `aesop` | 汎用探索 | より広範なルールベース探索が必要な場合 |
| `tauto` | 命題論理 | 命題論理のトートロジー |

## 参照
- [Lean4 公式リファレンス — solve_by_elim](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
