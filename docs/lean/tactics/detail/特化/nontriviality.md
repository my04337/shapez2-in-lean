# `nontriviality` — 非自明性インスタンスの導入

**カテゴリ**: 特化 | **定義元**: `Mathlib.Tactic.Nontriviality.nontriviality` | **ソース**: Mathlib

## 概要
`nontriviality` は `Nontrivial α`（型 `α` に少なくとも2つの異なる要素が存在する）のインスタンスをコンテキストに追加するタクティク。多くの代数的定理は `Nontrivial` を暗黙の仮定として必要とするため、このタクティクでその前提を自動的に導出する。ゴール自体から非自明性を逆算して証明する場合もある。

## ゴールパターン

**適用前**
```lean
⊢ (1 : R) ≠ 0
```

**適用後**
```lean
inst✝ : Nontrivial R
⊢ (1 : R) ≠ 0
```
（`Nontrivial R` が仮定に追加され、後続のタクティクで利用可能になる）

## 構文
```lean
nontriviality          -- ゴールまたはコンテキストから Nontrivial を導出
nontriviality α        -- 型 α に対して Nontrivial を導出
```

## 必須 import
```lean
import Mathlib.Tactic.Nontriviality
```

## Pros
- `Nontrivial` 仮定の導出を自動化
- ゴールから必要な非自明性を逆算できる
- 代数的証明でボイラープレートを削減
- 既存のインスタンスと仮定から推論可能

## Cons
- 非自明性の導出元がない場合は失敗する
- 自明な型（例: `Unit`, `Fin 1`）には当然適用不可
- 後続タクティクと組み合わせる必要がある（単体ではゴールを閉じない）
- Mathlib 依存

## コードサンプル

### サンプル 1: 1 ≠ 0 の証明
```lean
import Mathlib.Tactic.Nontriviality
import Mathlib.Algebra.Order.Field.Basic

example : (1 : ℝ) ≠ 0 := by
  nontriviality
  -- inst✝ : Nontrivial ℝ がコンテキストに追加
  exact one_ne_zero
```

### サンプル 2: ゴールからの逆算
```lean
import Mathlib.Tactic.Nontriviality
import Mathlib.Algebra.GroupWithZero.Basic

example {R : Type*} [MonoidWithZero R] [NoZeroDivisors R]
    (a : R) (ha : a ≠ 0) : (1 : R) ≠ 0 := by
  nontriviality
  -- Nontrivial R が a ≠ 0 等の仮定から導出される
  exact one_ne_zero
```

### サンプル 3: 環の性質との組み合わせ
```lean
import Mathlib.Tactic.Nontriviality
import Mathlib.RingTheory.Polynomial.Basic

open Polynomial

example {R : Type*} [CommRing R] [Nontrivial R] :
    degree (X : R[X]) = 1 := by
  nontriviality R
  -- Nontrivial R が明示的に確認される
  exact degree_X
```

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `positivity` | 正値性 | `0 < expr` の自動証明に |
| `norm_num` | 数値評価 | 具体的な数値の非等式に |
| `assumption` | 仮定利用 | 既にインスタンスがある場合 |

## 参照
- [Mathlib4 ドキュメント — nontriviality](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Nontriviality/Basic.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
