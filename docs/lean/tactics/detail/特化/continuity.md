# `continuity` — 連続性の自動証明

**カテゴリ**: 特化 | **定義元**: `tacticContinuity` | **ソース**: Mathlib

## 概要
`continuity` は `Continuous f` 形式のゴールを、`@[continuity]` 属性が付与された補題群を組み合わせて自動的に証明するタクティク。関数の合成・積・射影など、構造的に連続性が導かれるケースを再帰的に分解して証明を構築する。位相空間の基本的な証明で頻繁に使われる。

## ゴールパターン

**適用前**
```lean
⊢ Continuous (fun x => f x + g x)
```

**適用後**: ゴールが閉じる（`@[continuity]` 補題で解決可能な場合）

## 構文
```lean
continuity             -- @[continuity] 補題で自動証明
```

## 必須 import
```lean
import Mathlib.Topology.Basic
```

## Pros
- 連続写像の合成・積などのルーチン証明を自動化
- `@[continuity]` 属性で拡張可能
- `fun_prop` よりも位相空間に特化した補題セットを持つ

## Cons
- `Continuous` 以外の性質（`Differentiable` 等）には直接使えない
- 補題データが不足する場合は `fun_prop` の方が解決力が高い
- ゴール形式が `Continuous f` でないと適用不可
- Mathlib の位相空間ライブラリが必要

## コードサンプル

### サンプル 1: 加法の連続性
```lean
import Mathlib.Topology.Algebra.Group.Basic

example : Continuous (fun p : ℝ × ℝ => p.1 + p.2) := by
  continuity
  -- ゴールが閉じる（実数の加法は連続）
```

### サンプル 2: 合成関数の連続性
```lean
import Mathlib.Topology.Basic

example {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] (f : α → β) (g : β → γ)
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (g ∘ f) := by
  continuity
  -- ゴールが閉じる（Continuous.comp から）
```

### サンプル 3: 定数関数の連続性
```lean
import Mathlib.Topology.Basic

example {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (b : β) : Continuous (fun _ : α => b) := by
  continuity
  -- ゴールが閉じる（continuous_const から）
```

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `continuity?` | 成功時に使用した補題列を提案する |

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `fun_prop` | 汎用プロパティ | `Continuous` / `Differentiable` 等を統一的に扱う |
| `apply?` | 補題検索 | 手動で適用する補題を探すとき |
| `exact?` | 完全一致検索 | 直接閉じる補題を探すとき |

## 参照
- [Mathlib4 ドキュメント — continuity](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Continuity.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
