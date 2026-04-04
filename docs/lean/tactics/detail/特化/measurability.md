# `measurability` — 可測性の自動証明

**カテゴリ**: 特化 | **定義元**: `Mathlib.Tactic.measurability` | **ソース**: Mathlib

## 概要
`measurability` は `Measurable f` や `MeasurableSet s` 形式のゴールを、`@[measurability]` 属性が付与された補題群を用いて自動的に証明するタクティク。可測関数の合成・積・定数などの構造的なケースを再帰的に分解して証明を構築する。測度論の基本的な証明で頻繁に使われる。

## ゴールパターン

**適用前**
```lean
⊢ Measurable (fun x => f x + g x)
```

**適用後**: ゴールが閉じる（`@[measurability]` 補題で解決可能な場合）

## 構文
```lean
measurability          -- @[measurability] 補題で自動証明
measurability?         -- 使った証明手順を表示
```

## 必須 import
```lean
import Mathlib.MeasureTheory.MeasurableSpace.Basic
```

## Pros
- 可測性の構造的証明を全自動化
- `Measurable`, `MeasurableSet`, `AEMeasurable` を幅広くカバー
- `@[measurability]` 属性でユーザー定義補題も登録可能
- `measurability?` でどの補題が使われたか確認できる

## Cons
- 測度論以外のゴールには適用不可
- 非自明な可測性（例: ルベーグ可測集合の複雑な構成）は解けない場合がある
- Mathlib の測度論ライブラリが必要
- 大規模なゴールでは探索が遅くなることがある

## コードサンプル

### サンプル 1: 加法の可測性
```lean
import Mathlib.MeasureTheory.Function.Basic

example {α : Type*} [MeasurableSpace α]
    (f g : α → ℝ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => f x + g x) := by
  measurability
  -- ゴールが閉じる（Measurable.add と hf, hg から）
```

### サンプル 2: 可測集合の補集合
```lean
import Mathlib.MeasureTheory.MeasurableSpace.Basic

example {α : Type*} [MeasurableSpace α] (s : Set α)
    (hs : MeasurableSet s) : MeasurableSet sᶜ := by
  measurability
  -- ゴールが閉じる（MeasurableSet.compl から）
```

### サンプル 3: 合成関数の可測性
```lean
import Mathlib.MeasureTheory.Function.Basic

example {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (f : α → β) (g : β → γ)
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (g ∘ f) := by
  measurability
  -- ゴールが閉じる（Measurable.comp から）
```

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `measurability?` | 使用した補題を提案する |
| `measurability!` | より積極的に探索する強化版 |
| `measurability!?` | `measurability!` + 提案 |

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `continuity` | 連続性 | `Continuous` ゴールに特化 |
| `fun_prop` | 汎用プロパティ | 関数性質を統一的に扱う |
| `exact?` | 補題検索 | 手動で適用補題を探すとき |

## 参照
- [Mathlib4 ドキュメント — measurability](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Measurability.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
