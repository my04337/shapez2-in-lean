# `fun_prop` — 関数プロパティの汎用自動証明

**カテゴリ**: 特化 | **定義元**: `Mathlib.Meta.FunProp.funPropTacStx` | **ソース**: Mathlib

## 概要
`fun_prop` は `P f` 形式のゴール（`Continuous f`, `Differentiable ℝ f`, `Measurable f` 等）を、関数の構造を再帰的に分解して自動証明するタクティク。ラムダ式・合成・射影・定数などの構成要素を認識し、`@[fun_prop]` 属性が付いた補題群を適用して証明を組み立てる。`continuity` や `measurability` の上位互換として、複数の関数性質を統一的に扱える。

## ゴールパターン

**適用前**
```lean
⊢ Continuous (fun x => f (g x) + h x)
```

**適用後**: ゴールが閉じる（構造分解と `@[fun_prop]` 補題で解決可能な場合）

## 構文
```lean
fun_prop               -- 関数プロパティを自動証明
fun_prop (disch := tac) -- 補助ゴールを tac で片付ける
```

## 必須 import
```lean
import Mathlib.Tactic.FunProp
```

## オプション一覧
| 構文 | 意味 |
|---|---|
| `fun_prop` | デフォルトの自動証明 |
| `fun_prop (disch := simp)` | サイドゴールを `simp` で処理 |
| `fun_prop (disch := assumption)` | サイドゴールを仮定から処理 |

## Pros
- `Continuous`, `Differentiable`, `Measurable`, `ContDiff` 等を統一的に扱える
- 関数合成・積・和などの構造分解が自動
- `@[fun_prop]` で独自の性質・補題を登録できる
- `continuity` や `measurability` で解けないケースも解ける場合がある

## Cons
- 探索空間が広いため、複雑な関数では遅くなりうる
- 登録補題が不足すると途中で止まる
- エラーメッセージが分かりにくい場合がある
- 非関数プロパティ（集合や値の性質）には使えない

## コードサンプル

### サンプル 1: 合成関数の連続性
```lean
import Mathlib.Topology.Basic
import Mathlib.Tactic.FunProp

example {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] (f : β → γ) (g : α → β)
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f (g x)) := by
  fun_prop
  -- ゴールが閉じる（合成の連続性として分解）
```

### サンプル 2: 微分可能性の証明
```lean
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.FunProp

example (f g : ℝ → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Differentiable ℝ (fun x => f x + g x) := by
  fun_prop
  -- ゴールが閉じる（Differentiable.add から）
```

### サンプル 3: disch オプションとの組み合わせ
```lean
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Tactic.FunProp

example (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (fun x => f x * f x) := by
  fun_prop
  -- ゴールが閉じる（Continuous.mul と hf から）
```

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `continuity` | 連続性特化 | `Continuous` のみなら十分 |
| `measurability` | 可測性特化 | `Measurable` のみなら十分 |
| `gcongr` | 不等式分解 | 不等式の構造分解に |

## 参照
- [Mathlib4 ドキュメント — fun_prop](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/FunProp/Decl.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
