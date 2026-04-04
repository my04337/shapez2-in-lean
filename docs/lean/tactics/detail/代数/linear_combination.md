# `linear_combination` — 仮定の線形結合で等式を証明

**カテゴリ**: 代数 | **定義元**: `Mathlib.Tactic.LinearCombination.linearCombination` | **ソース**: Mathlib

## 概要
`linear_combination` は仮定の等式の線形結合を指定して、ゴールの等式を証明する。ユーザーが `2 * h₁ + h₂` のように結合係数を指定し、残りのギャップを `ring` で閉じる。

## ゴールパターン

**適用前**
```lean
h₁ : x + y = 3
h₂ : x - y = 1
⊢ 2 * x = 4
```

**適用後** (`linear_combination h₁ + h₂`)
```lean
-- ゴールが閉じる
```

## 構文
```lean
linear_combination h₁ + h₂             -- 仮定の和
linear_combination 2 * h₁ - h₂         -- 係数付き結合
linear_combination (norm := ring_nf) e  -- 残りの処理を指定
```

## 必須 import
```lean
import Mathlib.Tactic.LinearCombination
```

## Pros
- 仮定の等式を明示的に組み合わせて等式を証明
- `ring` では仮定を使えないが、`linear_combination` は仮定を直接参照する
- 証明の意図が明確で可読性が高い

## Cons
- 正しい線形結合をユーザーが見つける必要がある
- 等式のみ（不等式には使えない → `linarith`）
- 結合係数を間違えると失敗

## コードサンプル

### サンプル 1: 基本
```lean
example (x y : ℚ) (h₁ : x + y = 5) (h₂ : x - y = 1) : x = 3 := by
  linear_combination (h₁ + h₂) / 2
```

### サンプル 2: 係数付き
```lean
example (h : a = b) : 2 * a = 2 * b := by
  linear_combination 2 * h
```

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `linear_combination'` | `ring` の代わりに手動で残余ゴールを処理する |
| `linear_combination2` | 2つの等式を同時に結合する |

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `ring` | 環の等式 | 仮定不要の等式 |
| `linarith` | 不等式 | 不等式の証明 |
| `polyrith` | 自動版 | linear_combination の係数を自動で見つける |
| `field_simp` | 分母消去 | 除算を含む場合の前処理 |

## 参照
- [Mathlib4 ドキュメント — LinearCombination](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/LinearCombination.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
