# `linarith` — 線形算術（体を含む）の不等式証明

**カテゴリ**: 算術 | **定義元**: `Mathlib.Tactic.Linarith.linarith` | **ソース**: Mathlib

## 概要
`linarith` は線形順序体（`LinearOrderedField` / `LinearOrderedCommRing` など）上の線形不等式・等式を証明する。仮定の非負結合を取って矛盾を導く。`omega` とは異なり `Real` や `Rat` でも動作する。

## ゴールパターン

**適用前**
```lean
x y : Real
h₁ : x ≤ 3
h₂ : y ≤ 2
⊢ x + y ≤ 5
```

**適用後**
```lean
-- ゴールが閉じる
```

## 構文
```lean
linarith                     -- 仮定のみで証明
linarith [h₁, h₂ * h₃]     -- 追加の補題・式をヒントとして渡す
nlinarith                    -- 非線形拡張版
nlinarith [sq_nonneg x]     -- 非線形ヒント付き
```

## 必須 import
```lean
import Mathlib.Tactic.Linarith
```

## オプション一覧
| 構文 | 意味 |
|---|---|
| `[e₁, e₂]` | 追加ヒント（非負であるべき式） |
| `only [h₁, h₂]` | 指定した仮定のみ使用 |
| `(config := { maxDegree := n })` | 非線形ヒント生成の次数制限 |

## Pros（使うべき場面）
- `Real`, `Rat`, `Int` 等を含む線形不等式/等式を一発で閉じる
- `omega` が対応しない体（`Real` 等）で動作
- `nlinarith` は非線形な不等式も扱える

## Cons（注意・失敗ケース）
- 純粋な `Nat` / `Int` の問題なら `omega` の方が高速・確実
- 非線形な場合は `nlinarith` でもヒントが必要なことがある
- 項数が多いと遅くなることがある
- 除算を含むゴールには `field_simp` で前処理が必要

## コードサンプル

### サンプル 1: Real の不等式
```lean
example (x y : Real) (h₁ : x ≤ 3) (h₂ : y ≤ 2) : x + y ≤ 5 := by
  linarith
```

### サンプル 2: nlinarith で非線形
```lean
example (x : Real) (hx : 0 ≤ x) : 0 ≤ x ^ 2 := by
  nlinarith [sq_nonneg x]
```

### サンプル 3: ヒント付き
```lean
example (x y : Real) (h : x * y = 1) (hx : 0 < x) : 0 < y := by
  nlinarith [mul_pos_iff.mp (by linarith : 0 < x * y)]
```

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `linarith!` | より積極的に仮定を探索する強化版 |
| `linarith?` | 使用した仮定を提案する |
| `linarith?!` | `linarith!` + 提案 |

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `omega` | Nat/Int 専用 | Nat/Int の線形算術なら omega が確実で高速 |
| `nlinarith` | 非線形拡張 | 乗算・累乗を含む不等式 |
| `positivity` | 非負証明 | `0 ≤ e` / `0 < e` の形のゴール |
| `norm_num` | 数値計算 | 具体的な数値のみの計算 |
| `polyrith` | 整数係数 | `linarith` + Gröbner 基底。より強力だが遅い |

## 参照
- [Mathlib4 ドキュメント — Linarith](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Linarith/Frontend.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。