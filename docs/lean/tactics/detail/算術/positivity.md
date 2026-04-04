# `positivity` — 非負性・正値性の自動証明

**カテゴリ**: 算術 | **定義元**: `Mathlib.Tactic.Positivity.positivity` | **ソース**: Mathlib

## 概要
`positivity` は `0 ≤ e` や `0 < e` の形のゴールを自動証明する。加算・乗算・累乗・絶対値・ノルムなどの非負性規則を再帰的に適用し、式の構造から非負性/正値性を導く。

## ゴールパターン

**適用前**
```lean
⊢ 0 ≤ x ^ 2 + 1
```

**適用後**: ゴールが閉じる

## 構文
```lean
positivity              -- 基本形
positivity at h         -- 仮定に適用（稀）
```

## 必須 import
```lean
import Mathlib.Tactic.Positivity
```

## Pros
- `0 ≤ e` / `0 < e` に特化した確実なタクティク
- `sq_nonneg`, `abs_nonneg`, `norm_nonneg` 等を自動適用
- `nlinarith` よりも表現力が高い場面がある（構造的な非負性）

## Cons
- `0 ≤` / `0 <` の形でないゴールには使えない → `linarith` で一般不等式
- 拡張するにはカスタム `@[positivity]` プラグインが必要
- Mathlib import が必要

## コードサンプル

### サンプル 1: 二乗の非負性
```lean
example (x : Real) : 0 ≤ x ^ 2 := by positivity
```

### サンプル 2: 乗算の正値性
```lean
example (x y : Real) (hx : 0 < x) (hy : 0 < y) : 0 < x * y := by positivity
```

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `nlinarith` | 非線形不等式 | 0≤以外の形の不等式 |
| `linarith` | 線形不等式 | 一般的な線形不等式 |
| `norm_num` | 数値計算 | 具体的な数値の不等式 |

## 参照
- [Mathlib4 ドキュメント — Positivity](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Positivity/Basic.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
