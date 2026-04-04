# `compute_degree` — 多項式の次数の自動計算

**カテゴリ**: 特化 | **定義元**: `Mathlib.Tactic.ComputeDegree.computeDegree` | **ソース**: Mathlib

## 概要
`compute_degree` は多項式 (`Polynomial R`) の次数に関するゴールを自動的に証明するタクティク。`natDegree`, `degree`, `leadingCoeff` 等の計算を、多項式の構造（加法・乗法・定数・`X` のべき等）を分解して実行する。多項式環の具体的な次数計算を自動化し、ルーチン的な次数評価の証明負担を軽減する。

## ゴールパターン

**適用前**
```lean
⊢ natDegree (X ^ 3 + C a * X + C b) ≤ 3
```

**適用後**: ゴールが閉じる（構造的に次数を計算）

## 構文
```lean
compute_degree          -- 多項式の次数を自動計算
compute_degree!         -- 正規化を強めに行うバリアント
```

## 必須 import
```lean
import Mathlib.Tactic.ComputeDegree
```

## Pros
- 多項式の次数計算を完全自動化
- `natDegree`, `degree`, `leadingCoeff` を幅広くカバー
- 加法・乗法・べき乗・定数多項式の次数を正確に計算
- `compute_degree!` で正規化が不十分なケースにも対応

## Cons
- `Polynomial R` 以外のデータ型には使えない
- 次数が不確定な場合（例: 係数がゼロかもしれない場合）はサブゴールが残る
- Mathlib の多項式ライブラリ依存
- 非常に複雑な多項式では遅くなる場合がある

## コードサンプル

### サンプル 1: 基本的な次数計算
```lean
import Mathlib.Tactic.ComputeDegree
import Mathlib.RingTheory.Polynomial.Basic

open Polynomial

example : natDegree (X ^ 2 + C 3 * X + C 1 : ℤ[X]) = 2 := by
  compute_degree!
  -- ゴールが閉じる（X^2 の次数が支配的）
```

### サンプル 2: 次数の上界
```lean
import Mathlib.Tactic.ComputeDegree
import Mathlib.RingTheory.Polynomial.Basic

open Polynomial

example {R : Type*} [CommRing R] (a b : R) :
    natDegree (C a + C b * X : R[X]) ≤ 1 := by
  compute_degree
  -- ゴールが閉じる（C a + C b * X は次数 ≤ 1）
```

### サンプル 3: 主係数の計算
```lean
import Mathlib.Tactic.ComputeDegree
import Mathlib.RingTheory.Polynomial.Basic

open Polynomial

example : natDegree (X ^ 3 + C 2 : ℤ[X]) = 3 := by
  compute_degree!
  -- ゴールが閉じる（X^3 の次数は 3）
```

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `compute_degree!` | より積極的に次数計算を行う強化版 |

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `ring` | 環の等式 | 多項式の等式証明に |
| `norm_num` | 数値正規化 | 係数の数値計算に |
| `simp` | 簡約 | 一般的な多項式の簡約に |
| `decide` | 決定手続き | 有限体上の具体計算に |

## 参照
- [Mathlib4 ドキュメント — compute_degree](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/ComputeDegree.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
