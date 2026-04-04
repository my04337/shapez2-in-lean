# `polyrith` — 外部 CAS を使った多項式算術の自動証明

**カテゴリ**: 代数 | **定義元**: `Mathlib.Tactic.Polyrith.polyrith` | **ソース**: Mathlib

---

## 概要

`polyrith` は外部の計算代数システム（SageMath）を呼び出し、多項式算術の等式・不等式を証明する。具体的には Gröbner 基底計算により、ゴールが仮定の多項式結合であることを確認し、`linear_combination` の呼び出しに変換する。
非線形な等式・不等式に対して `ring` や `linarith` より強力だが、外部サーバへのアクセスが必要。

## ゴールパターン

**Before:**
```lean
x y : ℚ
h₁ : x + y = 3
h₂ : x - y = 1
⊢ x = 2
```

**After:**
```lean
-- ゴールが閉じる（no goals）
```

## 構文

```lean
polyrith                       -- 仮定から自動的に証明を探索
polyrith only [h₁, h₂]        -- 指定した仮定のみ使用
polyrith (config := { maxDegree := 4 })  -- 探索次数の上限を指定
```

## 必須 import

```lean
import Mathlib.Tactic.Polyrith
```

## オプション一覧

| オプション | 説明 |
|---|---|
| `only [h₁, h₂, ...]` | 使用する仮定を制限する |
| `(config := { maxDegree := n })` | 多項式係数の探索次数の上限を設定する |

## Pros（使うべき場面）

- `ring` や `linarith` では閉じない非線形等式を証明できる
- 仮定の多項式結合を自動探索するため、手動で係数を見つける必要がない
- 成功時に `linear_combination ...` の形で再現可能な証明を出力する
- 非線形不等式の証明にも応用可能

## Cons（注意・失敗ケース）

- 外部サーバ（SageMath）へのネットワークアクセスが必要（オフライン環境では使用不可）
- サーバの応答時間に依存するため、実行が遅い場合がある
- 成功したら `polyrith` の出力する `linear_combination` 呼び出しに置き換えるのが推奨（再現性・速度向上）
- 整数係数体（`ℚ`, `ℝ` 等）でないフィールドでは動作しない場合がある
- `Nat` の減算（フロア減算）を含む式には注意が必要

## コードサンプル

### 例 1: 連立方程式

```lean
import Mathlib.Tactic.Polyrith

-- h₁ : x + y = 3, h₂ : x - y = 1 ⊢ x = 2
example (x y : ℚ) (h₁ : x + y = 3) (h₂ : x - y = 1) : x = 2 := by
  polyrith
  -- polyrith が成功すると以下のような出力を返す:
  -- Try this: linear_combination (1 / 2) * h₁ + (1 / 2) * h₂
```

連立方程式の仮定から解を導出する。

### 例 2: 非線形等式

```lean
import Mathlib.Tactic.Polyrith

-- h : x ^ 2 = 4, hx : x = 2 ⊢ x ^ 3 = 8
example (x : ℚ) (hx : x = 2) : x ^ 3 = 8 := by
  polyrith
```

非線形な冪乗を含む等式を自動証明する。

### 例 3: only で仮定を制限

```lean
import Mathlib.Tactic.Polyrith

-- h₁ : a + b = 5, h₂ : a * b = 6 ⊢ a ^ 2 + b ^ 2 = 13
example (a b : ℚ) (h₁ : a + b = 5) (h₂ : a * b = 6) :
    a ^ 2 + b ^ 2 = 13 := by
  polyrith only [h₁, h₂, sq_nonneg (a - b)]
```

使用する仮定と補助項を明示して探索範囲を限定する。

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `linear_combination` | 出力先 | `polyrith` の出力結果。成功したら `linear_combination` に置き換える |
| `ring` | 基盤 | 恒等式（仮定不要）なら `ring` が高速。`polyrith` は仮定を使う証明向け |
| `nlinarith` | 代替 | ヒント付きの非線形算術。オフラインで動作し `polyrith` より軽量 |
| `linarith` | 基盤 | 線形不等式。`polyrith` は非線形を含むより広い範囲 |
| `field_simp` | 前処理 | 分数式の分母消去。`field_simp` → `polyrith` のコンボ |
| `norm_num` | 補完 | 具体的な数値計算。リテラルのみの場合に使用 |

## 参照

- [Mathlib4 docs — polyrith](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Polyrith.html)
- [Mathematics in Lean — §2.2 Proving Identities](https://leanprover-community.github.io/mathematics_in_lean/)

---

> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
