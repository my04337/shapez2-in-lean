# `nlinarith` — 非線形算術の不等式証明

**カテゴリ**: 算術 | **定義元**: `Mathlib.Tactic.Linarith.nlinarith` | **ソース**: Mathlib

---

## 概要

`nlinarith` は `linarith` の非線形拡張である。仮定同士の積（product of hypotheses）を自動生成してヒントとして追加し、非線形な不等式・等式を証明する。
内部的には仮定のペアワイズ積を候補に加えた上で `linarith` を呼び出すため、`a * b` や `x ^ 2` を含むゴールにも対応できる。ヒントを手動で与えることで成功率を高められる。

## ゴールパターン

**Before:**
```lean
x : ℝ
hx : 0 ≤ x
⊢ 0 ≤ x ^ 2
```

**After:**
```lean
-- ゴールが閉じる（no goals）
```

## 構文

```lean
nlinarith                        -- 仮定の積を自動追加して証明
nlinarith [sq_nonneg x]         -- 手動ヒント付き
nlinarith [h₁ * h₂, sq_abs a]  -- 複数ヒント
nlinarith (config := { maxDegree := 4 })  -- 次数制限を変更
```

## 必須 import

```lean
import Mathlib.Tactic.Linarith
```

## オプション一覧

| オプション | 説明 |
|---|---|
| `[e₁, e₂, ...]` | 非負であるべき式をヒントとして追加する |
| `only [h₁, h₂]` | 指定した仮定のみを使用する |
| `(config := { maxDegree := n })` | 仮定の積を生成するときの最大次数を設定する（デフォルト: 2） |

## Pros（使うべき場面）

- 非線形な不等式（乗算・累乗を含む）を証明できる
- `sq_nonneg`、`mul_self_nonneg` などのヒントと組み合わせて強力
- `linarith` では不可能な `x ^ 2 ≥ 0` 系の証明を自動化
- 仮定の積を自動探索するため、ヒントなしでも成功する場合がある

## Cons（注意・失敗ケース）

- 高次の非線形項（3 次以上）はヒントなしでは失敗しやすい → `maxDegree` の引き上げまたは手動ヒントが必要
- 仮定の積のペア数が多い場合、探索が遅くなることがある
- 除算を含むゴールには `field_simp` で前処理が必要
- 線形な不等式のみなら `linarith` の方が高速
- `Nat` / `Int` の線形算術には `omega` を優先すること

## コードサンプル

### 例 1: 平方の非負性

```lean
import Mathlib.Tactic.Linarith

-- ⊢ 0 ≤ x ^ 2
example (x : ℝ) : 0 ≤ x ^ 2 := by
  nlinarith [sq_nonneg x]
```

`sq_nonneg x` をヒントとして渡し、`x ^ 2 ≥ 0` を導出する。

### 例 2: 仮定の積を利用した証明

```lean
import Mathlib.Tactic.Linarith

-- h₁ : 0 ≤ a, h₂ : 0 ≤ b ⊢ 0 ≤ a * b
example (a b : ℝ) (h₁ : 0 ≤ a) (h₂ : 0 ≤ b) : 0 ≤ a * b := by
  nlinarith
```

`h₁ * h₂` の積が自動的に候補に加えられ、`0 ≤ a * b` が導出される。

### 例 3: 相加相乗平均の特殊ケース

```lean
import Mathlib.Tactic.Linarith

-- ha : 0 ≤ a, hb : 0 ≤ b ⊢ a * b ≤ (a + b) ^ 2 / 4
-- （(a - b) ^ 2 ≥ 0 を展開すると導ける）
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    4 * (a * b) ≤ (a + b) ^ 2 := by
  nlinarith [sq_nonneg (a - b)]
```

`(a - b) ^ 2 ≥ 0` をヒントとして渡し、AM-GM 不等式の変形を証明する。

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `linarith` | 基盤 | 線形不等式のみなら `linarith` が高速。`nlinarith` は非線形拡張 |
| `omega` | Nat/Int 専用 | `Nat` / `Int` の線形算術には `omega` を優先 |
| `positivity` | 補完 | `0 ≤ e` / `0 < e` の形のゴールに特化。構造的に非負性を証明 |
| `polyrith` | 上位 | Gröbner 基底を利用した多項式算術。`nlinarith` より強力だが外部 CAS が必要 |
| `norm_num` | 補完 | 数値リテラルの計算。具体値のみの場合に使用 |

## 参照

- [Mathlib4 docs — nlinarith](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Linarith/Frontend.html)
- [Mathematics in Lean — §2.4 More on Order and Divisibility](https://leanprover-community.github.io/mathematics_in_lean/)

---

> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
