# `ring_nf` — 環式の正規化

**カテゴリ**: 代数 | **定義元**: `Mathlib.Tactic.Ring.ringNF` | **ソース**: Mathlib

---

## 概要

`ring_nf` は可換半環 (`CommSemiring`) 以上の構造で、環式を正規形に書き換える。`ring` と同じ正規化エンジンを使用するが、ゴールを閉じることを要求しない点が異なる。
等式の両辺が正規化後に一致すればゴールは閉じるが、主な用途は式の整理・簡約であり、後続のタクティクへの前処理として使われることが多い。

## ゴールパターン

**Before:**
```lean
a b : Int
⊢ (a + b) * (a - b) = a ^ 2 - b ^ 2
```

**After:**
```lean
-- 両辺が同一の正規形になり、ゴールが閉じる（no goals）
```

**Before (整理のみ):**
```lean
x y : Int
h : x * y + y * x = 10
⊢ 2 * x * y = 10
```

**After (`ring_nf at h ⊢`):**
```lean
-- 仮定 h とゴールの両方が正規化され、h : 2 * x * y = 10 ⊢ 2 * x * y = 10 の形になる
```

## 構文

```lean
ring_nf                -- ゴールを正規化
ring_nf at h           -- 仮定 h を正規化
ring_nf at h₁ h₂      -- 複数の仮定を正規化
ring_nf at *           -- ゴールと全仮定を正規化
ring_nf at h ⊢        -- 仮定 h とゴールを正規化
```

## 必須 import

```lean
import Mathlib.Tactic.Ring
```

## Pros（使うべき場面）

- 環式を標準的な正規形に統一できる（項の順序・係数の整理）
- 仮定に対しても適用できる（`at h` / `at *`）
- `ring` で差分がわずかに残る場合の前処理として有効
- ゴールを閉じる必要がないため、中間ステップとして柔軟に使える

## Cons（注意・失敗ケース）

- ゴールを閉じることが保証されない（等式が環の恒等式でない場合は残る）
- 非可換環には対応しない
- 正規形の選択が直感的でない場合がある（`2 * a * b` vs `a * b + a * b` など）
- 仮定の書き換えが他の仮定との整合性を崩す場合がある（注意して使うこと）

## コードサンプル

### 例 1: ゴールの正規化で証明完了

```lean
import Mathlib.Tactic.Ring

-- ⊢ (a + b) * (a - b) = a ^ 2 - b ^ 2
example (a b : Int) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring_nf
```

両辺が同一の正規形に変換されるため、そのままゴールが閉じる。

### 例 2: 仮定の正規化

```lean
import Mathlib.Tactic.Ring

-- h : x * y + y * x + z = 10 ⊢ 2 * x * y + z = 10
example (x y z : Int) (h : x * y + y * x + z = 10) : 2 * x * y + z = 10 := by
  ring_nf at h ⊢
  exact h
```

仮定 `h` とゴールの環式部分を正規化し、一致させてから `exact` で閉じる。

### 例 3: 後続タクティクへの前処理

```lean
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

-- ha : 0 < a, ⊢ 0 < a ^ 2 + 2 * a + 1
example (a : ℝ) (ha : 0 < a) : 0 < (a + 1) ^ 2 := by
  ring_nf
  -- ⊢ 0 < 1 + 2 * a + a ^ 2 に正規化される
  nlinarith [sq_nonneg a]
```

`ring_nf` で式を整理してから `nlinarith` で閉じるコンボパターン。

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `ring` | 上位 | 等式を閉じることを要求する。恒等式の証明なら `ring` を使う |
| `field_simp` | 前処理 | 分数式の分母を消去する。`field_simp` → `ring_nf` のコンボ |
| `simp` | 代替 | 一般的な簡約。`ring_nf` は環に特化した正規化 |
| `abel` | 部分 | 加法群のみの正規化。乗算を含まない場合に使う |
| `linear_combination` | 後続 | 仮定の線形結合で残ったゴールを `ring_nf` で整理 |

## 参照

- [Mathlib4 docs — ring_nf](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Ring/Basic.html)

---

> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
