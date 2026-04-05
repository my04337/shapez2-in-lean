# `ring` — 可換環上の等式の自動証明

**カテゴリ**: 代数 | **定義元**: `Mathlib.Tactic.Ring.ring` / `Mathlib.Tactic.Ring.ringNF` | **ソース**: Mathlib

---

## 概要

可換半環 (`CommSemiring`) 以上の代数構造で成り立つ等式を自動証明する。多項式の展開・因数分解相当の正規化を行い、両辺が同一の正規形になれば証明完了。
`ring_nf` は正規形への書き換えのみ行い、ゴールは閉じない。

## ゴールパターン

**Before:**
```lean
a b : Int
⊢ (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2
```

**After:**
```lean
-- ゴールが閉じる（no goals）
```

**Before (ring_nf):**
```lean
x y : Int
⊢ (x + y) * (x - y) = x ^ 2 - y ^ 2
```

**After (ring_nf):**
```lean
-- 両辺が同一の正規形になり、ゴールが閉じる（no goals）
```

## 構文

```lean
ring
ring_nf
ring_nf at h
ring_nf at *
```

## 必須 import

```lean
import Mathlib.Tactic.Ring
```

## オプション一覧

| オプション | 説明 |
|---|---|
| `ring_nf` | 正規形への書き換えのみ行い、ゴールを閉じない。中間ステップで使用する |
| `ring_nf at h` | 仮定 `h` に対して正規化を適用する |
| `ring_nf at *` | ゴールと全仮定に対して正規化を適用する |

## Pros（使うべき場面）

- 可換環上の等式をワンショットで閉じる
- `Nat`, `Int`, `ℚ`, `ℝ`, 多項式環など広範な型をサポート
- 計算ミスの心配がない（完全な決定手続き）
- 冪乗 (`^`) を含む式も正しく展開して処理する

## Cons（注意・失敗ケース）

- 非可換環には使えない → `noncomm_ring` を使うこと
- 不等式には使えない → `nlinarith` + ヒント、または `positivity` を使うこと
- 体の除算を含む等式 → `field_simp` で分母を消してから `ring` を使うこと
- 仮定を使った書き換えはできない（仮定が必要なら `linarith` / `linear_combination` を使うこと）
- `Nat` の減算（フロア減算）には注意が必要。`Int` にキャストしてから使うのが安全

## コードサンプル

### 例 1: 展開公式

```lean
import Mathlib.Tactic.Ring

example (a b : Int) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring
```

二項展開を自動で検証する。

### 例 2: 実数上の等式

```lean
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

example (x : ℝ) : x * (x + 1) = x ^ 2 + x := by
  ring
```

実数上でも同様に動作する。

### 例 3: ring_nf による正規化

```lean
import Mathlib.Tactic.Ring

example (a b c : Int) (h : a + b + c = 0) : c + b + a = 0 := by
  ring_nf at h ⊢
  exact h
```

`ring_nf` で両辺を正規形に整理した後、仮定をそのまま適用する。

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `ring!` | `norm_num` を併用してより強力に正規化する |
| `ring1` | 1 ステップのみの ring |
| `ring1!` | `ring1` + `norm_num` |
| `ring_nf!` | `ring_nf` + `norm_num` |
| `ring1_nf` | 1 ステップの正規化 |
| `ring1_nf!` | `ring1_nf` + `norm_num` |

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `ring_nf` | サブセット | 正規形への書き換えのみ。ゴールを閉じずに整理したい場合 |
| `field_simp` | 前処理 | 分数式の分母を消去する。`field_simp` → `ring` のコンボが定番 |
| `linear_combination` | 拡張 | 仮定（等式）を線形結合してゴールを閉じる。残ったゴールを `ring` で処理 |
| `abel` | 部分 | 加法的可換群（加法のみ）の等式に特化 |
| `noncomm_ring` | 拡張 | 非可換環上の等式を証明する |
| `nlinarith` | 補完 | 非線形の不等式を証明する。乗算を含む不等式に使う |

## 参照

- [Mathlib4 docs — ring](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Ring/Basic.html)
- [Mathematics in Lean — §2.2 Proving Identities in Algebraic Structures](https://leanprover-community.github.io/mathematics_in_lean/)

---

> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
