# `module` — 加群・ベクトル空間の等式証明

**カテゴリ**: 代数 | **定義元**: `Mathlib.Tactic.Module.moduleStx` | **ソース**: Mathlib

---

## 概要

`module` は加群（Module）やベクトル空間上の等式を自動証明する。スカラー乗法 (`r • x`)・加法 (`+`)・減算 (`-`)・ゼロ (`0`) を含む式を正規形に変換し、両辺を比較する。
`abel` が自然数スカラー倍 (`n • x`) のみを扱うのに対し、`module` は任意の可換環上のスカラー乗法をサポートする。

## ゴールパターン

**Before:**
```lean
R : Type*
M : Type*
inst₁ : CommRing R
inst₂ : AddCommGroup M
inst₃ : Module R M
r : R
x y : M
⊢ r • (x + y) = r • x + r • y
```

**After:**
```lean
-- ゴールが閉じる（no goals）
```

## 構文

```lean
module
```

## 必須 import

```lean
import Mathlib.Tactic.Module
```

## Pros（使うべき場面）

- 加群・ベクトル空間上の等式をワンショットで閉じる
- スカラー乗法の分配法則・結合法則を自動処理
- `abel` では扱えない一般のスカラー倍 (`r • x` で `r` が環の元) に対応
- 線形代数の基本的な等式証明に有用

## Cons（注意・失敗ケース）

- 非線形なスカラー演算（スカラー同士の乗算を含む複雑な式）は扱えない場合がある
- 不等式は対象外 → `linarith` / `nlinarith` を使うこと
- スカラーの等式（`r = s` 型）は `ring` で処理するのが適切
- `Module` インスタンスが適切に設定されていないと失敗する

## コードサンプル

### 例 1: スカラー乗法の分配法則

```lean
import Mathlib.Tactic.Module

-- ⊢ r • (x + y) = r • x + r • y
example [CommRing R] [AddCommGroup M] [Module R M] (r : R) (x y : M) :
    r • (x + y) = r • x + r • y := by
  module
```

加群の公理（`smul_add`）を自動適用して閉じる。

### 例 2: スカラー倍の線形結合

```lean
import Mathlib.Tactic.Module

-- ⊢ r • x + s • x = (r + s) • x
example [CommRing R] [AddCommGroup M] [Module R M] (r s : R) (x : M) :
    r • x + s • x = (r + s) • x := by
  module
```

`add_smul` を自動認識し、スカラーを集約する。

### 例 3: ゼロスカラーの消去

```lean
import Mathlib.Tactic.Module

-- ⊢ (0 : R) • x + r • y = r • y
example [CommRing R] [AddCommGroup M] [Module R M] (r : R) (x y : M) :
    (0 : R) • x + r • y = r • y := by
  module
```

`zero_smul` を適用して `0 • x = 0` を消去する。

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `abel` | 部分 | 加法群の等式（自然数スカラー倍のみ）。一般のスカラー乗法なら `module` |
| `ring` | 補完 | スカラー環上の等式（`r * s = s * r` など）。加群の元の等式は `module` |
| `linear_combination` | 拡張 | 仮定の線形結合でゴールを証明。残余を `module` / `ring` で処理 |
| `simp [smul_add, add_smul]` | 手動代替 | `module` が失敗する場合に個別の補題で手動証明 |
| `ring_nf` | 前処理 | スカラー部分の整理。`ring_nf` → `module` のコンボ |

## 参照

- [Mathlib4 docs — module](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Module.html)

---

> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
