# `group` — 群の等式の正規化・自動証明

**カテゴリ**: 代数 | **定義元**: `Mathlib.Tactic.Group.group` | **ソース**: Mathlib

---

## 概要

`group` は（乗法的）自由群の等式を自動証明する。群の結合法則・単位元・逆元の公理のみを使い、式を正規形に変換して両辺を比較する。
可換性は仮定しないため、非可換群でも動作する。加法的な群等式には `abel` を使うこと。

## ゴールパターン

**Before:**
```lean
G : Type*
inst : Group G
a b : G
⊢ a * b * b⁻¹ = a
```

**After:**
```lean
-- ゴールが閉じる（no goals）
```

**Before:**
```lean
G : Type*
inst : Group G
a : G
⊢ a * a⁻¹ * a = a
```

**After:**
```lean
-- ゴールが閉じる（no goals）
```

## 構文

```lean
group
```

## 必須 import

```lean
import Mathlib.Tactic.Group
```

## Pros（使うべき場面）

- 群の結合法則・単位元・逆元の公理のみで等式を証明
- 非可換群でも動作する（`abel` は可換限定）
- `a * a⁻¹ = 1`、`1 * a = a` などの基本恒等式を自動処理
- 冪乗 (`a ^ n`、`a ^ (-n : ℤ)`) も正しく扱う

## Cons（注意・失敗ケース）

- 加法的表記（`+`, `-`, `0`）には対応しない → `abel` を使うこと
- 可換群の等式なら `abel`（加法）や `ring`（環）の方が適切
- 群の公理を超える性質（たとえば特定の関係 `a * b = b * a`）は使用しない
- 準群・モノイド（逆元がない構造）には対応しない

## コードサンプル

### 例 1: 逆元の消去

```lean
import Mathlib.Tactic.Group

-- ⊢ a * b * b⁻¹ = a
example [Group G] (a b : G) : a * b * b⁻¹ = a := by
  group
```

`b * b⁻¹ = 1` を自動認識し、消去する。

### 例 2: 複合的な逆元操作

```lean
import Mathlib.Tactic.Group

-- ⊢ (a * b)⁻¹ * a * b * c = c
example [Group G] (a b c : G) : (a * b)⁻¹ * a * b * c = c := by
  group
```

`(a * b)⁻¹ * (a * b) = 1` を導出し、残りを整理する。

### 例 3: 冪乗を含む等式

```lean
import Mathlib.Tactic.Group

-- ⊢ a ^ 2 * a⁻¹ = a
example [Group G] (a : G) : a ^ 2 * a⁻¹ = a := by
  group
```

`a ^ 2 = a * a` に展開し、`a * a * a⁻¹ = a` を証明する。

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `abel` | 加法版 | 加法的可換群の等式。`group` は乗法群（非可換含む） |
| `ring` | 上位 | 可換環の等式。乗算と加算の両方を含む場合に使う |
| `simp [mul_assoc, mul_inv_cancel]` | 手動代替 | `group` が失敗する場合に個別の補題で手動証明 |
| `noncomm_ring` | 拡張 | 非可換環の等式。加算と乗算の両方が非可換な場合 |

## 参照

- [Mathlib4 docs — group](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Group.html)

---

> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
