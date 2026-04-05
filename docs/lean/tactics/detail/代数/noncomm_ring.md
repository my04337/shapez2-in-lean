# `noncomm_ring` — 非可換環の等式正規化

**カテゴリ**: 代数 | **定義元**: `Mathlib.Tactic.NoncommRing.noncomm_ring` | **ソース**: Mathlib

---

## 概要

`noncomm_ring` は非可換環（乗法の交換律を仮定しない環）における等式を正規化するタクティクである。
内部的には `simp` と `abel` を組み合わせ、分配則の展開・加法部分の正規化を行う。
`ring` が使えない非可換な代数構造（行列環、四元数、一般の環など）の等式証明に適する。

---

## ゴールパターン

**適用対象**: 非可換環上の等式

**適用前**
```lean
⊢ (a + b) * c = a * c + b * c
```

**適用後**
```lean
-- ゴールなし（証明完了）
```

---

## 構文

```lean
noncomm_ring
```

引数は取らない。

---

## 必須 import

```lean
import Mathlib.Tactic.NoncommRing
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `noncomm_ring` | 非可換環の等式を正規化して証明 |

オプションはない。

---

## Pros（使うべき場面）

- `ring` が使えない非可換環の等式を自動的に処理できる
- 分配則の展開、加法の正規化、零元・単位元の処理を一発で行う
- 行列計算、四元数、一般の `Ring` インスタンスで利用可能

---

## Cons（注意・失敗ケース）

- 可換環なら `ring` の方が高速で確実
- 非常に複雑な式ではタイムアウトする可能性がある
- 環以外の代数構造（半群、モノイドのみ）には対応していない

---

## コードサンプル

### サンプル 1: 右分配則

```lean
import Mathlib.Tactic.NoncommRing

variable [Ring R] (a b c : R)

example : (a + b) * c = a * c + b * c := by
  -- ⊢ (a + b) * c = a * c + b * c
  noncomm_ring
  -- ゴールなし（証明完了）
```

### サンプル 2: 展開と整理

```lean
import Mathlib.Tactic.NoncommRing

variable [Ring R] (a b : R)

example : (a + b) * (a - b) = a * a - a * b + b * a - b * b := by
  -- ⊢ (a + b) * (a - b) = a * a - a * b + b * a - b * b
  noncomm_ring
  -- ゴールなし（証明完了）
```

### サンプル 3: 零元の処理

```lean
import Mathlib.Tactic.NoncommRing

variable [Ring R] (a : R)

example : a * 0 + 0 * a = 0 := by
  -- ⊢ a * 0 + 0 * a = 0
  noncomm_ring
  -- ゴールなし（証明完了）
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `ring` | 可換版 | 可換環の等式正規化。可換環なら `ring` が高速 |
| `abel` | 加法のみ | 可換群の加法正規化。加法部分のみ処理 |
| `simp` | 汎用簡約 | 個別の補題で段階的に簡約する場合 |
| `ring_nf` | 正規形 | 可換環の正規形に変換（等式でなくても使える） |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
