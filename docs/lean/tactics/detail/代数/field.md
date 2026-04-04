# `field` — field_simp + ring の組み合わせ

**カテゴリ**: 代数 | **定義元**: `Mathlib.Tactic.FieldSimp` | **ソース**: Mathlib

---

## 概要

`field_simp` は分母を払って有理式を整数式に変換し、その後 `ring` で等式を閉じるワークフローの前半を担うタクティクである。分母が 0 でないことの証明を自動検索し、分数を含む等式を分母なしの等価な式に変換する。

---

## ゴールパターン

**適用前**
```lean
⊢ a / b + c / d = (a * d + b * c) / (b * d)
```

**適用後**（`field_simp`）
```lean
⊢ a * (b * d) + ... = ...  -- 分母が払われた等式
```

---

## 構文

```lean
field_simp
field_simp [h₁, h₂]
field_simp at h
```

---

## 必須 import

```lean
import Mathlib.Tactic.FieldSimp
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `field_simp` | ゴールの分母を払う |
| `field_simp [h]` | 追加の simp 補題を使って分母を払う |
| `field_simp at h` | 仮定 `h` の分母を払う |

---

## Pros（使うべき場面）

- 分数・除算を含む等式の証明
- `ring` 前の前処理として分母を払う
- 分母 ≠ 0 の自動証明

---

## Cons（注意・失敗ケース）

- 分母が 0 でないことの証明が見つからない場合は失敗
- 整数のみの式なら `ring` だけで十分
- Mathlib import が必要

---

## コードサンプル

### サンプル 1: field_simp + ring

```lean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

example (a b : ℚ) (hb : b ≠ 0) : a / b * b = a := by
  field_simp
```

### サンプル 2: 分母払い後の ring

```lean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

example (x : ℚ) (hx : x ≠ 0) : 1 / x + 1 / x = 2 / x := by
  field_simp
  ring
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `ring` | 多項式等式 | 分数なしの多項式等式 |
| `norm_num` | 数値計算 | 具体的数値の等式 |
| `simp` | 汎用簡約 | 一般的な簡約 |

---

## 参照

- [Mathlib4 ドキュメント — FieldSimp](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/FieldSimp.html)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
