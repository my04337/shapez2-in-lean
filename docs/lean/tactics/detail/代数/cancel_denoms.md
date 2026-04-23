# `cancel_denoms` — 分母の消去

**カテゴリ**: 代数 | **定義元**: `Mathlib.Tactic.CancelDenoms.cancelDenomsTac` | **ソース**: Mathlib

---

## 概要

`cancel_denoms` は分数を含む等式・不等式の両辺に分母の最小公倍数を掛けて、
整数（または分母なしの）表現に変換するタクティクである。
体（`Field`）上の式から分母を取り除き、`ring` や `omega` で閉じやすい形に変換する。
分数の扱いが煩雑な線形算術や等式証明の前処理として有効。

---

## ゴールパターン

**適用対象**: 分数を含む等式・不等式

**適用前**
```lean
⊢ a / 2 + b / 3 = (3 * a + 2 * b) / 6
```

**適用後**
```lean
-- 分母が消去された等式に変換される
⊢ 3 * a + 2 * b = 3 * a + 2 * b
```

---

## 構文

```lean
cancel_denoms
```

引数は取らない。

---

## 必須 import

```lean
import Mathlib.Tactic.CancelDenoms
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `cancel_denoms` | 分母の最小公倍数を掛けて分母を消去 |

オプションはない。

---

## Pros（使うべき場面）

- 分数を含む等式・不等式を自動で分母なしの形に変換
- `ring` や `linarith` の前処理として使うと証明が通りやすくなる
- 複数の異なる分母が混在する場合も LCM を計算して処理

---

## Cons（注意・失敗ケース）

- `Field` インスタンスが必要。整数環（`Int`、`Nat`）単体では使えない
- 分母が変数（ゼロ除算の可能性あり）の場合は失敗することがある
- 変換後のゴールが自明でない場合、別のタクティクが必要

---

## コードサンプル

### サンプル 1: 基本的な分母消去

```lean
import Mathlib.Tactic.CancelDenoms

example (a : ℚ) : a / 2 + a / 2 = a := by
  -- ⊢ a / 2 + a / 2 = a
  cancel_denoms
  -- ⊢ a + a = 2 * a  （分母が消去される）
  ring
```

### サンプル 2: 異なる分母の混合

```lean
import Mathlib.Tactic.CancelDenoms

example (x : ℚ) : x / 3 + x / 6 = x / 2 := by
  -- ⊢ x / 3 + x / 6 = x / 2
  cancel_denoms
  -- 分母 6 が掛けられ整数の等式に変換
  ring
```

### サンプル 3: 不等式での使用

```lean
import Mathlib.Tactic.CancelDenoms

example (x : ℚ) (h : x > 0) : x / 4 > 0 := by
  -- ⊢ x / 4 > 0
  cancel_denoms
  -- ⊢ x > 0  （分母 4 を掛けて消去）
  linarith
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `ring` | 後処理 | `cancel_denoms` 後の等式を `ring` で閉じる |
| `field_simp` | 類似 | `field_simp` も分母を消去するが、より広範な簡約を行う |
| `linarith` | 後処理 | 分母消去後の不等式を線形算術で処理 |
| `norm_num` | 数値正規化 | 具体的な数値の分数計算に使う |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
