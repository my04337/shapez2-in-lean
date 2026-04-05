# `reduce_mod_char` — 標数による法簡約を実行する

**カテゴリ**: 簡約 | **定義元**: `Mathlib.Tactic.ReduceModChar.reduce_mod_char` | **ソース**: Mathlib

---

## 概要

`reduce_mod_char` は有限体や `ZMod n` 等の標数を持つ環で、数値リテラルを標数で割った剰余に簡約するタクティクである。例えば `ZMod 7` で `10 = 3` を自動証明する。`CharP` インスタンスが必要。

---

## ゴールパターン

**適用前**
```lean
⊢ (10 : ZMod 7) = 3
```

**適用後**: ゴール閉鎖

---

## 構文

```lean
reduce_mod_char
reduce_mod_char at h
```

---

## 必須 import

```lean
import Mathlib.Tactic.ReduceModChar
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `reduce_mod_char` | ゴールの数値を標数で簡約 |
| `reduce_mod_char at h` | 仮定に適用 |

---

## Pros（使うべき場面）

- `ZMod n` や有限体での数値計算を自動化
- 標数に基づく等式を一撃で証明
- `norm_num` では対応しにくい法演算に対応

---

## Cons（注意・失敗ケース）

- `CharP` インスタンスが推論できない場合は失敗
- Mathlib import が必要
- 非数値の式には適用できない

---

## コードサンプル

### サンプル 1: ZMod での簡約

```lean
import Mathlib.Tactic.ReduceModChar
import Mathlib.Data.ZMod.Basic

example : (10 : ZMod 7) = 3 := by
  reduce_mod_char
```

### サンプル 2: 計算の簡約

```lean
import Mathlib.Tactic.ReduceModChar
import Mathlib.Data.ZMod.Basic

example : (100 : ZMod 13) = 9 := by
  reduce_mod_char
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `norm_num` | 数値正規化 | 一般的な数値計算 |
| `ring` | 環の等式 | 環の等式証明 |
| `decide` | 決定手続き | Decidable な有限型の判定 |

---

## 参照

- [Mathlib4 ドキュメント — ReduceModChar](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/ReduceModChar.html)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
