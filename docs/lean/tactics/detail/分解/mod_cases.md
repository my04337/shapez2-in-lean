# `mod_cases` — 剰余によるケース分析

**カテゴリ**: 分解 | **定義元**: `Mathlib.Tactic.ModCases.modCasesStx` | **ソース**: Mathlib

---

## 概要

`mod_cases` は整数・自然数の値を剰余（mod）で場合分けするタクティクである。
`mod_cases h : n % m` の形式で使用し、`n % m` の取りうるすべての値（`0, 1, ..., m-1`）に対して
サブゴールを生成する。各ケースで `h : n % m = k` が仮定として追加される。
数論的な証明や周期的な性質の証明に特に有効。

---

## ゴールパターン

**適用対象**: 整数・自然数の剰余に関する命題

**適用前**
```lean
n : Int
⊢ P n
```

**適用後** (`mod_cases h : n % 3`)
```lean
-- ケース 1: h : n % 3 = 0 ⊢ P n
-- ケース 2: h : n % 3 = 1 ⊢ P n
-- ケース 3: h : n % 3 = 2 ⊢ P n
```

---

## 構文

```lean
mod_cases h : n % m          -- n % m の全ケースで分析
```

---

## 必須 import

```lean
import Mathlib.Tactic.ModCases
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `mod_cases h : n % m` | `n % m` の全ての剰余値でケース分析 |

---

## Pros（使うべき場面）

- 剰余に基づく場合分けが一行で完了する
- 数論的な命題（偶奇、3 の倍数の分類等）の証明で自然
- 各ケースで剰余の等式が仮定に追加されるため、`omega` 等で即座に処理できる

---

## Cons（注意・失敗ケース）

- 法 `m` が大きいとケース数が爆発する（`m = 100` なら 100 ケース）
- `Nat` と `Int` で剰余の挙動が異なる点に注意（`Int` の場合は負の値も考慮）
- `mod_cases` 後の各ケースが自明でない場合、`omega` や `ring` の追加が必要

---

## コードサンプル

### サンプル 1: 偶奇の場合分け

```lean
import Mathlib.Tactic.ModCases

example (n : Nat) : n % 2 = 0 ∨ n % 2 = 1 := by
  -- ⊢ n % 2 = 0 ∨ n % 2 = 1
  mod_cases h : n % 2
  · -- h : n % 2 = 0 ⊢ n % 2 = 0 ∨ n % 2 = 1
    left; exact h
  · -- h : n % 2 = 1 ⊢ n % 2 = 0 ∨ n % 2 = 1
    right; exact h
```

### サンプル 2: 3 の剰余の二乗

```lean
import Mathlib.Tactic.ModCases

example (n : Int) : n % 2 = 0 ∨ n % 2 = 1 := by
  -- ⊢ n % 2 = 0 ∨ n % 2 = 1
  mod_cases h : n % 2 <;> omega
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `omega` | 後処理 | `mod_cases` 後の各ケースの算術的処理に使う |
| `interval_cases` | 範囲分析 | 有界な変数の全値列挙。範囲が分かっている場合に使う |
| `cases` | 汎用分解 | 帰納型の一般的なケース分析 |
| `zify` | 型変換 | `Nat` → `Int` に持ち上げてから `mod_cases` を使う |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
