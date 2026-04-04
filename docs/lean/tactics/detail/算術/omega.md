# `omega` — 線形算術の決定手続き

**カテゴリ**: 算術 | **定義元**: `Lean.Parser.Tactic.omega` | **ソース**: Lean 4 core

---

## 概要

自然数 (`Nat`) および整数 (`Int`) の線形算術ゴールを完全に決定する。等式・不等式・否定・整除性を扱い、`x / k` や `x % k`（`k` がリテラル）は補助変数導入で処理する。
Lean 4.x 以降で大幅に強化され、多くの算術証明で最初に試すべきタクティク。

## ゴールパターン

**Before:**
```lean
n : Nat
⊢ 0 ≤ n
```

**After:**
```lean
-- ゴールが閉じる（no goals）
```

**Before:**
```lean
a b : Int
⊢ a + b = b + a
```

**After:**
```lean
-- ゴールが閉じる（no goals）
```

## 構文

```lean
omega
omega +splitDisjunctions
omega +splitNatSub
omega +splitNatAbs
omega +splitMinMax
```

## オプション一覧

| オプション | 説明 |
|---|---|
| `+splitDisjunctions` | 仮定中の論理和（`∨`）をケース分割して処理する |
| `+splitNatSub` | `Nat` の減算 `a - b` をケース分割（`a ≥ b` と `a < b`）して処理する |
| `+splitNatAbs` | `Int.natAbs` をケース分割して処理する |
| `+splitMinMax` | `min` / `max` をケース分割して処理する |

## Pros（使うべき場面）

- `Nat` / `Int` の線形算術に対する完全な決定手続き
- `Fin n`, `UInt8`, `UInt16`, `UInt32`, `UInt64` などの型も自動変換して処理
- 高速。ほとんどの算術ゴールを一撃で閉じる
- `+splitDisjunctions`, `+splitNatSub` などのオプションで適用範囲を拡張可能
- 仮定をコンテキストから自動で取り込む

## Cons（注意・失敗ケース）

- 実数 (`Real`)・有理数 (`ℚ`) には適用不可 → `linarith` を使うこと
- 非線形の乗算項（`a * b` で `a`, `b` が両方変数）は原則扱えない → `nlinarith` を使うこと
- ゴールに局所変数がある場合は自動では `revert` しない（`omega` 前に `revert` が必要な場合あり）
- `Nat` の減算はフロア減算のため直感に反する結果になることがある（`+splitNatSub` が必要）

## コードサンプル

### 例 1: Nat の基本的な不等式

```lean
example (n : Nat) : 0 ≤ n := by omega
```

自然数は常に非負なので `omega` が即座に閉じる。

### 例 2: Int の交換法則

```lean
example (a b : Int) : a + b = b + a := by omega
```

線形算術の等式として処理される。

### 例 3: 仮定を使った推論

```lean
example (n : Nat) (h : n < 5) : n ≤ 4 := by omega
```

コンテキストの仮定 `h` を自動的に取り込み、`n < 5 → n ≤ 4` を導出する。

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `linarith` | 補完 | `Real`, `ℚ` など順序体上の線形算術。`Nat`/`Int` でも使えるが `omega` のほうが高速 |
| `norm_num` | 補完 | 数値リテラルの計算に特化。`2 + 3 = 5` など具体値の評価 |
| `nlinarith` | 拡張 | 非線形算術。`a * b ≤ c` のような乗算を含むゴール |
| `grind` | 上位 | SMT 風の汎用タクティク。内部で `omega` を含む複数の決定手続きを呼び出す |
| `simp +arith` | 代替 | `simp` の算術拡張。簡約の一部として算術を処理 |

## 参照

- [Lean 4 Reference — omega](https://lean-lang.org/doc/reference/latest/Tactics/Arithmetic/)

---

> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
