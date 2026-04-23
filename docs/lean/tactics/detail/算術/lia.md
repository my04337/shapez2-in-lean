# `lia` — 線形整数算術ソルバ

**カテゴリ**: 算術 | **定義元**: `Lean.Parser.Tactic.lia` | **ソース**: Lean 4 core（Batteries 由来）

---

## 概要

`lia` は線形整数算術（Linear Integer Arithmetic）を解く決定手続きである。`omega` の後継・拡張として位置づけられ、`Nat` および `Int` 上の線形不等式・等式・整除性を扱う。
内部的には `omega` と同様のアルゴリズムを使用するが、将来的な拡張を見据えた統一インタフェースとして提供される。現時点では `omega` とほぼ同等の動作をするが、Batteries / Lean の更新に伴い機能が拡張される可能性がある。

## ゴールパターン

**Before:**
```lean
n m : Nat
h : n + m = 10
⊢ m + n = 10
```

**After:**
```lean
-- ゴールが閉じる（no goals）
```

**Before:**
```lean
a : Int
h : 2 * a = 6
⊢ a = 3
```

**After:**
```lean
-- ゴールが閉じる（no goals）
```

## 構文

```lean
lia
```

## Pros（使うべき場面）

- `Nat` / `Int` 上の線形算術を自動的に閉じる
- `omega` と同等の解決能力を持つ統一インタフェース
- 等式・不等式・否定を含む算術ゴールに対応
- オプション指定なしでシンプルに使える

## Cons（注意・失敗ケース）

- 現時点では `omega` とほぼ同等のため、`omega` が失敗する場合は `lia` も失敗する可能性が高い
- 実数 (`Real`)・有理数 (`ℚ`) には適用不可 → `linarith` を使うこと
- 非線形の乗算項には対応不可 → `nlinarith` を使うこと
- Lean / Batteries のバージョンによって動作が異なる場合がある

## コードサンプル

### 例 1: 自然数の加法交換

```lean
-- ⊢ m + n = 10
example (n m : Nat) (h : n + m = 10) : m + n = 10 := by
  lia
```

加法の交換法則を線形算術として処理し、仮定からゴールを閉じる。

### 例 2: 整数の等式

```lean
-- h : 2 * a = 6 ⊢ a = 3
example (a : Int) (h : 2 * a = 6) : a = 3 := by
  lia
```

線形方程式を解き、`a = 3` を導出する。

### 例 3: 不等式の推論

```lean
-- h₁ : a ≤ b, h₂ : b ≤ c ⊢ a ≤ c
example (a b c : Nat) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  lia
```

推移律を線形算術として自動処理する。

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `omega` | 同等 | 現時点ではほぼ同等。どちらを使っても良い |
| `linarith` | 補完 | `Real`, `ℚ` 等の順序体上で動作。`Nat` / `Int` のみなら `lia` / `omega` が高速 |
| `nlinarith` | 拡張 | 非線形算術。乗算・累乗を含む不等式に使用 |
| `norm_num` | 補完 | 数値リテラルの計算に特化 |
| `simp +arith` | 代替 | `simp` の算術オプション。簡約の一部として算術を処理 |

## 参照

- [Lean 4 Reference — Arithmetic Tactics](https://lean-lang.org/doc/reference/latest/Tactics/Arithmetic/)
- [Batteries4 — Tactic.Lia](https://leanprover-community.github.io/mathlib4_docs/Init/Omega/Tactic.html)

---

> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
