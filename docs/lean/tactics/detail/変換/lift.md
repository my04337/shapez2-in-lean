# `lift` — 型キャストを通じて値を持ち上げる

**カテゴリ**: 変換 | **定義元**: `Mathlib.Tactic.lift` | **ソース**: Mathlib

---

## 概要

`lift` は値を条件付きで別の型に「持ち上げる」タクティクである。
典型的には `lift n to ℕ using h` のように、整数 `n : ℤ` を自然数 `n : ℕ` に持ち上げ、
条件 `h : 0 ≤ n` を消費する。`CanLift` 型クラスに依存し、持ち上げ条件を自動検索する。

---

## ゴールパターン

**適用前**
```lean
n : Int
h : 0 ≤ n
⊢ P n
```

**適用後（`lift n to Nat using h`）**
```lean
n : Nat
⊢ P ↑n
```

---

## 構文

```lean
lift x to T
lift x to T using h
lift x to T using h with y hy
```

- `x`: 持ち上げる変数
- `T`: 持ち上げ先の型
- `h`: 持ち上げ条件の仮定（省略するとサブゴールが生成される）
- `y`: 新しい変数名、`hy`: 元の変数との関係の仮定名

---

## 必須 import

```lean
import Mathlib.Tactic.Lift
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `lift x to T` | 条件をサブゴールとして生成して持ち上げる |
| `lift x to T using h` | 条件仮定 `h` を使って持ち上げる |
| `lift x to T using h with y` | 新変数名 `y` を指定する |
| `lift x to T using h with y hy` | 新変数名と等式仮定名を指定する |

---

## Pros（使うべき場面）

- `ℤ` → `ℕ` など、条件付きの型変換を安全に行える
- キャスト（`↑`）を含む式を、キャスト元の型で直接扱えるようになる
- `CanLift` インスタンスが定義されていれば自動的に適用条件を検出する

---

## Cons（注意・失敗ケース）

- Mathlib のインポートと `CanLift` インスタンスが必要
- 持ち上げ条件を満たせない場合、サブゴールが残る
- 持ち上げ後の型キャスト（`↑`）が式中に現れ、`push_cast` 等での処理が必要になることがある

---

## コードサンプル

### サンプル 1: Int から Nat への持ち上げ

```lean
import Mathlib.Tactic.Lift

example (n : Int) (h : 0 ≤ n) : ∃ m : Nat, n = ↑m := by
  -- n : Int, h : 0 ≤ n
  -- ⊢ ∃ m : Nat, n = ↑m
  lift n to Nat using h
  -- n : Nat
  -- ⊢ ∃ m, ↑n = ↑m
  exact ⟨n, rfl⟩
```

### サンプル 2: with で変数名を指定

```lean
import Mathlib.Tactic.Lift

example (a : Int) (ha : 0 ≤ a) : a * a ≥ 0 := by
  -- a : Int, ha : 0 ≤ a
  lift a to Nat using ha with b
  -- b : Nat
  -- ⊢ ↑b * ↑b ≥ 0
  positivity
```

### サンプル 3: 条件をサブゴールとして生成

```lean
import Mathlib.Tactic.Lift

example (n : Int) (h : n * n ≥ 0) : True := by
  -- n : Int
  -- lift n to Nat のように条件なしで使う場合はサブゴールが生成される
  trivial
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `push_cast` | 後続 | `lift` 後に残る `↑` を整理する |
| `norm_cast` | 後続 | キャストを正規化してゴールを閉じる |
| `zify` | 逆方向 | `ℕ` → `ℤ` への変換。`lift` は `ℤ` → `ℕ` |
| `positivity` | 補完 | 非負性の証明。`lift` の条件証明に使えることがある |

---

## 参照

- [Mathlib4 ドキュメント — lift](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Lift.html)
- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
