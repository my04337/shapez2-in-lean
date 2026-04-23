# `convert` — 型の不一致を許容し差分をサブゴール化する `exact`

**カテゴリ**: 補題適用 | **定義元**: `Mathlib.Tactic.Convert` | **ソース**: Mathlib

---

## 概要

`convert` は `exact` に似ているが、与えた項の型がゴールと**完全一致しなくてもよい**。
型の不一致部分を `congr` で分解し、差分をサブゴールとして生成する。
補題の型がゴールと「ほぼ一致するが微妙に異なる」場合に、手動で書換をせずに済む強力なタクティクである。
`exact` で型エラーが出るが「方向は合っている」と分かるときに `convert` への切り替えが有効。

---

## ゴールパターン

**適用対象**: 仮定依存（ゴールに近い型を持つ項が必要）

**適用前**
```lean
h : a + b = c
⊢ b + a = c
```

**適用後** (`convert h`)
```lean
-- ゴール 1: ⊢ b + a = a + b
```

---

## 構文

```lean
convert e                    -- 型の差分をサブゴール化
convert e using n            -- congr の再帰深度を n に制限
convert e using 0            -- 差分分解せず、ゴール全体の等価性をサブゴール化
convert e with x y           -- congr の変数名を指定
```

---

## 必須 import

```lean
import Mathlib.Tactic.Convert
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `convert e` | デフォルト深度で差分を分解 |
| `convert e using n` | `congr` の再帰深度を `n` に制限 |
| `convert e using 0` | 分解せず、ゴール全体 `⊢ goal = typeof(e)` をサブゴール化 |
| `convert e with x y` | `congr` で導入される変数に名前を指定 |

---

## Pros（使うべき場面）

- 補題の型とゴールが微妙に異なる場合（引数の順序、演算の結合方向など）に有効
- `rw` で事前に書き換えるよりも簡潔で宣言的
- `using n` で分解の深さを制御でき、不要なサブゴールの発生を防げる
- `exact` が失敗するが「ほぼ合っている」ときの定番の代替手段

---

## Cons（注意・失敗ケース）

- `congr` の分解が過剰になり、自明でないサブゴールが大量に生じることがある
- `using n` を適切に設定しないと、意図しない深さまで分解される
- `convert` が生成するサブゴールの型が予測しにくい場合がある
- Lean4 core には含まれないため、Mathlib への依存が必要

---

## コードサンプル

### サンプル 1: 引数の順序が異なる補題を適用

```lean
import Mathlib.Tactic.Convert

example (a b c : Nat) (h : a + b = c) : b + a = c := by
  -- ⊢ b + a = c
  convert h using 1
  -- ⊢ b + a = a + b
  omega
```

### サンプル 2: using 0 で全体を等価性のサブゴールに

```lean
import Mathlib.Tactic.Convert

example (a b : Nat) (h : a + b = b + a) : a + b = b + a := by
  -- ⊢ a + b = b + a
  convert h using 0
  -- (ゴールが自動的に閉じる)
```

### サンプル 3: 存在命題への適用

```lean
import Mathlib.Tactic.Convert

example (a b : Nat) (h : ∃ n : Nat, n = a + b) : ∃ n : Nat, n = b + a := by
  -- ⊢ ∃ n, n = b + a
  convert h using 2
  -- ⊢ b + a = a + b
  ring
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `exact` | 厳密版 | 型が完全一致する場合のみ。差分があれば `convert` を使う |
| `convert_to` | ゴール変形版 | ゴール自体を別の型に変換。`convert` は項からゴールを変形 |
| `congr` | 差分分解 | ゴール内の等式を構造的に分解。`convert` は `exact` + `congr` の合成 |
| `refine` | プレースホルダ版 | 項の構造を制御しつつサブゴール生成。型一致は必要 |

---

## 参照

- [Mathlib4 ドキュメント — convert](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Convert.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
