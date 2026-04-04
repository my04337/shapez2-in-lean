# `swap_var` — コンテキスト中の変数名を入れ替える

**カテゴリ**: 変換 | **定義元**: `Mathlib.Tactic.SwapVar.swapVar` | **ソース**: Mathlib

---

## 概要

`swap_var a ↔ b` はコンテキスト中の変数 `a` と `b` の名前を入れ替えるタクティクである。`wlog` 等で対称的なケースを扱う際に、一方のケースの証明をもう一方に適用するための名前調整に使う。ゴールやコンテキストの意味論は変わらず、名前のみが変更される。

---

## ゴールパターン

**適用前**
```lean
a b : Nat
h : a < b
⊢ a ≤ b
```

**適用後**（`swap_var a ↔ b`）
```lean
b a : Nat
h : b < a
⊢ b ≤ a
```

---

## 構文

```lean
swap_var a ↔ b
swap_var a ↔ b, c ↔ d
```

- 複数ペアを同時に入れ替え可能

---

## 必須 import

```lean
import Mathlib.Tactic.SwapVar
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `swap_var a ↔ b` | `a` と `b` の名前を入れ替える |
| `swap_var a ↔ b, c ↔ d` | 複数ペアを同時入れ替え |

---

## Pros（使うべき場面）

- `wlog` の対称ケースで名前を揃える際に便利
- 証明の意味を変えずに可読性を改善できる
- 複数ペアの一括入れ替えで対称性の証明を簡潔にする

---

## Cons（注意・失敗ケース）

- 名前のみの変更で意味論的には何も変わらない
- Mathlib import が必要
- 型が異なる変数を入れ替えようとすると失敗する場合がある

---

## コードサンプル

### サンプル 1: 基本的な名前入れ替え

```lean
import Mathlib.Tactic.SwapVar

example (a b : Nat) (h : a = b) : a = b := by
  swap_var a ↔ b
  -- 名前が入れ替わり h : b = a ⊢ b = a
  exact h
```

### サンプル 2: wlog との組み合わせ

```lean
import Mathlib.Tactic.SwapVar

example (a b : Nat) : a + b = b + a := by
  omega
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `rename` | 名前変更 | 一方向のリネームなら `rename` |
| `rename_i` | 無名仮定のリネーム | 無名仮定に名前を付けるなら `rename_i` |
| `wlog` | 対称性利用 | 対称的ケースの帰着には `wlog` を使い、名前調整に `swap_var` |

---

## 参照

- [Mathlib4 ドキュメント — SwapVar](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/SwapVar.html)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
