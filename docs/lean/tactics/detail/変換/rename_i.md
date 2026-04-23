# `rename_i` — アクセス不能な名前をリネームする

**カテゴリ**: 変換 | **定義元**: `Lean.Parser.Tactic.renameI` | **ソース**: Lean4 core

---

## 概要

`rename_i` はコンテキスト中の最後の `n` 個のアクセス不能な名前（`✝`, `✝¹` など）を、
指定した名前にリネームするタクティクである。
`cases` や `intro` で自動生成された名前を読みやすい名前に置き換える際に使用する。
`_` を指定するとその位置のリネームをスキップできる。

---

## ゴールパターン

**適用前**
```lean
n✝ : Nat
h✝ : n✝ > 0
⊢ n✝ ≥ 1
```

**適用後（`rename_i n h`）**
```lean
n : Nat
h : n > 0
⊢ n ≥ 1
```

---

## 構文

```lean
rename_i name₁ name₂ ...
rename_i _ name₂
```

- 名前は最後の仮定から逆順に対応する
- `_` でスキップ（リネームしない）が可能

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `rename_i x y` | 最後の 2 つのアクセス不能名を `x`, `y` にリネーム |
| `rename_i _ y` | 最後の 1 つだけリネームし、その前はスキップ |

---

## Pros（使うべき場面）

- `cases` や `match` で生成された `✝` 名を人間が読みやすい名前に変更できる
- 証明の可読性が大幅に向上する
- `intro` で名前を付け忘れた仮定の後付けリネームに便利

---

## Cons（注意・失敗ケース）

- アクセス不能な名前がない場合はエラーになる
- 名前の個数が合わないとエラーになる
- `rcases` や `obtain` を使えば最初から名前を付けられるため、`rename_i` が不要な場合も多い

---

## コードサンプル

### サンプル 1: cases 後のリネーム

```lean
example (h : ∃ n : Nat, n > 0) : True := by
  cases h
  -- n✝ : Nat
  -- h✝ : n✝ > 0
  rename_i n hn
  -- n : Nat
  -- hn : n > 0
  trivial
```

### サンプル 2: スキップ付きリネーム

```lean
example (h : ∃ n : Nat, ∃ m : Nat, n + m > 0) : True := by
  cases h
  rename_i n h2
  cases h2
  rename_i _ hm
  -- n : Nat, _: Nat, hm : n + ... > 0
  trivial
```

### サンプル 3: match 後のリネーム

```lean
example (b : Bool) : b = true ∨ b = false := by
  cases b
  · -- case false
    right; rfl
  · -- case true
    left; rfl
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `rcases` | 代替 | `rcases h with ⟨n, hn⟩` で最初から名前を付けられる |
| `obtain` | 代替 | `obtain ⟨n, hn⟩ := h` でパターンマッチと命名を同時に行う |
| `intro` | 前段 | `intro` で名前を付ければ `rename_i` が不要になる |
| `clear` | 仮定操作 | `clear` は仮定を除去する。`rename_i` は名前変更のみ |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
