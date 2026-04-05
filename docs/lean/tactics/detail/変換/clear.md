# `clear` — 仮定をコンテキストから除去する

**カテゴリ**: 変換 | **定義元**: `Lean.Parser.Tactic.clear` | **ソース**: Lean4 core

---

## 概要

`clear` は指定した仮定をコンテキストから完全に除去するタクティクである。
不要な仮定を取り除くことでコンテキストを簡潔に保ち、後続タクティクの可読性を向上させる。
除去対象の仮定に他の仮定やゴールが依存している場合はエラーとなる。

---

## ゴールパターン

**適用前**
```lean
h1 : P
h2 : Q
⊢ R
```

**適用後（`clear h1`）**
```lean
h2 : Q
⊢ R
```

---

## 構文

```lean
clear h
clear h₁ h₂ h₃
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `clear h` | 仮定 `h` を除去する |
| `clear h₁ h₂` | 複数の仮定を同時に除去する |

---

## Pros（使うべき場面）

- 不要な仮定を除去してコンテキストを簡潔にする
- `induction` や `cases` で依存関係エラーが出る場合、不要な仮定を先に `clear` して解消できる
- ゴールに無関係な仮定を除去して証明の見通しをよくする

---

## Cons（注意・失敗ケース）

- 他の仮定やゴールが依存している仮定は除去できない
- 一度除去した仮定は復元できない（不可逆操作）
- 必要な仮定を誤って除去すると証明不能になる

---

## コードサンプル

### サンプル 1: 不要な仮定の除去

```lean
example (h1 : True) (h2 : 1 = 1) : 2 + 2 = 4 := by
  -- h1 : True, h2 : 1 = 1
  -- ⊢ 2 + 2 = 4
  clear h1 h2
  -- ⊢ 2 + 2 = 4
  rfl
```

### サンプル 2: 依存関係の解消

```lean
example (n : Nat) (h : n = n) : True := by
  -- n : Nat, h : n = n
  -- ⊢ True
  clear h
  -- n : Nat
  -- ⊢ True
  clear n
  -- ⊢ True
  trivial
```

### サンプル 3: induction の前処理

```lean
example (n m : Nat) (h : n + m = 10) : n + m = 10 := by
  -- n m : Nat, h : n + m = 10
  -- ⊢ n + m = 10
  exact h
```

---

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `clear!` | 依存する仮定も含めて強制的に除去する |
| `clear_` | アンダースコア付き名前の仮定を除去する |
| `clear_value` | 仮定の値（定義）を除去して型だけ残す |

## 関連タクティク
| `rename_i` | 名前変更 | 仮定を除去せず名前だけ変更する |
| `have` | 逆操作 | 新しい仮定を導入する。`clear` は除去する |
| `simp` | 自動簡約 | 不要な仮定を直接除去するのではなく、自動で使い切る |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
