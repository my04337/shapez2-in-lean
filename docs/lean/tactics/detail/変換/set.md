# `set` — 部分式に名前を付けて局所定義を導入する

**カテゴリ**: 変換 | **定義元**: `Mathlib.Tactic.set` | **ソース**: Mathlib

---

## 概要

`set` は部分式に名前を付けて局所定義を導入し、同時にコンテキスト中の全出現を書き換えるタクティクである。
`set x := e` で `x` が局所定義として導入され、`x = e` の等式（`hx`）もコンテキストに追加される。
`let` に似ているが、既存の出現を自動書き換えする点が異なる。

---

## ゴールパターン

**適用前**
```lean
⊢ f (a + b) + f (a + b) = 2 * f (a + b)
```

**適用後（`set x := f (a + b)`）**
```lean
x : τ := f (a + b)
⊢ x + x = 2 * x
```

---

## 構文

```lean
set x := e
set x := e with hx
set x : T := e
```

- `x`: 新しい変数名
- `e`: 名前を付ける部分式
- `hx`: 等式仮定の名前（省略時は自動命名）
- `T`: 型注釈（省略可）

---

## 必須 import

```lean
import Mathlib.Tactic.Set
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `set x := e` | `e` に `x` と名前を付け、全出現を書き換える |
| `set x := e with hx` | 等式 `hx : x = e` を仮定に追加する |
| `set x := e with ← hx` | 等式 `hx : e = x` を仮定に追加する（向き逆転） |

---

## Pros（使うべき場面）

- 繰り返し出現する複雑な部分式を短い名前に置き換えて可読性を向上できる
- 等式仮定が自動追加されるため、後で元の式に戻すことも容易
- `generalize` と異なり、局所定義として `x := e` がコンテキストに残る

---

## Cons（注意・失敗ケース）

- Mathlib のインポートが必要
- 部分式のマッチングが厳密で、見た目は同じでも定義的に異なると書き換えられない
- `let` と機能が重複する場合がある（`let` は Lean4 core、`set` は Mathlib）

---

## コードサンプル

### サンプル 1: 部分式への名前付け

```lean
import Mathlib.Tactic.Set

example (a b : Nat) : (a + b) + (a + b) = 2 * (a + b) := by
  -- ⊢ (a + b) + (a + b) = 2 * (a + b)
  set x := a + b
  -- x : Nat := a + b
  -- ⊢ x + x = 2 * x
  omega
```

### サンプル 2: 等式仮定付き

```lean
import Mathlib.Tactic.Set

example (l : List Nat) : l.length + l.length = 2 * l.length := by
  -- ⊢ l.length + l.length = 2 * l.length
  set n := l.length with hn
  -- n : Nat := l.length
  -- hn : n = l.length
  -- ⊢ n + n = 2 * n
  omega
```

### サンプル 3: 型注釈付き

```lean
import Mathlib.Tactic.Set

example (n : Nat) : n + 0 = n := by
  -- ⊢ n + 0 = n
  set m : Nat := n + 0 with hm
  -- m : Nat := n + 0
  -- hm : m = n + 0
  -- ⊢ m = n
  omega
```

---

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `set!` | 強制的に全ての出現を書き換える |

## 関連タクティク
| `generalize` | 抽象化 | `generalize` は変数に一般化する。`set` は局所定義として保持する |
| `change` | 型変換 | `change` はゴールの型自体を変換する。`set` は部分式に名前を付ける |
| `conv` | 精密変換 | 特定箇所のみ書き換えたい場合は `conv` が適切 |

---

## 参照

- [Mathlib4 ドキュメント — set](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Set.html)
- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
