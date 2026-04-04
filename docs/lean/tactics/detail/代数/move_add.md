# `move_add` / `move_mul` — 指定項の末尾移動

**カテゴリ**: 代数 | **定義元**: `Mathlib.MoveAdd.tacticMove_add_` | **ソース**: Mathlib

---

## 概要

`move_add` は加法式中の指定した項を末尾に移動するタクティクである。
結合律と交換律（AC）を利用して項の並び替えを行う。
`move_mul` は乗法版で同様の機能を提供する。
`ac_rfl` は等式の両辺を一致させるが、`move_add` は片辺の項順序を制御する点が異なる。
特定の項を目立たせたり、後続の `ring_nf` や `simp` と組み合わせる前処理に適する。

---

## ゴールパターン

**適用対象**: 加法（`move_add`）・乗法（`move_mul`）を含む等式・式

**適用前**
```lean
⊢ a + b + c = ...
```

**適用後** (`move_add [c]` で `c` を末尾に移動)
```lean
⊢ a + b + c = ...   -- ただし左辺の並びが変更される
```

---

## 構文

```lean
move_add [e₁, e₂, ...]         -- 指定した項を末尾に移動
move_add [← e₁]                -- 指定した項を先頭に移動
move_mul [e₁, e₂, ...]         -- 乗法版
```

---

## 必須 import

```lean
import Mathlib.Tactic.MoveAdd
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `move_add [e]` | 項 `e` を加法式の末尾に移動 |
| `move_add [← e]` | 項 `e` を加法式の先頭に移動 |
| `move_add [e₁, e₂]` | 複数の項を指定順に末尾に移動 |
| `move_mul [e]` | 乗法版。項 `e` を乗法式の末尾に移動 |

---

## Pros（使うべき場面）

- 式の項順序を明示的に制御できる
- `ring_nf` や `simp` の前処理として、特定項を目立たせる位置に配置できる
- `conv` + `rw [add_comm]` の繰り返しより簡潔

---

## Cons（注意・失敗ケース）

- 等式の証明自体は行わない（並び替えのみ）
- `Comm` と `Assoc` インスタンスが必要
- 項の指定が式中に存在しない場合は何もしない

---

## コードサンプル

### サンプル 1: 指定項を末尾に移動

```lean
import Mathlib.Tactic.MoveAdd

example (a b c : Nat) : a + c + b = a + b + c := by
  -- ⊢ a + c + b = a + b + c
  move_add [c]
  -- c を末尾に移動
  -- ⊢ a + b + c = a + b + c
  rfl
```

### サンプル 2: 先頭への移動

```lean
import Mathlib.Tactic.MoveAdd

example (a b c : Int) : a + b + c = c + a + b := by
  -- ⊢ a + b + c = c + a + b
  move_add [← c]
  -- ⊢ c + a + b = c + a + b
  rfl
```

### サンプル 3: move_mul の使用

```lean
import Mathlib.Tactic.MoveAdd

example (a b c : Int) : a * b * c = c * a * b := by
  -- ⊢ a * b * c = c * a * b
  move_mul [c]
  -- 末尾に c を移動した結果 ac_rfl 相当で一致
  ac_rfl
```

---

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `move_mul` | 乗算の項を移動する（可換乗法版） |
| `move_oper` | 任意の可換演算子の項を移動する |

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `ac_rfl` | 等式証明 | AC で一致する等式を直接閉じる |
| `ring_nf` | 正規化 | 環の正規形に変換。並び順は制御不可 |
| `abel` | 加法正規化 | 可換群の正規化 |
| `conv` | 位置指定 | より細かい式変換の制御が必要な場合 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
