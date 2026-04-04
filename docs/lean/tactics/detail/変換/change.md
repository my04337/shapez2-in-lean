# `change` — ゴールを定義的に等しい型に変換する

**カテゴリ**: 変換 | **定義元**: `Lean.Parser.Tactic.change` | **ソース**: Lean4 core

---

## 概要

`change` は現在のゴールを、定義的に等しい（definitionally equal）別の型に書き換えるタクティクである。
ゴールの見た目を変えたい場合や、後続タクティクが特定の形を必要とする場合に使う。
新旧の型が定義的に等しくない場合はエラーとなる。`at h` で仮定に対しても適用できる。

---

## ゴールパターン

**適用前**
```lean
⊢ Nat.succ 0 = 1
```

**適用後（`change 1 = 1`）**
```lean
⊢ 1 = 1
```

---

## 構文

```lean
change newGoal
change newGoal at h
```

`newGoal` は現在のゴールと定義的に等しい型でなければならない。

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `change e` | ゴールを `e` に変換する |
| `change e at h` | 仮定 `h` の型を `e` に変換する |

---

## Pros（使うべき場面）

- ゴールの見た目を明示的に整理して後続タクティクの適用を容易にする
- 定義展開や β 簡約の結果を明示的に記述できるため、証明の意図が明確になる
- `at h` で仮定の型も変換できる

---

## Cons（注意・失敗ケース）

- 定義的に等しくない型を指定するとエラーになる
- 変換先の型を手動で書く必要があるため、複雑な型では冗長になりがち
- `dsimp` や `show` で代用できる場合が多い

---

## コードサンプル

### サンプル 1: ゴールの見た目を整理

```lean
example : Nat.succ (Nat.succ 0) = 2 := by
  -- ⊢ Nat.succ (Nat.succ 0) = 2
  change 2 = 2
  -- ⊢ 2 = 2
  rfl
```

### サンプル 2: 仮定を変換

```lean
example (h : Nat.succ 0 > 0) : 1 > 0 := by
  -- h : Nat.succ 0 > 0
  -- ⊢ 1 > 0
  change 1 > 0 at h
  -- h : 1 > 0
  exact h
```

### サンプル 3: 関数定義の展開

```lean
def double (n : Nat) : Nat := n + n

example : double 3 = 6 := by
  -- ⊢ double 3 = 6
  change 3 + 3 = 6
  -- ⊢ 3 + 3 = 6
  rfl
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `show` | 類似 | `show` もゴールの型を指定するが、複数ゴール時に対象ゴールを選択できる |
| `dsimp` | 自動版 | 定義的簡約を自動で行う。手動指定が不要 |
| `unfold` | 展開 | 定義名を指定して展開する。`change` より意図が明確 |
| `conv` | 精密版 | ゴールの特定部分だけを変換したい場合に使用 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
