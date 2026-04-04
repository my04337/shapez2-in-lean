# `subst` — 等式仮定で変数を代入して除去する

**カテゴリ**: 変換 | **定義元**: `Lean.Parser.Tactic.subst` | **ソース**: Lean4 core

---

## 概要

`subst` は仮定 `h : x = e` または `h : e = x`（ここで `x` は自由変数）を使い、
コンテキスト中の全出現を代入で置き換え、変数 `x` と仮定 `h` を同時に除去するタクティクである。
等式仮定を消費して文脈を簡潔にする基本操作であり、`cases` や `rcases` の後処理として頻出する。

---

## ゴールパターン

**適用前**
```lean
x : Nat
h : x = 3
⊢ x + 1 = 4
```

**適用後（`subst h`）**
```lean
⊢ 3 + 1 = 4
```

---

## 構文

```lean
subst h
subst x
```

- `h`: 等式仮定（`x = e` または `e = x` の形）
- `x`: 代入される自由変数を直接指定（対応する等式仮定を自動で探す）

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `subst h` | 仮定 `h` の等式を使って代入・除去する |
| `subst x` | 変数 `x` に関する等式仮定を探して代入・除去する |
| `subst_vars` | 全ての代入可能な等式仮定を一括処理する |

---

## Pros（使うべき場面）

- 自由変数を具体的な式に代入してコンテキストを簡潔にする
- `cases` で得た等式仮定を消化するのに最適
- 仮定と変数を同時に除去するため、後続の証明がシンプルになる

---

## Cons（注意・失敗ケース）

- 等式の片方が自由変数でなければならない（`3 = 5` のような等式には使えない）
- 変数が他の仮定の型に依存している場合、依存順序の問題でエラーになることがある
- `rw` と異なり、変数自体を除去するため元に戻せない

---

## コードサンプル

### サンプル 1: 基本的な代入

```lean
example (x : Nat) (h : x = 5) : x + 1 = 6 := by
  -- x : Nat, h : x = 5
  -- ⊢ x + 1 = 6
  subst h
  -- ⊢ 5 + 1 = 6
  rfl
```

### サンプル 2: 変数名で指定

```lean
example (n : Nat) (h : n = 0) : n * n = 0 := by
  -- n : Nat, h : n = 0
  -- ⊢ n * n = 0
  subst n
  -- ⊢ 0 * 0 = 0
  rfl
```

### サンプル 3: subst_vars で一括処理

```lean
example (x y : Nat) (h1 : x = 1) (h2 : y = 2) : x + y = 3 := by
  -- x y : Nat, h1 : x = 1, h2 : y = 2
  -- ⊢ x + y = 3
  subst_vars
  -- ⊢ 1 + 2 = 3
  rfl
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `rw` | 代替 | `rw` は等式で書き換えるが変数は除去しない。`subst` は変数ごと除去 |
| `simp` | 自動化 | `simp only [h]` で書き換え可能だが、変数除去はしない |
| `cases` | 前段 | `cases` で帰納型を分解した後の等式仮定を `subst` で消化する |
| `injection` | 前段 | コンストラクタの等式から内部等式を取り出し、`subst` で代入する |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
