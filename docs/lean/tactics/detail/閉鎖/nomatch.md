# `nomatch` — 空のパターンマッチでゴールを閉じる

**カテゴリ**: 閉鎖 | **定義元**: `Lean.Parser.Tactic.«tacticNomatch_,,»` | **ソース**: Lean4 core

---

## 概要

`nomatch` は、与えられた項の型が空（有効なコンストラクタが存在しない）であることを利用して、パターンマッチのケースが存在しないことをカーネルに示し、ゴールを閉じるタクティクである。
`exact nomatch h` の糖衣構文として機能し、`h` の型の全コンストラクタが矛盾により排除できる場合に成功する。
複数の項をカンマ区切りで渡すことで、複数の引数に対する同時パターンマッチとして機能する。

---

## ゴールパターン

**適用前**
```lean
h : Empty
⊢ P
```

**適用後**
```lean
-- ゴールなし（証明完了）
```

---

## 構文

```lean
nomatch e
nomatch e₁, e₂, ...
```

`e` は型が空であると判定できる項。複数項を渡す場合はカンマ区切り。

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `nomatch e` | 項 `e` の型が空であることを利用してゴールを閉じる |
| `nomatch e₁, e₂` | 複数項の同時パターンマッチで空であることを示す |

---

## Pros（使うべき場面）

- 仮定が `Empty`、`Fin 0`、矛盾した等式を持つ帰納型のケースなど、空型と判定できる場合に有効
- `cases` で分岐した後、到達不能なケースを明示的に閉じるのに適している
- 複数の discriminant を同時に渡せるため、組み合わせで空になるケースにも対応

---

## Cons（注意・失敗ケース）

- 渡す項の型が空でないと判定された場合は失敗する
- 型展開や仮定の正規化が必要な場合、先に `simp` や `subst` で整理する必要がある
- 空であることの判定はカーネルのパターンマッチ網羅性チェックに依存するため、複雑なインデックス付き型で失敗する場合がある
- 仮定なしで使う場合は `nofun` の方が適切

---

## コードサンプル

### サンプル 1: Empty 型の仮定

```lean
example (h : Empty) : 1 = 2 := by
  -- h : Empty
  -- ⊢ 1 = 2
  nomatch h
  -- ゴールなし（証明完了）
```

### サンプル 2: Fin 0 の仮定

```lean
example (i : Fin 0) : False := by
  -- i : Fin 0
  -- ⊢ False
  nomatch i
  -- ゴールなし（証明完了）
```

### サンプル 3: 矛盾するコンストラクタ等式

```lean
example (h : ([] : List Nat) = [1, 2]) : False := by
  -- h : [] = [1, 2]
  -- ⊢ False
  nomatch h
  -- ゴールなし（証明完了）
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `nofun` | 類似 | `nofun` は関数型ゴール全体を空パターンマッチで閉じる。`nomatch` は具体的な項を指定する |
| `contradiction` | 汎用 | `contradiction` はコンテキスト全体から矛盾を検出。`nomatch` は指定した項の型の空性を利用 |
| `cases` | 前処理 | `cases` でパターン分岐後に到達不能ケースを `nomatch` で閉じるパターンが一般的 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
