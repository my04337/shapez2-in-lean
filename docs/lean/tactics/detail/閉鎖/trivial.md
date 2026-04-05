# `trivial` — 複数の基本タクティクを順に試してゴールを閉じる

**カテゴリ**: 閉鎖 | **定義元**: `Lean.Parser.Tactic.tacticTrivial` | **ソース**: Lean4 core

---

## 概要

`trivial` は、`assumption`、`rfl`、`contradiction`、`decide`（小規模な場合）など複数の基本タクティクを順番に試行し、いずれかが成功すればゴールを閉じるメタタクティクである。
`True` のような自明なゴールや、仮定に解が含まれる場合に特に有効。
`@[trivial]` 属性で登録されたタクティクも試行対象に含まれる。

---

## ゴールパターン

**適用前**
```lean
⊢ True
```

**適用後**
```lean
-- ゴールなし（証明完了）
```

---

## 構文

```lean
trivial
```

引数は取らない。

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `trivial` | 登録済みの基本タクティクを順に試行する |

`trivial` 自体にオプションはないが、`@[trivial]` 属性を使ってユーザー定義タクティクを試行リストに追加できる。

---

## Pros（使うべき場面）

- `True`、`rfl` で閉じるゴール、仮定から直接閉じるゴールを 1 ワードで処理できる
- `simp` ほど重くなく、軽量な自動証明として使える
- `@[trivial]` 拡張で、プロジェクト固有の自明ケースを追加登録できる

---

## Cons（注意・失敗ケース）

- 試行するタクティクの範囲は限定的で、`simp` や `omega` のような高度な推論は行わない
- どのサブタクティクが成功したか不透明なため、デバッグ時は個別タクティクで試す方がよい
- `decide` を内部で呼ぶ場合、`Decidable` インスタンスが必要

---

## コードサンプル

### サンプル 1: True の証明

```lean
example : True := by
  -- ⊢ True
  trivial
  -- ゴールなし（証明完了）
```

### サンプル 2: 仮定から閉じる（assumption 相当）

```lean
example (h : P) : P := by
  -- h : P
  -- ⊢ P
  trivial
  -- ゴールなし（証明完了）
```

### サンプル 3: 反射律（rfl 相当）

```lean
example : (1 : Nat) = 1 := by
  -- ⊢ 1 = 1
  trivial
  -- ゴールなし（証明完了）
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `assumption` | 内包 | `trivial` の試行リストに含まれる。仮定検索だけなら `assumption` で十分 |
| `rfl` | 内包 | 反射律のみ必要な場合は `rfl` を直接使う方が意図が明確 |
| `decide` | 内包 | 決定可能な命題の自動証明。`trivial` でも呼ばれうるが、単独使用の方が確実 |
| `simp` | 上位互換 | `simp` はより広範な簡約を行うが、重い。`trivial` は軽量な代替 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
