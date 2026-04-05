# `infer_instance` — 型クラスインスタンスの合成でゴールを閉じる

**カテゴリ**: 閉鎖 | **定義元**: `Lean.Parser.Tactic.tacticInfer_instance` | **ソース**: Lean4 core

---

## 概要

`infer_instance` は型クラスのインスタンス合成機構を呼び出し、ゴールを閉じるタクティクである。
内部的には `exact inferInstance` と同等であり、ゴールの型が型クラスのインスタンス型である場合に、
登録済みのインスタンスを自動で検索・合成して証明を完了する。
`[instance]` 属性で登録されたインスタンスが利用される。

---

## ゴールパターン

**適用対象**: 型クラスのインスタンスを要求するゴール

**適用前**
```lean
⊢ Inhabited Nat
```

**適用後**
```lean
-- ゴールなし（証明完了）
```

---

## 構文

```lean
infer_instance
```

引数は取らない。

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `infer_instance` | インスタンス合成でゴールを閉じる |

オプションはない。

---

## Pros（使うべき場面）

- 型クラスインスタンスの存在証明を一発で閉じられる
- `Inhabited`、`DecidableEq`、`BEq`、`Ord` などの標準クラスで特に有効
- 暗黙のインスタンス検索の結果を明示的に確認できる

---

## Cons（注意・失敗ケース）

- インスタンスが登録されていない場合は失敗する
- インスタンス検索がタイムアウトする場合がある（複雑なクラス階層）
- 合成されたインスタンスが意図したものと異なる場合がある

---

## コードサンプル

### サンプル 1: Inhabited インスタンス

```lean
example : Inhabited Nat := by
  -- ⊢ Inhabited Nat
  infer_instance
  -- ゴールなし（証明完了）
```

### サンプル 2: DecidableEq インスタンス

```lean
example : DecidableEq Bool := by
  -- ⊢ DecidableEq Bool
  infer_instance
  -- ゴールなし（証明完了）
```

### サンプル 3: 複合インスタンスの合成

```lean
example : BEq (List Nat) := by
  -- ⊢ BEq (List Nat)
  infer_instance
  -- ゴールなし（BEq Nat から List の BEq が合成される）
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `exact` | 汎用版 | `exact inferInstance` と同等だが、`infer_instance` の方が意図が明確 |
| `apply` | 部分適用 | インスタンスの一部を手動で埋める場合 |
| `trivial` | メタ | `trivial` もインスタンス合成を試行するが限定的 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
