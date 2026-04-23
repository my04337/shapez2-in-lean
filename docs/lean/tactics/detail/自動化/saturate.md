# `saturate` — Aesop 前方推論による仮定の飽和

**カテゴリ**: 自動化 | **定義元**: `Aesop.Frontend.saturate` | **ソース**: Aesop

---

## 概要

`saturate` は `@[aesop]` 属性で登録された前方推論（forward）補題を使って、
ローカルコンテキストを飽和させるタクティクである。
ゴール自体は閉じず、仮定に対して適用可能な前方推論ルールを繰り返し適用し、
新たな仮定が導出されなくなるまで拡張する。
`aesop` の前処理として使ったり、手動証明の前に有用な仮定を自動で追加したりする用途に適する。

---

## ゴールパターン

**適用対象**: 任意（ゴールは変化しない。仮定が拡張される）

**適用前**
```lean
h : P
⊢ Q
```

**適用後** （前方推論で仮定が追加される）
```lean
h : P
h' : R       -- @[aesop forward] 補題により導出
⊢ Q
```

---

## 構文

```lean
saturate                        -- 登録済み前方推論ルールで飽和
saturate [lemma₁, lemma₂]     -- 追加の補題も使用
```

---

## 必須 import

```lean
import Aesop
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `saturate` | `@[aesop forward]` ルールで仮定を飽和 |
| `saturate [lem₁, lem₂]` | 追加の補題も前方推論に使用 |

---

## Pros（使うべき場面）

- 仮定から導出可能な情報を網羅的に追加し、後続の証明を楽にする
- `aesop` で証明が通らない場合の代替として、仮定飽和 + 手動証明が有効
- `@[aesop forward]` ルールの効果を局所的に確認できる

---

## Cons（注意・失敗ケース）

- ゴール自体は閉じないため、別のタクティクで証明を完了する必要がある
- 前方推論ルールが多いとコンテキストが肥大化し、後続の `simp` が遅くなる
- 登録されたルール次第で効果が大きく異なる

---

## コードサンプル

### サンプル 1: 基本的な飽和

```lean
import Aesop

@[aesop forward safe] theorem pos_of_ne_zero (n : Nat) (h : n ≠ 0) : n > 0 := by omega

example (n : Nat) (h : n ≠ 0) : n ≥ 1 := by
  -- h : n ≠ 0
  -- ⊢ n ≥ 1
  saturate
  -- h : n ≠ 0, fwd : n > 0  （前方推論で追加）
  -- ⊢ n ≥ 1
  omega
```

### サンプル 2: 追加補題を指定

```lean
import Aesop

example (a b : Nat) (h : a < b) : a + 1 ≤ b := by
  -- h : a < b
  -- ⊢ a + 1 ≤ b
  saturate [Nat.succ_le_of_lt]
  -- Nat.succ_le_of_lt h が仮定に追加される
  assumption
```

---

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `saturate?` | 追加された仮定を提案する |

## 関連タクティク
| `simp` | 簡約 | 仮定飽和後の簡約に使う |
| `have` | 手動導入 | 特定の仮定を手動で追加する場合 |
| `apply_rules` | ルール適用 | 前方推論ではなく後方推論のルール適用 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
