# `pull` — 定数・演算子を外側に引き上げる

**カテゴリ**: 書換 | **定義元**: `Mathlib.Tactic.Push` | **ソース**: Mathlib

---

## 概要

`pull` は `push_neg` のように特定の演算子（否定、キャスト等）を式の外側に引き上げるタクティクの総称である。Mathlib では `push_neg` のペアとなる `pull_neg` や、`push_cast` / `pull_cast` として提供される。`push` が内側に押し込むのに対し、`pull` は外側に引き出す。

---

## ゴールパターン

**適用前**（`pull_neg` の例）
```lean
⊢ ¬(∀ x, P x)
```

**適用後**
```lean
⊢ ∃ x, ¬P x
```

---

## 構文

```lean
pull_neg
pull_neg at h
pull_cast
pull_cast at h
```

---

## 必須 import

```lean
import Mathlib.Tactic.PushNeg     -- pull_neg
import Mathlib.Tactic.NormCast    -- pull_cast（push_cast の逆方向）
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `pull_neg` | ゴールの否定を外側に引き上げ |
| `pull_neg at h` | 仮定 `h` で否定を引き上げ |

---

## Pros（使うべき場面）

- 否定やキャストを正規形に揃えたい場合
- `push_neg`/`push_cast` の逆操作が必要な場合
- 式を外側から読みやすい形にしたい場合

---

## Cons（注意・失敗ケース）

- `pull_neg` と `push_neg` の使い分けに慣れが必要
- Mathlib import が必要
- 一部の形式では効果がない場合がある

---

## コードサンプル

### サンプル 1: 否定の引き上げ

```lean
import Mathlib.Tactic.PushNeg

example : ¬(∀ x : Nat, x = 0) := by
  push_neg
  exact ⟨1, by omega⟩
```

### サンプル 2: push_cast との対比

```lean
import Mathlib.Tactic.NormCast

-- push_cast: キャストを内側に押し込む
-- pull_cast: キャストを外側に引き出す（push_cast の逆）
example (n m : Nat) : (n : Int) + (m : Int) = ((n + m : Nat) : Int) := by
  push_cast
  ring
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `push_neg` | 逆方向 | 否定を内側に押し込む |
| `push_cast` | キャスト版 | キャストを内側に押し込む |
| `norm_cast` | 正規化 | キャストを自動正規化 |

---

## 参照

- [Mathlib4 ドキュメント — PushNeg](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/PushNeg.html)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
