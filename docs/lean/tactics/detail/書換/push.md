# `push` — 演算子を内側に押し込む

**カテゴリ**: 書換 | **定義元**: `Mathlib.Tactic.PushNeg` / `Mathlib.Tactic.NormCast` | **ソース**: Mathlib

---

## 概要

`push` は否定やキャストを式の内側に押し込むタクティクの総称である。`push_neg` は否定 `¬` を量化子の内側へ分配し、`push_cast` は型キャストを演算子の内側に押し込む。`pull` が外側に引き上げるのに対し、`push` は内側に移動する。

---

## ゴールパターン

**適用前**（`push_neg` の例）
```lean
⊢ ¬∃ x, P x
```

**適用後**
```lean
⊢ ∀ x, ¬P x
```

---

## 構文

```lean
push_neg
push_neg at h
push_cast
push_cast at h
```

---

## 必須 import

```lean
import Mathlib.Tactic.PushNeg     -- push_neg
import Mathlib.Tactic.NormCast    -- push_cast
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `push_neg` | ゴールの否定を内側に分配 |
| `push_neg at h` | 仮定 `h` で否定を分配 |
| `push_cast` | キャストを内側に押し込む |
| `push_cast at h` | 仮定 `h` でキャストを押し込む |

---

## Pros（使うべき場面）

- `¬∀` → `∃ ¬` のような正規形変換
- キャストを演算の内側に揃えたい場合
- `linarith` / `omega` 前の前処理として

---

## Cons（注意・失敗ケース）

- 望む方向と逆の場合は `pull` 系を使う
- Mathlib import が必要
- `push_neg` は `DecidableEq` が必要な場合がある

---

## コードサンプル

### サンプル 1: push_neg で否定を分配

```lean
import Mathlib.Tactic.PushNeg

example (h : ¬∀ x : Nat, x = 0) : ∃ x : Nat, x ≠ 0 := by
  push_neg at h
  exact h
```

### サンプル 2: push_cast でキャストを分配

```lean
import Mathlib.Tactic.NormCast

example (n m : Nat) : ((n + m : Nat) : Int) = (n : Int) + (m : Int) := by
  push_cast
  ring
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `pull_neg` | 逆方向 | 否定を外側に引き上げる |
| `norm_num` | 数値正規化 | 数値式だけなら `norm_num` |
| `norm_cast` | キャスト正規化 | キャストの自動正規化 |
| `by_contra` | 背理法 | 否定を仮定に移す |

---

## 参照

- [Mathlib4 ドキュメント — PushNeg](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/PushNeg.html)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
