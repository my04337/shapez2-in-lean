# `beta_reduce` — β簡約を実行する

**カテゴリ**: 簡約 | **定義元**: `Mathlib.Tactic.betaReduceStx` | **ソース**: Mathlib

---

## 概要

`beta_reduce` はゴール中の `(fun x => body) arg` 形式のβ-レデックスを `body[x := arg]` に簡約するタクティクである。`dsimp` や `simp` よりも限定的な変換で、β簡約のみを行いたい場合に使う。`at` 句で仮定にも適用可能。

---

## ゴールパターン

**適用前**
```lean
⊢ (fun x => x + 1) 5 = 6
```

**適用後**
```lean
⊢ 5 + 1 = 6
```

---

## 構文

```lean
beta_reduce
beta_reduce at h
beta_reduce at *
```

---

## 必須 import

```lean
import Mathlib.Tactic.BetaReduce
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `beta_reduce` | ゴールのβ-レデックスを簡約 |
| `beta_reduce at h` | 仮定 `h` に適用 |
| `beta_reduce at *` | 全仮定とゴールに適用 |

---

## Pros（使うべき場面）

- β簡約のみを surgical に適用したい場合
- `dsimp` が他の変換も行ってしまう場合の代替
- ラムダ式適用の明示的な簡約

---

## Cons（注意・失敗ケース）

- β-レデックスがない場合は効果なし
- Mathlib import が必要
- ほとんどの場合 `dsimp` や `simp` で十分

---

## コードサンプル

### サンプル 1: 基本的なβ簡約

```lean
import Mathlib.Tactic.BetaReduce

example : (fun x : Nat => x + 1) 5 = 6 := by
  beta_reduce
  -- ⊢ 5 + 1 = 6
  rfl
```

### サンプル 2: 仮定に適用

```lean
import Mathlib.Tactic.BetaReduce

example (h : (fun x : Nat => x) 0 = 0) : True := by
  beta_reduce at h
  -- h : 0 = 0
  trivial
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `dsimp` | 定義的簡約 | β簡約以外も含む定義的簡約 |
| `simp` | 汎用簡約 | simp 補題も使う汎用簡約 |
| `eta_reduce` | η簡約 | η-レデックスの簡約 |

---

## 参照

- [Mathlib4 ドキュメント — BetaReduce](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/BetaReduce.html)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
