# `eta_reduce` — η簡約を実行する

**カテゴリ**: 簡約 | **定義元**: `Mathlib.Tactic.etaReduceStx` | **ソース**: Mathlib

---

## 概要

`eta_reduce` はゴール中の `fun x => f x` を `f` に簡約するタクティクである。η-レデックスを除去して式を簡潔にする。メタプログラミングや `conv` 内で展開された式をクリーンアップする前処理として有用。

---

## ゴールパターン

**適用前**
```lean
⊢ (fun x => f x) = f
```

**適用後**
```lean
⊢ f = f
```

---

## 構文

```lean
eta_reduce
eta_reduce at h
eta_reduce at *
```

---

## 必須 import

```lean
import Mathlib.Tactic.EtaReduce
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `eta_reduce` | ゴールのη-レデックスを簡約 |
| `eta_reduce at h` | 仮定 `h` に適用 |
| `eta_reduce at *` | 全仮定とゴールに適用 |

---

## Pros（使うべき場面）

- 冗長な `fun x => f x` を `f` にクリーンアップ
- `beta_reduce` と組み合わせた式の正規化
- `conv` 後の式整理

---

## Cons（注意・失敗ケース）

- η-レデックスがない場合は効果なし
- Mathlib import が必要
- 通常は `simp` や `dsimp` で十分対応可能

---

## コードサンプル

### サンプル 1: 基本的なη簡約

```lean
import Mathlib.Tactic.EtaReduce

example (f : Nat → Nat) : (fun x => f x) = f := by
  eta_reduce
  rfl
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `eta_expand` | 逆操作 | η展開（`f` → `fun x => f x`） |
| `beta_reduce` | β簡約 | β-レデックスの簡約 |
| `dsimp` | 定義的簡約 | 包括的な定義的簡約 |

---

## 参照

- [Mathlib4 ドキュメント — EtaReduce](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/EtaReduce.html)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
