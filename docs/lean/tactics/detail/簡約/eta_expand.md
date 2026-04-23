# `eta_expand` — η展開を実行する

**カテゴリ**: 簡約 | **定義元**: `Mathlib.Tactic.etaExpandStx` | **ソース**: Mathlib

---

## 概要

`eta_expand` はゴール中の関数 `f` を `fun x => f x` にη展開するタクティクである。`eta_reduce` の逆操作。`conv` や `simp` の前処理として、関数をラムダ式に展開して後続タクティクで内部にアクセスしやすくする場合に使う。

---

## ゴールパターン

**適用前**
```lean
⊢ f = g
```

**適用後**
```lean
⊢ (fun x => f x) = (fun x => g x)
```

---

## 構文

```lean
eta_expand
eta_expand at h
eta_expand at *
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
| `eta_expand` | ゴール中の関数をη展開 |
| `eta_expand at h` | 仮定 `h` にη展開を適用 |

---

## Pros（使うべき場面）

- `conv` でラムダ式の内部にアクセスしたい場合の前処理
- `funext` 適用前の準備
- 関数のポイントフリー表記をポイントワイズに変換

---

## Cons（注意・失敗ケース）

- 式が冗長になる
- Mathlib import が必要
- 通常は `funext` で直接ラムダ変数を束縛する方が良い

---

## コードサンプル

### サンプル 1: 基本的なη展開

```lean
import Mathlib.Tactic.EtaReduce

example (f : Nat → Nat) (h : ∀ x, f x = x) : f = id := by
  funext x
  simp [h]
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `eta_reduce` | 逆操作 | η簡約（`fun x => f x` → `f`） |
| `funext` | 関数拡張 | 関数等式を要素ごとに分解 |
| `beta_reduce` | β簡約 | β-レデックスの簡約 |

---

## 参照

- [Mathlib4 ドキュメント — EtaReduce](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/EtaReduce.html)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
