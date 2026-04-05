# `generalize_proofs` — 証明項を変数に一般化する

**カテゴリ**: 変換 | **定義元**: `Mathlib.Tactic.GeneralizeProofs.generalizeProofs` | **ソース**: Mathlib

---

## 概要

`generalize_proofs` はゴールや仮定中に埋め込まれた証明項（`Prop` の項）を新しい仮定変数に置き換えるタクティクである。大きな証明項がゴール内に展開されて可読性が下がっている場合に、それを `h : P` のような仮定に切り出す。`simp` や `rw` の前処理として、証明項をクリーンアップする用途で使う。

---

## ゴールパターン

**適用前**
```lean
⊢ f (proof_of_P) = g (proof_of_P)
```

**適用後**（`generalize_proofs h`）
```lean
h : P
⊢ f h = g h
```

---

## 構文

```lean
generalize_proofs
generalize_proofs h₁ h₂
generalize_proofs at h
```

- 名前を指定すると各証明項にその名前を付ける
- `at h` で仮定中の証明項も一般化

---

## 必須 import

```lean
import Mathlib.Tactic.GeneralizeProofs
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `generalize_proofs` | ゴール中の全証明項を自動命名で変数化 |
| `generalize_proofs h₁ h₂` | 順に名前を付与 |
| `generalize_proofs at hyp` | 仮定 `hyp` 中の証明項を変数化 |

---

## Pros（使うべき場面）

- ゴール内の証明項が大きく展開されて読めない場合のクリーンアップに最適
- `Array.get` 等のインデックス範囲証明を変数化して `simp` を通しやすくする
- 証明項の構造に依存しない証明を書ける

---

## Cons（注意・失敗ケース）

- 一般化しすぎると変数が増え、後続の証明が複雑になる場合がある
- Prop でない項は対象外
- Mathlib import が必要

---

## コードサンプル

### サンプル 1: 基本的な使い方

```lean
import Mathlib.Tactic.GeneralizeProofs

example (a : Array Nat) (h : 0 < a.size) : a[0] = a[0] := by
  generalize_proofs
  rfl
```

### サンプル 2: 名前付き一般化

```lean
import Mathlib.Tactic.GeneralizeProofs

example (a : Array Nat) (h : 0 < a.size) (h2 : 1 < a.size) :
    a[0] + a[1] = a[0] + a[1] := by
  generalize_proofs p1 p2
  -- p1 : 0 < a.size, p2 : 1 < a.size がコンテキストに追加
  rfl
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `generalize` | 項の一般化 | 任意の項を変数化するなら `generalize`、証明項のみなら `generalize_proofs` |
| `extract_lets` | let 抽出 | let 束縛を引き上げるなら `extract_lets` |
| `simp` | 簡約 | 証明項クリーンアップ後に `simp` で処理 |

---

## 参照

- [Mathlib4 ドキュメント — GeneralizeProofs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/GeneralizeProofs.html)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
