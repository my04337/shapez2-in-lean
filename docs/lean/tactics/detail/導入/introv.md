# `introv` — 依存変数を自動命名で導入する

**カテゴリ**: 導入 | **定義元**: `Mathlib.Tactic.introv` | **ソース**: Mathlib

---

## 概要

`introv h₁ h₂` は `∀` で束縛された変数を自動命名で導入し、名前を与えた分だけ仮定を導入する。`intro` と異なり、型が `Prop` でない変数には自動的に名前を付け、`Prop` 型の仮定だけにユーザ指定の名前を使う。

---

## ゴールパターン

**適用前**
```lean
⊢ ∀ (n : Nat) (m : Nat), n < m → n ≤ m
```

**適用後**（`introv h`）
```lean
n m : Nat
h : n < m
⊢ n ≤ m
```

---

## 構文

```lean
introv
introv h₁ h₂
```

- 名前は `Prop` 型の仮定に順にバインドされる
- 型変数は自動命名

---

## 必須 import

```lean
import Mathlib.Tactic.Core
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `introv` | 全変数を自動命名で導入 |
| `introv h₁ h₂` | Prop 仮定に `h₁`, `h₂` を付けて導入 |

---

## Pros（使うべき場面）

- 型変数の名前を手動で指定したくない場合
- 仮定（Prop）だけに名前を付けたい場合
- `intro` で大量の変数名を書くのが面倒な場合

---

## Cons（注意・失敗ケース）

- 自動命名された変数名が分かりにくい場合がある
- `intro` の方が全変数を制御でき堅牢
- Mathlib import が必要

---

## コードサンプル

### サンプル 1: 仮定だけ名前付け

```lean
import Mathlib.Tactic.Core

example : ∀ (n m : Nat), n < m → n ≤ m := by
  introv h
  -- n m : Nat, h : n < m ⊢ n ≤ m
  omega
```

### サンプル 2: 名前なしで全導入

```lean
import Mathlib.Tactic.Core

example : ∀ (n : Nat), n = n := by
  introv
  rfl
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `intro` | 標準版 | 全変数の名前を制御するなら `intro` |
| `intros` | 複数版 | 全部自動命名で導入するなら `intros` |
| `rintro` | パターン版 | 導入と分解を同時に行うなら `rintro` |

---

## 参照

- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
