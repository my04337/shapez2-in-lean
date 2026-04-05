# `extract_lets` — let 束縛をローカル定義に抽出する

**カテゴリ**: 変換 | **定義元**: `Mathlib.Tactic.ExtractLets.extractLets` | **ソース**: Mathlib

---

## 概要

`extract_lets` はゴールやコンテキスト中の `let` 束縛をトップレベルのローカル定義に引き上げるタクティクである。ゴールが `let x := e; body` の形をしているとき、`x` をコンテキストに移し `body` をゴールにする。`simp` や `rw` が let 内部にアクセスしにくい場合の前処理として有用。

---

## ゴールパターン

**適用前**
```lean
⊢ let x := 5; x + x = 10
```

**適用後**（`extract_lets x`）
```lean
x : Nat := 5
⊢ x + x = 10
```

---

## 構文

```lean
extract_lets
extract_lets x y z
```

- 名前を指定すると抽出された定義にその名前を付ける
- 名前省略時は自動命名

---

## 必須 import

```lean
import Mathlib.Tactic.ExtractLets
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `extract_lets` | 全 let 束縛を自動命名で抽出 |
| `extract_lets x y` | 順に `x`, `y` と命名して抽出 |

---

## Pros（使うべき場面）

- let 束縛がネストしてゴールが見づらい場合の整理に最適
- `simp` や `rw` が let 内部に到達しない場合の前処理として有効
- 抽出後は通常の仮定として扱えるため後続のタクティクと相性が良い

---

## Cons（注意・失敗ケース）

- let 束縛がない場合は効果なし
- Mathlib import が必要
- 大量の let があると抽出後のコンテキストが長くなる

---

## コードサンプル

### サンプル 1: 基本的な let 抽出

```lean
import Mathlib.Tactic.ExtractLets

example : (let x := 2; x + x) = 4 := by
  extract_lets x
  -- x : Nat := 2 ⊢ x + x = 4
  rfl
```

### サンプル 2: 複数の let 束縛

```lean
import Mathlib.Tactic.ExtractLets

example : (let a := 1; let b := 2; a + b) = 3 := by
  extract_lets a b
  -- a : Nat := 1, b : Nat := 2 ⊢ a + b = 3
  rfl
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `set` | ローカル定義導入 | 新しい定義を導入するなら `set`、既存 let を引き上げるなら `extract_lets` |
| `refold_let` | let の折り畳み | 展開済みの式を let 名に戻すなら `refold_let` |
| `intro` | 束縛変数の導入 | ∀/→ の導入。let 束縛には `extract_lets` |

---

## 参照

- [Mathlib4 ドキュメント — ExtractLets](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/ExtractLets.html)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
