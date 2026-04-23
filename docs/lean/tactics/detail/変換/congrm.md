# `congrm` — パターンを指定して合同性分解する

**カテゴリ**: 変換 | **定義元**: `Mathlib.Tactic.Congrm.congrm` | **ソース**: Mathlib

---

## 概要

`congrm` は等式ゴール `⊢ f a₁ ... = f b₁ ...` に対し、ユーザ指定のパターンで一致する部位を固定し、差異がある `?_` の箇所のみをサブゴールとして残す Mathlib タクティクである。`congr` が自動で深さを決めるのに対し、`congrm` はパターンで制御できるため、複雑な式でもピンポイントで合同分解が可能。

---

## ゴールパターン

**適用前**
```lean
⊢ f (g a) (h b) = f (g a') (h b)
```

**`congrm f (g ?_) (h b)` 適用後**
```lean
⊢ a = a'
```

---

## 構文

```lean
congrm pattern
```

- `pattern`: 両辺の共通構造を記述し、差異の箇所を `?_` で示す

---

## 必須 import

```lean
import Mathlib.Tactic.Congrm
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `congrm pat` | パターン `pat` に従って合同性を適用し `?_` をサブゴール化 |

---

## Pros（使うべき場面）

- 式が複雑でどの部分を分解するか明示したい場合に最適
- `congr n` の深さ指定では制御しきれないネスト構造に対応
- パターンで意図を明示できるため証明の可読性が高い

---

## Cons（注意・失敗ケース）

- パターンが両辺にマッチしない場合は失敗する
- Mathlib import が必要（Lean4 core にはない）
- 単純な合同分解には `congr` の方が簡潔

---

## コードサンプル

### サンプル 1: 基本的なパターン指定

```lean
import Mathlib.Tactic.Congrm

example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  -- ⊢ a + 1 = b + 1
  congrm ?_ + 1
  -- ⊢ a = b
  exact h
```

### サンプル 2: ネストした式での使用

```lean
import Mathlib.Tactic.Congrm

example (f : Nat → Nat) (a b : Nat) (h : a = b) : f a + 0 = f b + 0 := by
  congrm f ?_ + 0
  exact h
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `congr` | 基本版 | 自動深さで合同分解するなら `congr` |
| `rcongr` | 再帰版 | バインダ内部に入り再帰的に分解するなら `rcongr` |
| `convert` | 柔軟な変換 | 関数自体が異なる場合は `convert` |

---

## 参照

- [Mathlib4 ドキュメント — congrm](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Congrm.html)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
