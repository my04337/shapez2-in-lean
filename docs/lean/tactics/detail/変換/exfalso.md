# `exfalso` — ゴールを `False` に変換する

**カテゴリ**: 変換 | **定義元**: `Lean.Parser.Tactic.tacticExfalso` | **ソース**: Lean4 core

---

## 概要

`exfalso` は現在のゴールの型を任意の `P` から `False` に変換するタクティクである。
`False.elim` を適用することに相当し、矛盾を導くことでどんな命題でも証明できるという論理的原理に基づく。
仮定同士が矛盾している場合に、ゴールの型に関係なく矛盾から証明する出発点として使う。

---

## ゴールパターン

**適用前**
```lean
⊢ P
```

**適用後**
```lean
⊢ False
```

---

## 構文

```lean
exfalso
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

特になし。`exfalso` は引数を取らない単一構文である。

---

## Pros（使うべき場面）

- 仮定に矛盾があることが明らかなとき、ゴールの型を気にせず矛盾の導出に集中できる
- `by_contra` と異なり否定仮定を追加しないため、既に矛盾が仮定にある場合にシンプル
- `contradiction` が自動検出できない複雑な矛盾を手動で導く場合の第一歩として使える

---

## Cons（注意・失敗ケース）

- 仮定に矛盾がない場合、ゴールが `False` になるため証明不能になる
- `contradiction` で自動的に矛盾を検出できる場合は `exfalso` は不要
- `by_contra` の方が否定仮定を得られるため一般的に強力

---

## コードサンプル

### サンプル 1: 仮定の矛盾から証明

```lean
example (h1 : n > 0) (h2 : n = 0) : n * n = 42 := by
  -- ⊢ n * n = 42
  exfalso
  -- ⊢ False
  omega
```

### サンプル 2: 空リストの不可能ケース

```lean
example (h : [] = [1, 2, 3]) : False := by
  -- ⊢ False（既に False なので exfalso 不要だが例示のため）
  exact absurd h (by simp)
```

### サンプル 3: match でのあり得ないケース

```lean
example (b : Bool) (h1 : b = true) (h2 : b = false) : 0 = 1 := by
  -- ⊢ 0 = 1
  exfalso
  -- ⊢ False
  rw [h1] at h2
  exact absurd h2 (by decide)
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `contradiction` | 自動版 | 仮定の矛盾を自動検出して `False` を導く。検出可能なら `contradiction` が簡潔 |
| `by_contra` | 拡張版 | ゴールを `False` にし、さらに否定仮定 `¬P` を追加する |
| `absurd` | 類似 | `absurd h1 h2` で `h1 : P` と `h2 : ¬P` から `False` を導く項 |
| `nomatch` | 項レベル | パターンマッチで空ケースを処理する（タクティクではなく項） |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
