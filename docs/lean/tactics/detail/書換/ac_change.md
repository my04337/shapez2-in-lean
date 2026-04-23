# `ac_change` — 結合律・交換律を考慮したゴール変更

**カテゴリ**: 書換 | **定義元**: `Mathlib.Tactic.acChange` | **ソース**: Mathlib

## 概要
`ac_change` はゴールを新しい形に変更する `change` の拡張版。通常の `change` が definitional equality を要求するのに対し、`ac_change` は結合律（associativity）と交換律（commutativity）を考慮して等価性を判定する。可換な演算の項の並び替えを透過的に行える。

## ゴールパターン

**適用前**
```lean
⊢ a + b + c = d
```

**適用後**（`ac_change c + a + b = d`）
```lean
-- + の結合律・交換律により等価と判定
⊢ c + a + b = d
```

## 構文
```lean
ac_change newGoal           -- ゴールを AC 同値な形に変更
ac_change newGoal using n   -- ゴール数 n を指定（デフォルト 1）
```

## 必須 import
```lean
import Mathlib.Tactic.ACRefl
```

## オプション一覧
| 構文 | 意味 |
|---|---|
| `newGoal` | AC 同値な新しいゴール式 |
| `using n` | 生成するサブゴールの数（デフォルト 1） |

## Pros
- 可換演算の項の並び替えを自然に行える
- `ring_nf` や `abel` を使わずに式を整理できる
- `change` では通らない並べ替えに対応

## Cons
- AC 同値性が成り立たない変更には使えない
- `ring` や `omega` で一発で閉じる場合は冗長
- Mathlib import が必要
- `ac_rfl` で閉じるほど単純な場合は `ac_rfl` を直接使う方が良い

## コードサンプル

### サンプル 1: 加法の交換
```lean
import Mathlib.Tactic.ACRefl

example (a b c : Nat) (h : b + a = c) : a + b = c := by
  ac_change b + a = c
  -- ⊢ b + a = c  （+ の交換律で元のゴールと AC 同値）
  exact h
```

### サンプル 2: 結合律と交換律の組み合わせ
```lean
import Mathlib.Tactic.ACRefl

example (a b c d : Nat) (h : c + (a + b) = d) : a + b + c = d := by
  ac_change c + (a + b) = d
  -- 結合律と交換律で並べ替え
  exact h
```

### サンプル 3: 乗法での使用
```lean
import Mathlib.Tactic.ACRefl

example [CommMonoid α] (a b c d : α) (h : c * a * b = d) :
    a * b * c = d := by
  ac_change c * a * b = d
  -- * の AC 同値性で変換
  exact h
```

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `change` | 定義同値 | definitional equality で済む場合 |
| `ac_rfl` | AC 反射律 | ゴールが `a = b` で AC 同値なら即閉じる |
| `ring` | 環の等式 | 環構造上の等式を自動証明 |
| `abel` | アーベル群 | 加法群の等式を自動証明 |
| `conv` | 位置指定 | 特定位置の式だけ並べ替えたい場合 |

## 参照
- [Mathlib4 ドキュメント — ac_change](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/ACRefl.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
