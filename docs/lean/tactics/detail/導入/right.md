# `right` — 論理和の右側を選択

**カテゴリ**: 導入 | **定義元**: `Lean.Parser.Tactic.right` | **ソース**: Lean4 core

---

## 概要

`right` は、ゴールが `A ∨ B` のとき、2 番目のコンストラクタ `Or.inr` を適用して `B` の証明に帰着する。`left` と対になるタクティクで、「右側が正しい」と宣言する。`∨` のゴールでどちらを選ぶかを明示的にコードに表せるため、可読性が高い。

---

## ゴールパターン

**適用前**
```lean
⊢ P ∨ Q
```

**適用後** (`right`)
```lean
⊢ Q
```

---

## 構文

```lean
right                  -- Or.inr を適用
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 説明 |
|---|---|
| `right` | 引数なし。`Or.inr` を適用 |

---

## Pros（使うべき場面）

- `∨` のゴールで右側を証明したいと明示できる
- `left` と組み合わせて意図を明確に表現
- コンストラクタ名 `Or.inr` を覚えていなくても使える

---

## Cons（注意・失敗ケース）

- ゴールが `∨` の形でないと失敗する
- 右側が証明できない場合は `left` に切り替える必要がある
- `A ∨ B ∨ C` で `B` だけを証明したい場合、`right; left` と入れ子にする必要がある

---

## コードサンプル

### サンプル 1: 基本的な右選択
```lean
example : 1 = 2 ∨ 2 = 2 := by
  right
  -- ⊢ 2 = 2
  rfl
```

### サンプル 2: 仮定を使った選択
```lean
example (hq : Q) : P ∨ Q := by
  right
  -- ⊢ Q
  exact hq
```

### サンプル 3: 入れ子の論理和で中央を選択
```lean
example : 1 = 2 ∨ 3 = 3 ∨ 1 = 4 := by
  right
  -- ⊢ 3 = 3 ∨ 1 = 4
  left
  -- ⊢ 3 = 3
  rfl
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `left` | 対 | `∨` の左側を証明する場合 |
| `constructor` | 汎用 | 最初のコンストラクタを自動選択 |
| `Or.inr` | Term モード | タクティクモード外での直接適用 |
| `decide` | 自動判定 | 決定可能な命題の場合 |

---

## 参照
- [Lean4 公式リファレンス — right](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#left-right)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
