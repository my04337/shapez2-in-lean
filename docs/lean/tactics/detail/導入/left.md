# `left` — 論理和の左側を選択

**カテゴリ**: 導入 | **定義元**: `Lean.Parser.Tactic.left` | **ソース**: Lean4 core

---

## 概要

`left` は、ゴールが `A ∨ B` のとき、最初のコンストラクタ `Or.inl` を適用して `A` の証明に帰着する。「左側が正しい」と宣言するタクティクであり、残りのゴールは `⊢ A` になる。`constructor` と異なり、`∨` の場合にどちら側を選ぶかが明示的になる。

---

## ゴールパターン

**適用前**
```lean
⊢ P ∨ Q
```

**適用後** (`left`)
```lean
⊢ P
```

---

## 構文

```lean
left                   -- Or.inl を適用
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 説明 |
|---|---|
| `left` | 引数なし。`Or.inl` を適用 |

---

## Pros（使うべき場面）

- `∨` のゴールでどちらを証明するか明示できる
- `constructor` よりも意図が明確で可読性が高い
- `Or.inl` を覚えていなくても使える

---

## Cons（注意・失敗ケース）

- ゴールが `∨` の形でないと失敗する
- 左側が証明できない場合は `right` に切り替える必要がある
- 3 つ以上の選択肢（`A ∨ B ∨ C`）では `left` で `A` だけ、`right` で `B ∨ C` に進むため、入れ子になることがある

---

## コードサンプル

### サンプル 1: 基本的な左選択
```lean
example : 1 = 1 ∨ 1 = 2 := by
  left
  -- ⊢ 1 = 1
  rfl
```

### サンプル 2: 仮定を使った選択
```lean
example (hp : P) : P ∨ Q := by
  left
  -- ⊢ P
  exact hp
```

### サンプル 3: 入れ子の論理和
```lean
example : 1 = 1 ∨ 1 = 2 ∨ 1 = 3 := by
  left
  -- ⊢ 1 = 1
  rfl
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `right` | 対 | `∨` の右側を証明する場合 |
| `constructor` | 汎用 | 最初のコンストラクタを自動選択（`∨` では `left` と同じ） |
| `Or.inl` | Term モード | タクティクモード外での直接適用 |
| `decide` | 自動判定 | 決定可能な命題の場合 |

---

## 参照
- [Lean4 公式リファレンス — left](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#left-right)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
