# `transitivity` — 推移律の中間項を挿入する

**カテゴリ**: 変換 | **定義元**: `Mathlib.Tactic.tacticTransitivity__` | **ソース**: Mathlib

---

## 概要

`transitivity e` はゴール `⊢ a R b`（`R` が推移的関係）を `⊢ a R e` と `⊢ e R b` の 2 つのサブゴールに分割する。Lean4 core の `trans` とほぼ同等だが、Mathlib 版は中間項を明示的に指定できる。等式だけでなく `≤`、`<` 等の推移的関係にも使える。

---

## ゴールパターン

**適用前**
```lean
⊢ a ≤ c
```

**適用後**（`transitivity b`）
```lean
⊢ a ≤ b
⊢ b ≤ c
```

---

## 構文

```lean
transitivity
transitivity e
```

- `e` を省略すると中間項がメタ変数になる

---

## 必須 import

```lean
import Mathlib.Tactic.Relation.Trans
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `transitivity` | 中間項をメタ変数で生成 |
| `transitivity e` | 中間項を `e` に指定 |

---

## Pros（使うべき場面）

- `calc` よりも軽量に推移律を 1 ステップだけ適用したい場合
- `≤` や `<` 等の順序関係での段階証明
- `trans` の代替として使える

---

## Cons（注意・失敗ケース）

- 2 ステップ以上の推移律は `calc` の方が可読性が高い
- 中間項を省略するとメタ変数が残り後続で混乱する場合がある
- Lean4 core の `trans` でほぼ同等の機能がある

---

## コードサンプル

### サンプル 1: 不等式の推移律

```lean
import Mathlib.Tactic.Relation.Trans

example (a b c : Nat) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  transitivity b
  · exact h₁
  · exact h₂
```

### サンプル 2: 等式の推移律

```lean
import Mathlib.Tactic.Relation.Trans

example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  transitivity b
  · exact h₁
  · exact h₂
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `trans` | Lean4 core 版 | core のみで済む場合は `trans` |
| `calc` | 段階証明 | 多段階の推移律は `calc` が可読性高い |
| `linarith` | 算術推移 | 線形算術の場合は `linarith` が自動的に推移律を使う |

---

## 参照

- [Mathlib4 ドキュメント — Trans](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Relation/Trans.html)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
