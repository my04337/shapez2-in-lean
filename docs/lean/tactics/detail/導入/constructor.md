# `constructor` — 帰納型のコンストラクタ適用

**カテゴリ**: 導入 | **定義元**: `Lean.Parser.Tactic.constructor` | **ソース**: Lean4 core

---

## 概要

`constructor` は、ゴールが帰納型の場合に最初のマッチするコンストラクタを適用する。典型的には `∧`（`And.intro`）や `∃`（`Exists.intro`）のゴールを分解するのに使う。`∧` の場合はゴールが 2 つに分かれ、`∃` の場合はウィットネスとプロパティの 2 つのサブゴールが生成される。

---

## ゴールパターン

**適用前**（論理積）
```lean
⊢ P ∧ Q
```

**適用後** (`constructor`)
```lean
-- ゴール 1: ⊢ P
-- ゴール 2: ⊢ Q
```

**適用前**（存在）
```lean
⊢ ∃ n : Nat, n = 0
```

**適用後** (`constructor`)
```lean
-- ゴール 1: ⊢ Nat          （ウィットネス）
-- ゴール 2: ⊢ ?w = 0       （プロパティ）
```

---

## 構文

```lean
constructor            -- 最初のコンストラクタを適用
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 説明 |
|---|---|
| `constructor` | 引数なし。最初にマッチするコンストラクタを適用 |

---

## Pros（使うべき場面）

- `∧` のゴールを左右に分割する最も簡潔な方法
- コンストラクタ名を覚えていなくても使える
- `Prod.mk`、`And.intro`、`Exists.intro` 等に汎用的に対応

---

## Cons（注意・失敗ケース）

- `∃` に使うとメタ変数が残り `exact` で値を埋める必要がある（`use` の方が楽）
- コンストラクタが複数ある型（`∨` 等）では最初のコンストラクタ（`Or.inl`）が選ばれる
- どのコンストラクタが適用されるか不明瞭な場合は `left` / `right` / `use` を明示する方がよい

---

## コードサンプル

### サンプル 1: 論理積の証明
```lean
example (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  -- ゴール 1: ⊢ P
  · exact hp
  -- ゴール 2: ⊢ Q
  · exact hq
```

### サンプル 2: 存在量化子の証明
```lean
example : ∃ n : Nat, n + 1 = 3 := by
  constructor
  -- ⊢ ?n + 1 = 3（n はメタ変数として残る）
  show 2 + 1 = 3  -- ?n := 2 に確定
  rfl
```

### サンプル 3: Prod の構成
```lean
example : Nat × String := by
  constructor
  -- ゴール 1: ⊢ Nat
  · exact 42
  -- ゴール 2: ⊢ String
  · exact "hello"
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `left` | Or 専用 | `∨` の左側を証明したい場合 |
| `right` | Or 専用 | `∨` の右側を証明したい場合 |
| `use` | ∃ 専用 | ウィットネスを直接指定して `∃` を証明 |
| `exact ⟨a, b⟩` | Term モード | 匿名コンストラクタで直接構成 |
| `And.intro` | 明示的 | `constructor` の代わりに名前で適用 |

---

## 参照
- [Lean4 公式リファレンス — constructor](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#constructor)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
