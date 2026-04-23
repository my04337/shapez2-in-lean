# `rsuffices` — obtain 記法で十分条件に帰着する

**カテゴリ**: 変換 | **定義元**: `Mathlib.Tactic.RSuffices.rsuffices` | **ソース**: Mathlib

---

## 概要

`rsuffices` は `suffices` の逆順版で、`obtain` のパターン構文を使って十分条件に帰着する。`suffices` + `rcases` を組み合わせた糖衣構文であり、最初に証明すべきサブゴールと、その結果を受けて元のゴールを閉じるブロックの順序が `obtain` 形式になる。

---

## ゴールパターン

**適用前**
```lean
⊢ P
```

**適用後**（`rsuffices ⟨a, b⟩ : A ∧ B`）
```lean
-- ゴール 1: A ∧ B を証明
⊢ A ∧ B
-- ゴール 2（a, b を使って P を証明）
a : A
b : B
⊢ P
```

---

## 構文

```lean
rsuffices h : Q
rsuffices ⟨a, b⟩ : A ∧ B
rsuffices (h : Q) | (h : R)
```

---

## 必須 import

```lean
import Mathlib.Tactic.RSuffices
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `rsuffices h : Q` | `Q` を示すサブゴールと `h : Q ⊢ P` のサブゴールを生成 |
| `rsuffices ⟨a, b⟩ : A ∧ B` | パターンで分解しつつ帰着 |

---

## Pros（使うべき場面）

- `suffices` + `rcases` を 1 行にまとめられ簡潔
- パターンマッチで構造的な分解と帰着を同時に行える
- `obtain` に慣れたユーザにとって直感的なサブゴール順序

---

## Cons（注意・失敗ケース）

- Mathlib import が必要
- `suffices` で十分な場合はオーバーキル
- サブゴール順序が `suffices` と逆なので注意

---

## コードサンプル

### サンプル 1: 基本的な帰着

```lean
import Mathlib.Tactic.RSuffices

-- rsuffices はパターン分解（obtain スタイル）で使用する
example (h : True ∧ (1 = 1)) : 1 = 1 := by
  rsuffices ⟨_, h₂⟩ : True ∧ 1 = 1
  · exact h₂   -- ゴール 1: h₂ : 1 = 1 ⊢ 1 = 1
  · exact h    -- ゴール 2: ⊢ True ∧ 1 = 1
```

### サンプル 2: 存在量化と分解

```lean
import Mathlib.Tactic.RSuffices

example : ∃ n : Nat, n = 1 := by
  rsuffices ⟨n, hn⟩ : ∃ n : Nat, n = 1
  · exact ⟨n, hn⟩   -- 分解した n, hn を使って結論を組み立て
  · exact ⟨1, rfl⟩  -- 十分条件 ∃ n, n = 1 を証明
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `suffices` | 基本版 | パターン分解不要なら `suffices` |
| `obtain` | 存在の分解 | 仮定を分解するなら `obtain`、帰着なら `rsuffices` |
| `have` | 補題導入 | 中間結果を導入するだけなら `have` |

---

## 参照

- [Mathlib4 ドキュメント — RSuffices](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/RSuffices.html)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
