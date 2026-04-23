# `fconstructor` — サブゴール順序を固定して constructor を適用する

**カテゴリ**: 導入 | **定義元**: `Mathlib.Tactic.fconstructor` | **ソース**: Mathlib

---

## 概要

`fconstructor` は `constructor` と同様にコンストラクタを適用するが、サブゴールの順序を依存関係順ではなくフィールド定義順に固定する。`constructor` は Lean のヒューリスティクスでサブゴール順を並替えることがあるが、`fconstructor` は常にフィールド順を保つ。

---

## ゴールパターン

**適用前**
```lean
⊢ ∃ n : Nat, n > 0
```

**適用後**
```lean
-- サブゴール 1: witness
⊢ Nat
-- サブゴール 2: 性質
⊢ ?n > 0
```

---

## 構文

```lean
fconstructor
```

---

## 必須 import

```lean
import Mathlib.Tactic.Core
```

---

## オプション一覧

特になし。

---

## Pros（使うべき場面）

- サブゴール順序を明確にしたい場合
- `constructor` の順序変更により証明が壊れる場合の代替
- 構造体のフィールドを定義順に埋めたい場合

---

## Cons（注意・失敗ケース）

- `constructor` で十分な場合はオーバーキル
- 依存関係により先に witness が必要な場合がある
- Mathlib import が必要

---

## コードサンプル

### サンプル 1: 存在量化

```lean
import Mathlib.Tactic.Core

example : ∃ n : Nat, n = 1 := by
  fconstructor
  · exact 1
  · rfl
```

### サンプル 2: And の証明

```lean
import Mathlib.Tactic.Core

example : True ∧ (1 = 1) := by
  fconstructor
  · trivial
  · rfl
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `constructor` | 標準版 | 通常はこちらで十分 |
| `econstructor` | メタ変数後回し | 引数を後で決定するなら |
| `use` | witness 明示 | 存在証明で witness を直接指定 |

---

## 参照

- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
