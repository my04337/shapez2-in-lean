# `econstructor` — メタ変数を後回しにして constructor を適用する

**カテゴリ**: 導入 | **定義元**: `Mathlib.Tactic.econstructor` | **ソース**: Mathlib

---

## 概要

`econstructor` は `constructor` と同様に帰納型のコンストラクタを適用するが、引数をメタ変数として後回しにしてサブゴールを生成する。`∃ x, P x` のように witness を先に決めたくない場合に有用。`constructor` が即座に引数を要求するのに対し、`econstructor` は後から統一（unification）で決定させる。

---

## ゴールパターン

**適用前**
```lean
⊢ ∃ n : Nat, n = 1
```

**適用後**
```lean
⊢ ?n = 1
```

（後から `?n` がメタ変数統一で `1` に決定される）

---

## 構文

```lean
econstructor
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

- witness を先に決めず、後のタクティクで統一させたい場合
- `constructor` では too eager に引数を要求される場合の代替
- `eapply` の constructor 版

---

## Cons（注意・失敗ケース）

- メタ変数が解決されないまま残ると証明が完了しない
- `use` で witness を明示する方が明確なことが多い
- Mathlib import が必要

---

## コードサンプル

### サンプル 1: 存在量化の証明

```lean
import Mathlib.Tactic.Core

example : ∃ n : Nat, n = 1 := by
  econstructor
  -- ⊢ ?n = 1
  rfl
  -- rfl が ?n を 1 に統一する
```

### サンプル 2: And の証明

```lean
import Mathlib.Tactic.Core

example : True ∧ True := by
  econstructor <;> trivial
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `constructor` | 標準版 | 引数を即座に決定するなら `constructor` |
| `fconstructor` | 順序固定版 | サブゴール順序を固定するなら `fconstructor` |
| `use` | witness 明示 | witness を明示的に指定するなら `use` |
| `eapply` | メタ変数後回し | 一般的な apply のメタ変数後回し版 |

---

## 参照

- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
