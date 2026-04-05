# `map_tacs` — 各ゴールに対応するタクティクをマッピングする

**カテゴリ**: 制御 | **定義元**: `Mathlib.Tactic.mapTacs` | **ソース**: Mathlib

---

## 概要

`map_tacs [tac₁, tac₂, ...]` は各ゴールに対応するタクティクを順番に適用する。1 番目のゴールに `tac₁`、2 番目に `tac₂` のように対応付ける。`<;>` が全ゴールに同じタクティクを適用するのに対し、`map_tacs` は各ゴールに異なるタクティクを適用できる。

---

## ゴールパターン

**適用前**
```lean
-- ゴール 1: ⊢ A
-- ゴール 2: ⊢ B
```

**適用後**（`map_tacs [tac₁, tac₂]`）: 各ゴールに対応するタクティクが適用される

---

## 構文

```lean
map_tacs [tac₁, tac₂, tac₃]
```

---

## 必須 import

```lean
import Mathlib.Tactic.Core
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `map_tacs [tac₁, tac₂]` | 各ゴールに順番にタクティクを適用 |

---

## Pros（使うべき場面）

- 各ゴールに異なるタクティクを 1 行で適用
- `<;>` では対応できない場合の代替

---

## Cons（注意・失敗ケース）

- タクティク数とゴール数が一致しないと失敗する
- Mathlib import が必要
- `case` や `·` の方が可読性が高いことが多い

---

## コードサンプル

### サンプル 1: 基本的な使い方

```lean
import Mathlib.Tactic.Core

example : True ∧ (1 = 1) := by
  constructor
  map_tacs [trivial, rfl]
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `<;>` | 全ゴール同一 | 全ゴールに同じタクティクを適用するなら `<;>` |
| `all_goals` | 全ゴール同一 | ブロック構文で同じタクティクを適用 |
| `case` | 名前指定 | 名前でゴールを選択するなら `case` |

---

## 参照

- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
