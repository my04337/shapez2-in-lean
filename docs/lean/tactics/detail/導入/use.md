# `use` — 存在量化子のウィットネス提供

**カテゴリ**: 導入 | **定義元**: `Mathlib.Tactic.useSyntax` | **ソース**: Mathlib

---

## 概要

`use` は、ゴールが `∃ x, P x` や `Σ x, P x` のような存在型の場合に、具体的なウィットネス（証拠の値）を提供する。`constructor` + `exact` の組み合わせを 1 行で書ける。複数の値をカンマ区切りで渡すことで、入れ子の `∃` にも対応する。ウィットネス提供後、残りのゴールに対して自動的に `try trivial` が試行される。

---

## ゴールパターン

**適用前**
```lean
⊢ ∃ n : Nat, n + 1 = 3
```

**適用後** (`use 2`)
```lean
⊢ 2 + 1 = 3
```

**適用前**（入れ子の ∃）
```lean
⊢ ∃ n m : Nat, n + m = 5
```

**適用後** (`use 2, 3`)
```lean
⊢ 2 + 3 = 5
```

---

## 構文

```lean
use e                  -- ウィットネス e を提供
use e₁, e₂            -- 複数の値を順に提供
use e₁, e₂, e₃        -- 3 つ以上も可
```

---

## 必須 import

```lean
import Mathlib.Tactic.Use
```

---

## オプション一覧

| 構文 | 説明 |
|---|---|
| `use e` | 単一のウィットネスを提供 |
| `use e₁, e₂` | 入れ子の ∃ に対して順にウィットネスを提供 |

---

## Pros（使うべき場面）

- `∃` の証明で最も自然で簡潔な方法
- `constructor` + `exact` の 2 行を 1 行に圧縮できる
- 残りが自明なら `try trivial` で自動閉じされる

---

## Cons（注意・失敗ケース）

- Mathlib の import が必要（Lean4 core には含まれない）
- ウィットネスの型が合わないとエラーになる
- `try trivial` で閉じない場合は追加の証明が必要

---

## コードサンプル

### サンプル 1: 基本的な存在量化子
```lean
example : ∃ n : Nat, n * 2 = 10 := by
  use 5
  -- ⊢ 5 * 2 = 10  （trivial で自動閉じ、または rfl）
```

### サンプル 2: 複数ウィットネス
```lean
example : ∃ a b : Nat, a + b = 7 := by
  use 3, 4
  -- ⊢ 3 + 4 = 7  （自動で閉じる）
```

### サンプル 3: 残りの証明が必要なケース
```lean
example : ∃ n : Nat, n > 0 ∧ n < 10 := by
  use 5
  -- ⊢ 5 > 0 ∧ 5 < 10
  constructor
  · norm_num
  · norm_num
```

---

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `use!` | 再帰的にコンストラクタを適用する強化版 |
| `use_discharger` | `use` 内部のディスチャージャをカスタマイズ |

## 関連タクティク
| `constructor` | 汎用 | ∃ にも使えるがメタ変数が残る |
| `refine ⟨_, _⟩` | Term モード混合 | 一部を `_` で残して後で埋める |
| `obtain` | 逆操作 | ∃ の仮定を分解する場合 |

---

## 参照
- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント — use](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Use.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
