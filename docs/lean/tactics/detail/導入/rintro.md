# `rintro` — パターンマッチ付き導入

**カテゴリ**: 導入 | **定義元**: `Lean.Parser.Tactic.rintro` | **ソース**: Mathlib

---

## 概要

`rintro` は `intro` と `rcases` を合成したタクティクで、`∀` / `→` の導入と同時にパターンマッチを行う。存在量化子 `∃`、論理積 `∧`、論理和 `∨`、入れ子構造などを一度に分解できる。`intro` + `rcases` の 2 段階を 1 行で書けるため、証明が簡潔になる。

---

## ゴールパターン

**適用前**
```lean
⊢ (∃ n : Nat, n = 0 ∧ n < 1) → True
```

**適用後** (`rintro ⟨n, rfl, hn⟩`)
```lean
hn : 0 < 1
⊢ True
```

**適用前**（論理和の分解）
```lean
⊢ (P ∨ Q) → R
```

**適用後** (`rintro (hp | hq)`)
```lean
-- ゴール 1: hp : P ⊢ R
-- ゴール 2: hq : Q ⊢ R
```

---

## 構文

```lean
rintro x                    -- 単純な導入（intro と同等）
rintro ⟨a, b⟩               -- ∧ / ∃ / 構造体の分解
rintro ⟨a, b, c⟩            -- 入れ子の分解
rintro (h | h)               -- ∨ の場合分け
rintro ⟨a, rfl⟩             -- 等式を即座に代入（rfl パターン）
rintro ⟨⟨a, b⟩, c | d⟩     -- 入れ子パターン
rintro _                     -- ワイルドカード
```

---

## 必須 import

```lean
import Mathlib.Tactic.RCases
```

---

## オプション一覧

| パターン | 説明 |
|---|---|
| `⟨a, b⟩` | 匿名コンストラクタで分解（∧, ∃, Prod 等） |
| `(h₁ \| h₂)` | 論理和 `∨` の場合分け |
| `rfl` | 等式仮定を即座に代入して消去 |
| `_` | 仮定を導入するが名前を付けない |
| `⟨⟩` | 空パターン（False の消去等） |

---

## Pros（使うべき場面）

- `∃ x, P x ∧ Q x` のような複合仮定を 1 行で分解できる
- `rfl` パターンにより等式を即座に消去できる
- `intro` + `rcases` の 2 ステップを 1 ステップに圧縮

---

## Cons（注意・失敗ケース）

- パターンの入れ子が深いと可読性が下がる
- Mathlib の import が必要（Lean4 core のみでは使えない）
- パターンが実際のゴール構造と一致しないとエラーになる

---

## コードサンプル

### サンプル 1: 存在量化子と論理積の分解
```lean
example : (∃ n : Nat, n = 0 ∧ 0 < 1) → 0 < 1 := by
  rintro ⟨n, _hn_eq, hn_lt⟩
  -- n : Nat
  -- _hn_eq : n = 0
  -- hn_lt : 0 < 1
  -- ⊢ 0 < 1
  exact hn_lt
```

### サンプル 2: rfl パターンで即時代入
```lean
example : (∃ n : Nat, n = 5) → ∃ m : Nat, m = 5 := by
  rintro ⟨n, rfl⟩
  -- ⊢ ∃ m, m = 5  （n が 5 に代入された）
  exact ⟨5, rfl⟩
```

### サンプル 3: 論理和の場合分け
```lean
example (P Q R : Prop) (hpr : P → R) (hqr : Q → R) : P ∨ Q → R := by
  rintro (hp | hq)
  -- ゴール 1: hp : P ⊢ R
  · exact hpr hp
  -- ゴール 2: hq : Q ⊢ R
  · exact hqr hq
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `intro` | 基本形 | パターンマッチ不要な単純な導入 |
| `rcases` | 分解のみ | 既にコンテキストにある仮定を分解 |
| `obtain` | 類似 | `rcases` + 型注釈付きの仮定導入 |
| `match` | Term モード | タクティクモード外でのパターンマッチ |

---

## 参照
- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント — rintro](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/RCases.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
