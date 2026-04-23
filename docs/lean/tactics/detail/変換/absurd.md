# `absurd` — 矛盾する命題からゴールを導出

**カテゴリ**: 変換 | **定義元**: `Batteries.Tactic.tacticAbsurd_` | **ソース**: Batteries

---

## 概要

`absurd h` は仮定 `h : P` がある場合にゴールを `⊢ ¬P` に変換するタクティクである。
つまり「`P` が成り立つが、`¬P` も示せるなら矛盾により何でも示せる」という推論を行う。
Lean4 core の `absurd` 関数（`h : P → h' : ¬P → α`）をタクティクとして使えるようにした Batteries 版。
ゴールが `False` でない場合にも使用でき、任意のゴールから矛盾を導出できる。

---

## ゴールパターン

**適用対象**: 任意のゴール（矛盾を導出可能な場合）

**適用前**
```lean
h : P
⊢ Q
```

**適用後** (`absurd h`)
```lean
⊢ ¬P
```

---

## 構文

```lean
absurd h          -- h : P を与え、ゴールを ¬P に変更
```

---

## 必須 import

```lean
import Batteries.Tactic.Basic   -- Batteries の absurd タクティク
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `absurd h` | `h : P` を与え、ゴールを `¬P` に変換 |

---

## Pros（使うべき場面）

- ゴールが `False` でなくても矛盾を利用した証明ができる
- `have` + `exact absurd` の組み合わせよりも簡潔
- 不可能なケースの処理で直感的に記述できる

---

## Cons（注意・失敗ケース）

- `¬P` を示す手段がない場合、変換後のゴールが閉じられない
- 既に `h₁ : P` と `h₂ : ¬P` が両方ある場合は `contradiction` の方が簡潔
- Batteries の import が必要

---

## コードサンプル

### サンプル 1: 基本的な使用

```lean
import Batteries.Tactic.Basic

example (h : 0 = 1) : False := by
  -- h : 0 = 1
  -- ⊢ False
  absurd h
  -- ⊢ ¬0 = 1
  omega
```

### サンプル 2: 任意のゴールからの矛盾導出

```lean
import Batteries.Tactic.Basic

example (n : Nat) (h : n < 0) : n = 42 := by
  -- h : n < 0
  -- ⊢ n = 42
  absurd h
  -- ⊢ ¬n < 0
  omega
```

### サンプル 3: 否定仮定との組み合わせ

```lean
import Batteries.Tactic.Basic

example (P Q : Prop) (hp : P) (hnp : ¬P) : Q := by
  -- hp : P, hnp : ¬P
  -- ⊢ Q
  absurd hp
  -- ⊢ ¬P
  exact hnp
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `contradiction` | 自動検出 | 仮定中の矛盾を自動で検出して閉じる |
| `exfalso` | False 化 | ゴールを `False` に変換。`absurd` は特定の仮定を指定 |
| `omega` | 算術矛盾 | 算術的な矛盾は `omega` で直接閉じられることが多い |
| `simp` | 簡約 | 矛盾する等式を `simp` で `False` に簡約できる場合がある |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
