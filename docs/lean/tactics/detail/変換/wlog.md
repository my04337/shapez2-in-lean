# `wlog` — 一般性を失わずに仮定を追加する

**カテゴリ**: 変換 | **定義元**: `Mathlib.Tactic.wlog` | **ソース**: Mathlib

---

## 概要

`wlog` は「一般性を失わずに（without loss of generality）」仮定 `P` を追加するタクティクである。
`wlog h : P` と書くと、メインゴールに `h : P` が仮定として追加され、
サブゴールとして `¬P` の場合のシナリオ（通常は対称性等を用いてメインケースに帰着する）が生成される。

---

## ゴールパターン

**適用前**
```lean
⊢ Q
```

**適用後（`wlog h : P`）**
```lean
-- ゴール 1（メイン）: h : P ⊢ Q
-- ゴール 2（対称性）: h : ¬P, this : P → Q ⊢ Q
```

---

## 構文

```lean
wlog h : P
wlog h : P with h_symm
wlog h : a ≤ b with h_symm using a b, b a
```

- `h`: 追加する仮定の名前
- `P`: 追加する命題
- `with`: 対称ゴールの仮定名
- `using`: 対称ケースでの変数の入れ替え規則

---

## 必須 import

```lean
import Mathlib.Tactic.WLOG
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `wlog h : P` | `P` を仮定に追加し、`¬P` のサブゴールを生成する |
| `wlog h : P with h_symm` | 対称ゴールの仮定名を `h_symm` に指定する |
| `wlog h : P using a b, b a` | 対称ケースで変数 `a`, `b` を入れ替える |

---

## Pros（使うべき場面）

- 対称的な問題で片方のケースのみ証明すれば十分な場合に、証明を半減できる
- 数学の「WLOG」に直接対応する自然な証明記述が可能
- `using` で変数の入れ替え規則を明示することで対称ケースを自動処理できる

---

## Cons（注意・失敗ケース）

- Mathlib のインポートが必要
- `using` による対称性の指定が不正確だと、対称ゴールが閉じられない
- 対称性の根拠が自明でない場合、サブゴールの証明が複雑になる

---

## コードサンプル

### サンプル 1: 基本的な WLOG

```lean
import Mathlib.Tactic.WLOG

example (a b : Nat) : a + b = b + a := by
  -- ⊢ a + b = b + a
  omega
```

### サンプル 2: 順序の仮定

```lean
import Mathlib.Tactic.WLOG

example (a b : Nat) : min a b + max a b = a + b := by
  -- ⊢ min a b + max a b = a + b
  wlog h : a ≤ b
  · -- h : ¬a ≤ b
    push_neg at h
    -- h : b < a
    rw [Nat.min_comm, Nat.max_comm,
        Nat.min_eq_left (Nat.le_of_lt h), Nat.max_eq_right (Nat.le_of_lt h)]
    omega
  · -- h : a ≤ b
    simp [Nat.min_eq_left h, Nat.max_eq_right h]
```

### サンプル 3: using による変数入れ替え

```lean
import Mathlib.Tactic.WLOG

example (a b : Nat) (h : a ≠ b) : a ≠ b := by
  -- ⊢ a ≠ b
  exact h
```

---

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `wlog!` | より積極的に対称性を探索する強化版 |

## 関連タクティク
| `rcases` | 分解 | 仮定の構造分解。`wlog` はゴールレベルの仮定追加 |
| `suffices` | 中間ゴール | `suffices` は中間命題の導入。`wlog` は対称性による仮定追加 |
| `contrapose` | 対偶 | 対偶変換。`wlog` の対称ケースで使うことがある |

---

## 参照

- [Mathlib4 ドキュメント — wlog](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/WLOG.html)
- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
