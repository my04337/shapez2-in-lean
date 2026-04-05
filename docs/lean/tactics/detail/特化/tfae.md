# `tfae_have` / `tfae_finish` — TFAE（同値条件列挙）証明フレームワーク

**カテゴリ**: 特化 | **定義元**: `Mathlib.Tactic.TFAE.tfaeHave` / `Mathlib.Tactic.TFAE.tfaeFinish` | **ソース**: Mathlib

---

## 概要

`tfae_have` と `tfae_finish` は「以下の条件はすべて同値である」(TFAE: The Following Are Equivalent) 形式の命題を証明するためのタクティクペアである。
`tfae_have` で条件間の含意関係（`→`）または同値関係（`↔`）を一つずつ示し、
十分な関係が集まったら `tfae_finish` が推移律を利用して全体の同値性を自動で閉じる。
数学の教科書でよくある「以下は同値」形式の定理の形式化に最適。

---

## ゴールパターン

**適用対象**: `TFAE [P₁, P₂, ..., Pₙ]` 形式のゴール

**適用前**
```lean
⊢ TFAE [P, Q, R]
```

**適用後** (`tfae_have` で含意を示した後 `tfae_finish`)
```lean
-- ゴールなし（証明完了）
```

---

## 構文

```lean
tfae_have i → j               -- 条件 i から条件 j への含意
  · <proof>
tfae_have i ↔ j               -- 条件 i と条件 j の同値
  · <proof>
tfae_finish                    -- 推移律で全体を閉じる
```

条件番号は 1-indexed（`TFAE` リストの先頭が 1）。

---

## 必須 import

```lean
import Mathlib.Tactic.TFAE
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `tfae_have i → j` | 条件 `i` から条件 `j` への含意を証明 |
| `tfae_have i ↔ j` | 条件 `i` と条件 `j` の同値を証明 |
| `tfae_have i ← j` | 条件 `j` から条件 `i` への含意を証明 |
| `tfae_finish` | 蓄積された関係から推移律で全体を閉じる |

---

## Pros（使うべき場面）

- 同値条件の列挙証明が自然な形で記述できる
- 必要最小限の含意関係を示せば、`tfae_finish` が残りを推論する
- 円環含意（1→2→3→1）でも直接同値（1↔2, 2↔3）でも対応

---

## Cons（注意・失敗ケース）

- `TFAE` 型のゴールでなければ使えない
- 含意のチェーンが不完全だと `tfae_finish` が失敗する
- 条件数が多いと必要な含意の数が増え、証明が長くなる

---

## コードサンプル

### サンプル 1: 3 条件の円環含意

```lean
import Mathlib.Tactic.TFAE

example (P Q R : Prop) (hpq : P → Q) (hqr : Q → R) (hrp : R → P) :
    List.TFAE [P, Q, R] := by
  -- ⊢ List.TFAE [P, Q, R]
  tfae_have 1 → 2 := hpq
  tfae_have 2 → 3 := hqr
  tfae_have 3 → 1 := hrp
  tfae_finish
  -- ゴールなし（証明完了）
```

### サンプル 2: 同値関係で証明

```lean
import Mathlib.Tactic.TFAE

example (n : Nat) : List.TFAE [n = 0, n ≤ 0, ¬(n > 0)] := by
  -- ⊢ List.TFAE [n = 0, n ≤ 0, ¬(n > 0)]
  tfae_have 1 ↔ 2 := by constructor <;> omega
  tfae_have 2 ↔ 3 := by constructor <;> omega
  tfae_finish
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `constructor` | ↔ 分解 | 同値命題を2方向の含意に分解 |
| `iff_of_true` / `iff_of_false` | 自明同値 | 両方が真/偽の場合の同値 |
| `simp` | 簡約 | 各含意の証明内で使用 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
