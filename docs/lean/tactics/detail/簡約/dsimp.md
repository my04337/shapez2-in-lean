# `dsimp` — 定義的等価のみによる簡約

**カテゴリ**: 簡約 | **定義元**: `Lean.Parser.Tactic.dsimp` | **ソース**: Lean 4 core

---

## 概要

`dsimp` は `simp` の軽量版であり、**定義的等価（definitional equality）** で証明できる等式のみを用いて簡約する。
`rfl` で閉じられる書き換えだけを適用するため、証明項（proof term）に影響を与えない安全な簡約タクティク。
`simp` より高速で、後続タクティクが期待する正規形へ整えるための前処理として頻用される。

## ゴールパターン

**Before:**
```lean
⊢ (fun x => x + 1) 5 = 6
```

**After:**
```lean
⊢ 5 + 1 = 6
```

**Before:**
```lean
⊢ (α × β).1 = α   -- ペアの射影
```

**After:**
```lean
-- ゴールが閉じる（no goals）
```

## 構文

```lean
dsimp
dsimp only [lemma₁, lemma₂, ...]
dsimp [lemma₁, lemma₂, ...]
dsimp at h
dsimp at *
dsimp (config := { zeta := false })
```

## オプション一覧

| オプション | 説明 |
|---|---|
| `only` | デフォルトの `@[simp]` 集合を無効化し、明示した補題のみ使用する |
| `[h₁, h₂, ...]` | 追加で使用する補題を指定する（`rfl` で証明可能なもののみ有効） |
| `at h` | 仮定 `h` に対して簡約を適用する |
| `at *` | ゴールと全仮定に対して簡約を適用する |
| `config := { ... }` | `zeta`（let 展開）、`beta`（β簡約）等の設定を変更する |

## Pros（使うべき場面）

- 定義的等価のみを用いるため、証明項に影響しない安全な簡約
- `simp` より高速に実行される
- β簡約（ラムダ適用）、ι簡約（マッチ式の計算）、ζ簡約（let 展開）を自動処理
- 後続タクティクの前処理として安定的に利用できる
- 構造体のフィールドアクセス（射影）の簡約に最適

## Cons（注意・失敗ケース）

- `rfl` で証明できない等式（例: `Nat.add_comm`）は適用されない
- `simp` で閉じるゴールでも `dsimp` では閉じないケースが多い
- 補題を指定しても、それが定義的等価でなければ無視される
- `dsimp` だけで十分な場面を見極めるには慣れが必要

## コードサンプル

### 例 1: β簡約（ラムダの適用）

```lean
example : (fun x : Nat => x + 1) 3 = 4 := by
  dsimp
  -- ゴールが閉じる（定義的等価）
```

ラムダ式に引数を適用する β簡約は定義的等価なので `dsimp` で処理される。

### 例 2: 構造体の射影の簡約

```lean
example : (⟨1, 2⟩ : Nat × Nat).1 = 1 := by
  dsimp
  -- ゴールが閉じる（no goals）
```

構造体コンストラクタへの射影（`.1`, `.2`）は定義的等価で簡約される。

### 例 3: dsimp only で後続タクティクの前処理

```lean
example (f : Nat → Nat) (h : f = id) (n : Nat) : f n = n := by
  simp only [h]
  -- ⊢ id n = n
  rfl
```

`dsimp only [h]` は仮定 `h : f = id` を用いて `f` を `id` に書き換える。`id n` は定義的に `n` と等しいため `rfl` で閉じる。

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `dsimp?` | 使用した simp 補題を提案する |
| `dsimp!` | より積極的に展開する |
| `dsimp?!` | `dsimp!` + 提案 |

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `simp` | 上位互換 | 定義的等価以外の等式も使う。`dsimp` で不十分なら `simp` |
| `unfold` | 類似 | 特定の定義を1段階だけ展開したい場合 |
| `norm_num` | 補完 | 数値リテラルの計算は `norm_num` が最適 |
| `rfl` | 基盤 | `dsimp` は内部的に `rfl` で証明可能な等式のみ使用する |
| `change` | 代替 | 定義的に等しい別の式に手動で書き換える |

## 参照

- [Lean 4 Reference — The Simplifier](https://lean-lang.org/doc/reference/latest/Tactics/Simplifier/)
- [Theorem Proving in Lean 4 — Tactics §5.4](https://lean-lang.org/theorem_proving_in_lean4/tactics.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
