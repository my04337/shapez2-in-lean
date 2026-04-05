# `simp` — 補題データベースによる自動簡約

**カテゴリ**: 簡約 | **定義元**: `Lean.Parser.Tactic.simp` | **ソース**: Lean 4 core

---

## 概要

`@[simp]` 属性の補題群を用いてゴールや仮定を自動簡約する。Lean で最も頻繁に使われるタクティクの一つ。
`simp only [...]` で使用補題を限定でき、`at h` で仮定にも適用可能。
証明の最終版では `simp?` で `simp only` 形式に変換することが推奨される。

## ゴールパターン

**Before:**
```lean
⊢ 0 + n = n
```

**After:**
```lean
-- ゴールが閉じる（no goals）
```

**Before:**
```lean
⊢ (if True then x + 2 else 3) = x + 2
```

**After (simp only [ite_true]):**
```lean
-- ゴールが閉じる（no goals）
```

## 構文

```lean
simp
simp only [lemma₁, lemma₂, ...]
simp [lemma₁, lemma₂, ...]
simp [-lemma_to_exclude]
simp [*]
simp at h
simp at h₁ h₂
simp at *
simp_all
dsimp
dsimp only [...]
simpa
simpa using h
simp (config := { contextual := true })
simp +arith
simp +decide
```

## オプション一覧

| オプション | 説明 |
|---|---|
| `only` | デフォルトの `@[simp]` 集合を無効化し、明示した補題のみ使用する |
| `[h₁, h₂, ...]` | 追加で使用する補題を指定する |
| `[-id]` | 指定した `@[simp]` 補題を除外する |
| `[*]` | ローカルコンテキストの全仮定を補題として追加する |
| `at h` | 仮定 `h` に対して簡約を適用する |
| `at *` | ゴールと全仮定に対して簡約を適用する |
| `config := { ... }` | 簡約器の設定を変更する（`contextual`, `zeta`, `singlePass` など） |
| `+arith` | 算術的簡約を有効にする |
| `+decide` | `Decidable` インスタンスによる決定手続きを有効にする |

## Pros（使うべき場面）

- 広範なゴールに対応する最も汎用的な簡約タクティク
- `@[simp]` 補題の蓄積により巨大な書き換えデータベースを活用できる
- `simp?` で安定した `simp only` 形式を自動生成可能
- `at h` / `at *` で仮定にも適用可能
- `dsimp` は定義的等価を用いた簡約のみ行うため証明項に影響しない

## Cons（注意・失敗ケース）

- `simp` 単体は非終端的使用（中間ステップでの使用）が非推奨。簡約集合の変更で壊れやすい
- `simp` は遅い場合がある（補題数が多いため）。パフォーマンスが重要な場合は `simp only` を使う
- ループする場合がある（相互に書き換え合う `@[simp]` 補題がある場合）
- `norm_num` や `omega` で済むゴールに `simp` を使うのは非効率
- `simp` が失敗した場合、どの補題が足りないのか判別しにくい

## コードサンプル

### 例 1: 基本的な簡約

```lean
example (n : Nat) : 0 + n = n := by simp
```

`Nat.zero_add` が `@[simp]` 属性を持つため、自動で適用される。

### 例 2: simp only で補題を限定

```lean
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp only [ite_true]
```

`simp only` は指定した補題のみを使用するため、安定性が高い。

### 例 3: 仮定に対する simp

```lean
example (a b : Nat) (h : a + 0 = b) : a = b := by
  simp at h
  exact h
```

`simp at h` により仮定 `h : a + 0 = b` が `h : a = b` に簡約される。

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `simp!` | より積極的に展開する強化版 |
| `simp_intro` | `intro` + `simp` を組み合わせたタクティク |
| `simp_arith` | 算術簡約も併用する simp |

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `dsimp` | サブセット | 定義的等価による簡約のみ。証明項に影響しない安全な簡約 |
| `simpa` | 派生 | `simp` 後に `assumption` を自動適用する finishing tactic |
| `simp_all` | 拡張 | 全仮定とゴールを相互に簡約する。`simp at *` より強力 |
| `norm_num` | 補完 | 数値リテラルの計算に特化。`1 + 1 = 2` 等は `norm_num` 推奨 |
| `norm_cast` | 補完 | 型キャスト（`↑n`）を含む式の簡約に特化 |
| `rw` | 代替 | 特定の一箇所だけ書き換えたい場合。`simp` は繰り返し適用する |

## 参照

- [Lean 4 Reference — The Simplifier](https://lean-lang.org/doc/reference/latest/Tactics/Simplifier/)
- [Theorem Proving in Lean 4 — Tactics §5.4](https://lean-lang.org/theorem_proving_in_lean4/tactics.html)

---

> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
