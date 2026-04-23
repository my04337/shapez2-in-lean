# `simpa` — 簡約後に仮定で即座に閉じる

**カテゴリ**: 簡約 | **定義元**: `Lean.Parser.Tactic.simpa` | **ソース**: Lean 4 core

---

## 概要

`simpa` は `simp` の後に `assumption` または `exact` を自動適用する finishing tactic。
`simpa using e` の形式が最も頻用され、ゴールと式 `e` の両方を `simp` で簡約した後、
`e` でゴールを閉じる。`simp` → `exact` の2行を1行に凝縮できる。

典型的なパターン: 仮定 `h` とゴールが「ほぼ同じだが `simp` 補題で整理すれば一致する」場合に使用。

## ゴールパターン

**Before:**
```lean
h : a + 0 = b
⊢ a = b
```

**After (simpa using h):**
```lean
-- ゴールが閉じる（no goals）
```

**Before:**
```lean
h : p ∧ True
⊢ p
```

**After (simpa using h):**
```lean
-- ゴールが閉じる（no goals）
```

## 構文

```lean
simpa
simpa using e
simpa [lemma₁, ...] using e
simpa only [lemma₁, ...] using e
simpa (config := { ... }) using e
```

## オプション一覧

| オプション | 説明 |
|---|---|
| `using e` | ゴール簡約後に `e` を `simp` で簡約し `exact` する。最も一般的な用法 |
| `only` | デフォルトの `@[simp]` 集合を無効化し、明示した補題のみ使用する |
| `[h₁, h₂, ...]` | 追加で使用する補題を指定する |
| `config := { ... }` | 簡約器の設定を変更する |

## Pros（使うべき場面）

- `simp at h; exact h` を1行で書ける
- ゴールと仮定を同時に簡約するため、手動で合わせる手間がない
- finishing tactic として非常に読みやすい
- `simpa only [...]` で安定した証明が書ける

## Cons（注意・失敗ケース）

- `using` を省略した場合、`assumption` で閉じようとするが、マッチする仮定がなければ失敗する
- `simp` で閉じてしまう場合は `simpa` を使う意味がない（冗長）
- ゴールと `using` の式が `simp` 後にも一致しない場合は失敗する
- デバッグが `simp` より難しい（ゴール側と式側のどちらが問題か判別しにくい）

## コードサンプル

### 例 1: 基本的な simpa using

```lean
example (a b : Nat) (h : a + 0 = b) : a = b := by
  simpa using h
  -- simp がゴールの a = b と仮定 h の a + 0 = b を両方簡約し、一致させて閉じる
```

`Nat.add_zero` で `h : a + 0 = b` が `h : a = b` に簡約され、ゴールと一致する。

### 例 2: 補題を追加して simpa

```lean
example (l : List Nat) (h : l.reverse.reverse = [1, 2]) : l = [1, 2] := by
  simpa [List.reverse_reverse] using h
  -- List.reverse_reverse で l.reverse.reverse = l に簡約し、h でゴールを閉じる
```

`simpa [lemma] using h` で追加補題を指定しつつ仮定でゴールを閉じる典型パターン。

### 例 3: using なしの simpa

```lean
example (p : Prop) (h : p) : p ∧ True := by
  simpa
  -- ゴール p ∧ True を simp で p に簡約後、仮定 h : p で自動的に閉じる
```

`using` を省略した `simpa` は、ゴールを `simp` した後にコンテキストの仮定から `assumption` を試みる。

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `simpa?` | 使用した補題を提案する |
| `simpa!` | より積極的に展開する強化版 |
| `simpa?!` | `simpa!` + 提案 |

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `simp` | ベース | ゴールを閉じずに簡約だけしたい場合 |
| `simp_all` | 拡張 | 全仮定を相互簡約する場合 |
| `exact` | 構成要素 | `simpa` は内部的に `simp` 後に `exact` を適用する |
| `assumption` | 構成要素 | `using` なしの `simpa` は `assumption` を使用する |
| `rw [...]; exact h` | 代替 | 特定の箇所だけ書き換えて閉じたい場合 |

## 参照

- [Lean 4 Reference — The Simplifier](https://lean-lang.org/doc/reference/latest/Tactics/Simplifier/)
- [Theorem Proving in Lean 4 — Tactics §5.4](https://lean-lang.org/theorem_proving_in_lean4/tactics.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
