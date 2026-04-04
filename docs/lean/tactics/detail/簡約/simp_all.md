# `simp_all` — ゴールと全仮定の相互簡約

**カテゴリ**: 簡約 | **定義元**: `Lean.Parser.Tactic.simpAll` | **ソース**: Lean 4 core

---

## 概要

`simp_all` は `simp at *` の強化版であり、ゴールと全仮定を**相互に**簡約する。
各仮定を簡約する際に他の仮定も補題として使用し、ゴール簡約時には全仮定を活用する。
仮定間の依存関係を考慮した反復簡約により、`simp at *` では閉じないゴールも閉じることができる。
強力だが積極的に仮定を書き換えるため、中間ステップでの使用には注意が必要。

## ゴールパターン

**Before:**
```lean
h₁ : a = b
h₂ : b = c
⊢ a = c
```

**After:**
```lean
-- ゴールが閉じる（no goals）
```

**Before:**
```lean
h₁ : p → q
h₂ : p
⊢ q
```

**After:**
```lean
-- ゴールが閉じる（no goals）
```

## 構文

```lean
simp_all
simp_all only [lemma₁, lemma₂, ...]
simp_all [lemma₁, lemma₂, ...]
simp_all [-lemma_to_exclude]
simp_all +arith
simp_all +decide
```

## オプション一覧

| オプション | 説明 |
|---|---|
| `only` | デフォルトの `@[simp]` 集合を無効化し、明示した補題のみ使用する |
| `[h₁, h₂, ...]` | 追加で使用する補題を指定する |
| `[-id]` | 指定した `@[simp]` 補題を除外する |
| `+arith` | 算術的簡約を有効にする |
| `+decide` | `Decidable` インスタンスによる決定手続きを有効にする |

## Pros（使うべき場面）

- `simp at *` より強力。仮定同士の相互簡約が可能
- 仮定が多い場合のゴール消化に非常に有効
- `simp_all only [...]` で安定性を確保しつつ強力な簡約が行える
- 証明の finishing tactic として頻出

## Cons（注意・失敗ケース）

- 全仮定を書き換えるため、仮定の名前や形が予測しにくくなる
- 中間ステップで使うと後続のタクティクが壊れやすい
- `simp at *` より遅い場合がある（反復回数が多い）
- 非終端的使用は非推奨。`simp_all only [...]` への変換を推奨
- 仮定を `False` に簡約した場合、暗黙に `contradiction` が適用される

## コードサンプル

### 例 1: 仮定間の相互簡約

```lean
example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  simp_all
  -- h₁ により a が b に、h₂ により b が c に簡約され、ゴールが閉じる
```

`simp at *` と異なり、`simp_all` は仮定 `h₁` を使ってゴール中の `a` を `b` に書き換え、さらに `h₂` で `b` を `c` に書き換える。

### 例 2: 仮定の命題値による簡約

```lean
example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  simp_all
  -- hp : p が hpq : p → q に適用され、q が得られてゴールが閉じる
```

`simp_all` は命題値の仮定 `hp : p` を使って `hpq : p → q` を `hpq : q` に簡約し、ゴールを閉じる。

### 例 3: simp_all only でリスト操作

```lean
example (l : List Nat) (h : l = []) : l.length = 0 := by
  simp_all only [List.length_nil]
  -- h : l = [] を使い l.length を [].length に簡約し、List.length_nil で 0 に
```

`simp_all only` は指定した補題のみを使用するため、安定した証明が書ける。

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `simp_all?` | 使用した補題を提案する |
| `simp_all!` | より積極的に展開する強化版 |
| `simp_all_arith` | 算術簡約も併用する |

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `simp` | ベース | ゴールのみ簡約。仮定を書き換えたくない場合 |
| `simp at *` | 弱い版 | 各仮定を独立に簡約。仮定間の相互利用なし |
| `simpa` | 補完 | `simp` 後に `assumption`/`exact` で閉じる finishing tactic |
| `aesop` | 代替 | より汎用的な自動証明。`simp_all` で不十分な場合 |
| `omega` | 補完 | 線形算術に特化。数値制約は `omega` が最適 |

## 参照

- [Lean 4 Reference — The Simplifier](https://lean-lang.org/doc/reference/latest/Tactics/Simplifier/)
- [Theorem Proving in Lean 4 — Tactics §5.4](https://lean-lang.org/theorem_proving_in_lean4/tactics.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
