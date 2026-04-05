# `rewrite` — 等式による書き換え（明示形）

**カテゴリ**: 書換 | **定義元**: `Lean.Parser.Tactic.rewrite` | **ソース**: Lean4 core

## 概要
`rewrite` は等式 `a = b` を用いてゴールや仮定中の `a` を `b` に置換する。`rw` と異なり、書き換え後に `rfl` を自動的に試みない。ゴールが書き換え後も残るため、連鎖的な書き換えの途中で使用する場面や、書き換え後にさらに別のタクティクを適用したい場合に適する。

## ゴールパターン

**適用前**
```lean
h : a = b
⊢ f a = f b
```

**適用後**（`rewrite [h]`）
```lean
-- rw と違い rfl を自動適用しない → ゴールが残る
⊢ f b = f b
```

## 構文
```lean
rewrite [h]               -- h : a = b で a → b に書き換え
rewrite [← h]             -- 逆方向: b → a に書き換え
rewrite [h₁, h₂, h₃]     -- 順次適用
rewrite [h] at hyp        -- 仮定 hyp を書き換え
rewrite [h] at *          -- 全体を書き換え
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `[e₁, e₂, ...]` | 複数の書き換え規則を順次適用 |
| `[← e]` | 逆方向で書き換え |
| `at h` | 仮定 h で書き換え |
| `at *` | 全仮定とゴールで書き換え |

## Pros
- `rfl` を試みないため、書き換え後にゴールを確認しやすい
- 書き換えが `rfl` で閉じないケースでも想定通りに使える
- `rw` と同じ構文で馴染みやすい

## Cons
- 最終的に `rfl` で閉じる場合は `rw` の方が簡潔
- 通常は `rw` で十分であり、使用頻度は低い
- `rw` と同様、最初の出現のみを書き換える

## コードサンプル

### サンプル 1: 基本（rfl が自動適用されない）
```lean
example (h : a = b) : a + 1 = b + 1 := by
  rewrite [h]
  -- ⊢ b + 1 = b + 1  （ゴールが残る）
  rfl
```

### サンプル 2: rw との違い
```lean
-- rw は rewrite + try rfl
-- rw [h] は以下と同等:
example (h : a = b) (h₂ : b + 1 = c) : a + 1 = c := by
  rewrite [h]
  -- ⊢ b + 1 = c  （rfl で閉じないのでゴールが残る）
  exact h₂
```

### サンプル 3: 仮定の書き換え
```lean
example (h : a = b) (h₂ : b + 1 = c) : a + 1 = c := by
  rewrite [← h] at h₂
  -- h₂ : a + 1 = c（← h により b → a に書き換え）
  exact h₂
```

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `rw` | rewrite + try rfl | ほとんどの場合 `rw` で十分 |
| `erw` | 緩い rewrite | ユニフィケーションが厳しいとき |
| `simp` | 繰り返し書き換え | 全出現に繰り返し適用 |
| `conv` | 位置指定 | 特定の部分式のみ書き換えたい場合 |
| `subst` | 変数代入 | `h : x = e` で x を消去 |

## 参照
- [Lean4 公式リファレンス — Rewriting](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#tactic-ref-rw)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
