# `rwa` — 書き換え後に assumption

**カテゴリ**: 書換 | **定義元**: `Lean.Parser.Tactic.tacticRwa__` | **ソース**: Lean4 core

## 概要
`rwa` は `rw [...]; assumption` の省略形。等式で書き換えた後、コンテキスト中の仮定でゴールを自動的に閉じる。書き換えによってゴールが既存の仮定と一致する場合に、1行で証明を完了できる。

## ゴールパターン

**適用前**
```lean
h₁ : a = b
h₂ : P b
⊢ P a
```

**適用後**（`rwa [h₁]`）
```lean
-- rw [h₁] で ⊢ P b となり、h₂ : P b で閉じる
-- ゴールなし（証明完了）
```

## 構文
```lean
rwa [h]               -- rw [h]; assumption と同等
rwa [← h]             -- 逆方向で書き換え後 assumption
rwa [h₁, h₂]          -- 順次書き換え後 assumption
rwa [h] at hyp        -- 仮定を書き換え後 assumption で閉じる
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `[e₁, e₂, ...]` | 複数の書き換え規則を順次適用 |
| `[← e]` | 逆方向で書き換え |
| `at h` | 仮定 h で書き換え |

## Pros
- `rw` + `assumption` を 1 行にまとめられる
- 仮定に一致するまで書き換えるパターンで簡潔
- Lean4 core 組み込みで追加 import 不要

## Cons
- `assumption` で閉じない場合はエラーになる
- 書き換え後のゴールがどの仮定で閉じるか不透明になりうる
- デバッグ時は `rw` + `assumption` に分解した方がわかりやすい

## コードサンプル

### サンプル 1: 基本的な使用
```lean
example {α : Type*} {P : α → Prop} {a b : α} (h₁ : a = b) (h₂ : P b) : P a := by
  rwa [h₁]
  -- rw [h₁] で ⊢ P b → h₂ で閉じる
```

### サンプル 2: 逆方向の書き換え
```lean
example {α : Type*} {P : α → Prop} {a b : α} (h₁ : a = b) (h₂ : P a) : P b := by
  rwa [← h₁]
  -- rw [← h₁] で ⊢ P a → h₂ で閉じる
```

### サンプル 3: 複数の書き換え後に閉じる
```lean
example {α : Type*} {P : α → Prop} {a b c : α} (h₁ : a = b) (h₂ : b = c) (h₃ : P c) : P a := by
  rwa [h₁, h₂]
  -- rw [h₁] で ⊢ P b、rw [h₂] で ⊢ P c → h₃ で閉じる
```

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `rw` | 書換のみ | 書き換え後に別のタクティクを使う場合 |
| `assumption` | 仮定照合 | ゴールが仮定と一致する場合に単独使用 |
| `exact` | 明示指定 | 閉じる仮定を明示したい場合 |
| `simp` | 簡約 | 複雑な書き換えが必要な場合 |
| `subst` | 変数代入 | `h : x = e` で変数 x を消去 |

## 参照
- [Lean4 公式リファレンス — Rewriting](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#tactic-ref-rw)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
