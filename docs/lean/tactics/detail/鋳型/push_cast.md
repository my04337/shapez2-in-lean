# `push_cast` — キャストを葉に向けて押し込む

**カテゴリ**: キャスト | **定義元**: `Lean.Parser.Tactic.tacticPush_cast_` | **ソース**: Lean4 core

## 概要
`push_cast` は型キャスト（`↑`）を式の外側から内側（葉）に向けて押し込む正規化タクティク。`@[push_cast]` 属性の補題を使い、`↑(a + b)` を `↑a + ↑b` のように分配する。キャストを葉に集約することで、`ring` や `omega` などの後続タクティクが適用しやすい形に変換する。

## ゴールパターン

**適用前**
```lean
⊢ (↑(n + m) : Int) = ↑n + ↑m
```

**適用後**
```lean
-- push_cast により ↑(n + m) が ↑n + ↑m に展開され、ゴールは ↑n + ↑m = ↑n + ↑m となり閉じる
```

**適用前**（仮定に対して）
```lean
h : (↑(a * b) : Int) > 0
⊢ P
```

**適用後**
```lean
h : ↑a * ↑b > 0
⊢ P
```

## 構文
```lean
push_cast                 -- ゴールのキャストを内側に押す
push_cast at h            -- 仮定 h のキャストを内側に押す
push_cast at h ⊢          -- 仮定 h とゴール両方
push_cast at *            -- 全仮定とゴールに適用
push_cast [lemma]         -- 追加の補題を使用
```

## 必須 import
Lean4 core 組み込み。`@[push_cast]` 補題は Batteries / Mathlib に多数あり。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `at h` | 仮定 h に適用 |
| `at *` | 全仮定とゴールに適用 |
| `[h₁, h₂]` | 追加の補題を使用して正規化 |

## Pros
- キャストの位置を統一し、後続の `ring` / `omega` / `linarith` が動きやすくなる
- `norm_cast` と異なり、ゴールを閉じようとしないため過剰な変換を避けられる
- `@[push_cast]` 属性で補題を追加すればカスタム型にも対応可能

## Cons
- `@[push_cast]` 補題が不足しているとキャストが残る
- キャストを外側に引き出したい場合は逆に不便（`norm_cast` を使う）
- 減算 `↑(a - b)` は `Nat` の飽和減算の扱いに注意が必要

## コードサンプル

### サンプル 1: 基本的なキャスト分配
```lean
example (n m : Nat) : (↑(n + m) : Int) = ↑n + ↑m := by
  push_cast
  -- ⊢ ↑n + ↑m = ↑n + ↑m
  rfl
```

### サンプル 2: push_cast + ring の連携
```lean
example (n : Nat) : (↑(n * n + 2 * n + 1) : Int) = (↑n + 1) ^ 2 := by
  push_cast
  -- ⊢ ↑n * ↑n + 2 * ↑n + 1 = (↑n + 1) ^ 2
  ring
```

### サンプル 3: 仮定のキャスト正規化
```lean
example (a b : Nat) (h : (↑(a + b) : Int) = 10) : (↑a : Int) + ↑b = 10 := by
  push_cast at h
  -- h : ↑a + ↑b = 10 ⊢ ↑a + ↑b = 10
  exact h
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `norm_cast` | キャスト正規化 | ゴールを閉じるところまでやる |
| `exact_mod_cast` | exact + cast処理 | キャスト差異を無視して exact |
| `ring` | 環の等式 | `push_cast` 後の等式を閉じる |
| `omega` | 線形算術 | `push_cast` 後の Nat/Int 不等式 |

## 参照
- [Lean4 公式リファレンス — norm_cast tactics](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#norm_cast-tactics)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
