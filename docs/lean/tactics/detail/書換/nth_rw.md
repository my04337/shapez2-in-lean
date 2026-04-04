# `nth_rw` — n番目の出現のみを書き換え

**カテゴリ**: 書換 | **定義元**: `Mathlib.Tactic.nthRwSeq` | **ソース**: Mathlib

## 概要
`nth_rw` は等式 `a = b` を用いて、ゴール中の `a` の **n番目の出現のみ** を書き換える。`rw` が最初の出現を書き換えるのに対し、`nth_rw` では出現位置を番号で指定できる。`conv` よりも簡潔に位置指定の書き換えを行える。

## ゴールパターン

**適用前**
```lean
h : a = b
⊢ f a + g a = h a
```

**適用後**（`nth_rw 2 [h]`）
```lean
-- 2番目の a のみが b に置換される
⊢ f a + g b = h a
```

## 構文
```lean
nth_rw n [h]            -- n番目の出現を書き換え（1-indexed）
nth_rw n [← h]          -- n番目を逆方向で書き換え
nth_rw n [h₁, h₂]      -- n番目の位置で順次適用
nth_rw n [h] at hyp     -- 仮定 hyp の n番目を書き換え
```

## 必須 import
```lean
import Mathlib.Tactic.NthRewrite
```

## オプション一覧
| 構文 | 意味 |
|---|---|
| `n` | 書き換え対象の出現番号（1始まり） |
| `[← e]` | 逆方向で書き換え |
| `at h` | 仮定 h の n番目を書き換え |

## Pros
- `conv` を使わず簡潔に位置を指定できる
- 番号指定なので構文が直感的
- `rw` と同じ感覚で使える

## Cons
- 式の構造変化で出現番号がずれる可能性がある
- 番号の数え方が直感に反する場合がある（ネストされた式の場合）
- `conv` の方が構造的に安定した位置指定ができる

## コードサンプル

### サンプル 1: 2番目の出現を書き換え
```lean
import Mathlib.Tactic.NthRewrite

example (a b : Nat) (h : a = b) : a + a = a + b := by
  nth_rw 2 [h]
  -- ⊢ a + b = a + b
```

### サンプル 2: 冪等性の証明
```lean
import Mathlib.Tactic.NthRewrite

example (f : α → α) (h : ∀ x, f (f x) = f x) (x : α) :
    f (f (f x)) = f x := by
  nth_rw 1 [h]
  -- ⊢ f (f x) = f x
  exact h x
```

### サンプル 3: 仮定の書き換え
```lean
import Mathlib.Tactic.NthRewrite

example (a b c : Nat) (h : a = b) (h₂ : a + a + a = c) : a + b + a = c := by
  nth_rw 2 [h] at h₂
  -- h₂ の 2番目の a を b に↑: h₂ : a + b + a = c
  exact h₂
```

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `nth_rewrite` | `nth_rw` の別名（同一機能） |
| `nth_grw` | `grewrite` を n 番目の出現にのみ適用する |
| `nth_grewrite` | `nth_grw` の別名 |

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `rw` | 最初の出現 | 位置を気にしない場合 |
| `conv` | 構造的位置指定 | 複雑な位置指定が必要な場合 |
| `simp_rw` | 全出現 + バインダ貫通 | 全出現を書き換える場合 |
| `erw` | 高透過度 | ユニフィケーション問題がある場合 |

## 参照
- [Mathlib4 ドキュメント — nth_rw](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/NthRewrite.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
