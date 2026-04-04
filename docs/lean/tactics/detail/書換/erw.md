# `erw` — 高透過度の書き換え

**カテゴリ**: 書換 | **定義元**: `Lean.Parser.Tactic.tacticErw__` | **ソース**: Lean4 core

## 概要
`erw` は `rw` と同じ書き換えを行うが、ユニフィケーションの透過度（transparency）を高く設定して実行する。`rw` が通常の `reducible` 透過度を使うのに対し、`erw` は `default`（`eq_mpr` レベル）まで展開して照合する。`rw` でユニフィケーションが失敗するケースで有効。

## ゴールパターン

**適用前**
```lean
h : f x = g x
⊢ P (f x)
```

**適用後**（`erw [h]`、`rw [h]` では失敗するケース）
```lean
⊢ P (g x)
```

## 構文
```lean
erw [h]               -- 高透過度で書き換え
erw [← h]             -- 逆方向
erw [h₁, h₂]          -- 順次適用
erw [h] at hyp        -- 仮定 hyp を書き換え
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
- `rw` が失敗する definitional equality を跨いで書き換え可能
- 構文が `rw` と同一で移行コストが低い
- 型クラスのインスタンス展開が必要な場面で有効

## Cons
- 高透過度のため意図しない位置が書き換わるリスクがある
- Mathlib のリンティングで非推奨とされることがある
- デバッグ時に挙動が予測しづらい
- `rw` で済む場合は使わない方が良い

## コードサンプル

### サンプル 1: rw で失敗するケースの救済
```lean
-- rw で定義展開が不十分な場合
def myId (n : Nat) : Nat := n

example (h : myId 0 = 1) : myId 0 + 2 = 3 := by
  -- rw [h] で失敗する場合に erw を使う
  erw [h]
  -- ⊢ 1 + 2 = 3
```

### サンプル 2: 型強制を跨ぐ書き換え
```lean
example (n m : Nat) (h : (n : Int) = (m : Int)) :
    (n : Int) + 1 = (m : Int) + 1 := by
  erw [h]
  -- ⊢ ↑m + 1 = ↑m + 1 が rfl で閉じる
```

### サンプル 3: 仮定での使用
```lean
example {α : Type*} (a b c : α) (f : α → α) (h₁ : a = b) (h₂ : f a = c) : f b = c := by
  erw [← h₁]
  -- ⊢ f a = c
  exact h₂
```

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `erw?` | 使用可能な書き換えルールを提案する |

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `rw` | 標準書換 | ユニフィケーションが通る場合は `rw` 優先 |
| `simp` | 簡約 | 繰り返し簡約が必要な場合 |
| `change` | 型変更 | ゴールの型を definitionally equal に変更 |
| `unfold` | 定義展開 | 特定の定義を展開して見通しを良くする |

## 参照
- [Lean4 公式リファレンス — Rewriting](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#tactic-ref-rw)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
