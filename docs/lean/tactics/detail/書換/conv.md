# `conv` — 位置指定の変換モード

**カテゴリ**: 書換 | **定義元**: `Lean.Parser.Tactic.Conv.conv` | **ソース**: Lean4 core

## 概要
`conv` はゴールの特定の部分式にフォーカスして書き換えを行う変換モード。`rw` が最初の出現しか書き換えられないのに対し、`conv` では式のツリー構造を辿って特定位置のみを精密に変換できる。

## ゴールパターン

**適用前**
```lean
⊢ f a + f a = f a + f b
```

**適用後** (`conv_rhs => rw [← h]`, `h : b = a`)
```lean
⊢ f a + f a = f a + f a  -- rfl で閉じる
```

## 構文
```lean
conv =>                      -- ゴール全体で conv モードに入る
  lhs                        -- 左辺にフォーカス
  rhs                        -- 右辺にフォーカス
  arg 1                      -- 第1引数にフォーカス
  ext x                      -- バインダを開く
  rw [h]                     -- フォーカス位置で書き換え
  simp                       -- フォーカス位置で簡約
  ring_nf                    -- フォーカス位置で正規化

conv_lhs => tac              -- 左辺のみで conv
conv_rhs => tac              -- 右辺のみで conv
conv at h => tac             -- 仮定 h で conv
```

## 必須 import
Lean4 core 組み込み。

## conv モード内のナビゲーション
| コマンド | 意味 |
|---|---|
| `lhs` | 等式の左辺にフォーカス |
| `rhs` | 等式の右辺にフォーカス |
| `arg n` | 第n引数にフォーカス |
| `ext x` | ∀/λ のバインダを開く |
| `enter [1, 2]` | ネストされた位置にジャンプ |
| `pattern e` | パターンマッチで位置を特定 |

## Pros
- 特定の部分式だけを精密に書き換え可能
- `rw` では書き換えられない位置を制御できる
- `conv_lhs` / `conv_rhs` で左右を独立に操作

## Cons
- `rw` だけで済む場合は冗長
- ナビゲーション構文の学習コストがやや高い
- 深いネスト式ではナビゲーションが煩雑

## コードサンプル

### サンプル 1: 右辺のみ書き換え
```lean
example (f : Nat → Nat) (a b : Nat) (h : b = a) : f a = f b := by
  conv_rhs => rw [h]
```

### サンプル 2: 特定引数にフォーカス
```lean
example (a b : Nat) (h : a = b) : a + a = b + a := by
  conv_lhs => arg 1; rw [h]
```

### サンプル 3: ラムダ内部の書き換え
```lean
example (f g : Nat → Nat) (h : ∀ x, f x = g x) : (fun x => f x + 1) = (fun x => g x + 1) := by
  conv_lhs => ext x; rw [h x]
```

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `conv'` | より厚式な conv（内部実装の差異） |
| `conv?` | 提案版。フォーカス位置を提案する |
| [`conv_lhs`](conv_lhs.md) | 等式左辺にフォーカス |
| [`conv_rhs`](conv_rhs.md) | 等式右辺にフォーカス |

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `rw` | 単純書換 | 最初の出現を書き換えるだけで十分な場合 |
| `simp` | 簡約 | 全出現を一括簡約する場合 |
| `change` | 型変更 | ゴールを definitionally equal な形に変更 |

## 参照
- [Lean4 公式リファレンス — conv](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#conv)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
