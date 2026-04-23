# `congr` — 等式ゴールを引数ごとのサブゴールに分解する

**カテゴリ**: 変換 | **定義元**: `Lean.Parser.Tactic.congr` | **ソース**: Lean4 core

---

## 概要

`congr` はゴール `f a₁ a₂ ... = f b₁ b₂ ...` を、関数 `f` が共通であることを利用して
`a₁ = b₁`, `a₂ = b₂`, ... のサブゴールに分解するタクティクである。
合同性（congruence）を自動適用し、両辺の差異がある部分のみをサブゴールとして残す。
深さを指定する `congr n` や、拡張の `congr with` も使える。

---

## ゴールパターン

**適用前**
```lean
⊢ f a = f b
```

**適用後**
```lean
⊢ a = b
```

---

## 構文

```lean
congr
congr n
congr with x
```

- `n`: 分解の深さ（省略時は 1 段階）
- `x`: ラムダ変数を束縛する（関数拡張性との組み合わせ）

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `congr` | 1 段階だけ合同性を適用する |
| `congr n` | `n` 段階まで再帰的に合同性を適用する |
| `congr with x` | 関数型の引数に `x` を束縛して分解する（`funext` 的な分解） |

---

## Pros（使うべき場面）

- 両辺が同じ関数適用で引数だけ異なる場合に、差異の部分のみに集中できる
- `Sigma` 型やコンストラクタの等式分解にも使える
- `congr n` で深さを制御でき、必要な部分だけ分解可能

---

## Cons（注意・失敗ケース）

- 両辺の関数が異なる場合は適用できない
- 依存型の場合、分解後のサブゴールが複雑になることがある
- 分解しすぎると不要なサブゴールが生成される場合がある

---

## コードサンプル

### サンプル 1: 基本的な合同分解

```lean
example (h : a = b) : a + 1 = b + 1 := by
  -- ⊢ a + 1 = b + 1
  congr
  -- congr が h を assumption で自動的に使って閉じる
```

### サンプル 2: リストの合同分解

```lean
example (h : a = b) : [a, 1] = [b, 1] := by
  -- ⊢ [a, 1] = [b, 1]
  congr 1
  -- congr が h を assumption で自動的に使って閉じる
```

### サンプル 3: 深さ指定

```lean
example (h : a = b) : (a + 1, 2) = (b + 1, 2) := by
  -- ⊢ (a + 1, 2) = (b + 1, 2)
  congr 2
  -- congr が h を assumption で自動的に使って閉じる
```

---

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `congr!` | より強力な合同分解（Mathlib）。型レベルの合同性も処理 |
| [`congrm`](congrm.md) | パターンで合同分解の位置を指定する |
| `congrm?` | `congrm` の提案版。パターンを自動探索 |

## 関連タクティク
| `ext` | 拡張的等式 | `@[ext]` 属性で構造体の等式をフィールドごとに分解する |
| `rw` | 直接書き換え | 特定の等式で書き換え。`congr` は構造的分解 |
| `simp_rw` | 書き換え | バインダ内部の書き換えにも対応。`congr` は分解のみ |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
