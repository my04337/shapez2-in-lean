# `rw?` — 書き換え規則のライブラリ検索

**カテゴリ**: 検索 | **定義元**: `Lean.Parser.Tactic.rwSeq` (rw?) | **ソース**: Lean4 core

## 概要
`rw?` はライブラリを探索し、現在のゴールに適用可能な書き換え規則（等式・同値）を検索する。見つかった規則を `rw [lemma_name]` 形式でサジェスチョンとして提示する。ゴール中の部分式を書き換えできる補題を自動的に発見するため、等式の変形が必要な場面で名前が思い出せない場合に有用。

## ゴールパターン

**適用対象**: 等式・同値を含むゴール。書き換え候補をサジェスチョンとして表示する。

## 構文
```lean
rw?                      -- ゴールに適用可能な書き換え規則を検索
rw? at h                 -- 仮定 h に対して書き換え規則を検索
```

## 必須 import
Lean4 core 組み込み。追加 import 不要。

## Pros
- 等式の書き換えに使える補題を自動発見
- `rw [...]` 形式でそのまま証明に貼り付け可能
- `at h` で仮定に対しても検索できる
- Mathlib の膨大な `simp` 補題・等式から適切なものを見つけられる

## Cons
- ライブラリ全体を探索するため実行が遅い（数秒〜数十秒）
- 最終証明では結果で置き換えること（`rw?` のまま残さない）
- 書き換え方向（左→右 / 右→左）の候補が多く出る場合がある
- 複数ステップの書き換えは一度には見つからない

## コードサンプル

### サンプル 1: 加算の交換法則を発見
```lean
-- ⊢ a + b = b + a
-- rw? が "Try this: rw [Nat.add_comm]" と表示
example (a b : Nat) : a + b = b + a := by
  rw?
```

### サンプル 2: リストの性質
```lean
-- ⊢ (l₁ ++ l₂).length = l₁.length + l₂.length
-- rw? が List.length_append を発見
example (l₁ l₂ : List α) : (l₁ ++ l₂).length = l₁.length + l₂.length := by
  rw?
```

### サンプル 3: 仮定に対して検索
```lean
-- h : a + 0 = b
-- ⊢ a = b
-- 仮定 h の左辺を簡約する規則を検索
example (h : a + 0 = b) : a = b := by
  rw? at h
  exact h
```

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `rw` | 直接書き換え | 補題名が分かっている場合 |
| `simp?` | simp 版検索 | 複数の簡約を一括で特定したい場合 |
| `exact?` | 完全一致検索 | 書き換えではなく直接閉じたい場合 |
| `apply?` | 適用検索 | `apply` で使える補題を探したい場合 |
| `simp` | 自動簡約 | 書き換え規則を個別に指定せず簡約したい場合 |

## 参照
- [Lean4 公式リファレンス — rw](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
