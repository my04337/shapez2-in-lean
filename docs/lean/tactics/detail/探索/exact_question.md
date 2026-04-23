# `exact?` / `apply?` / `rw?` — ライブラリ検索タクティク

**カテゴリ**: 検索 | **定義元**: `Lean.Parser.Tactic.exact?` / `Lean.Parser.Tactic.apply?` / `Lean.Parser.Tactic.rw?` | **ソース**: Lean4 core

## 概要
`exact?` はゴールを閉じる補題をライブラリから検索する。`apply?` はゴールに `apply` で適用できる補題を検索する。`rw?` は `rw` で使える書き換え規則を検索する。いずれも主に探索・学習目的のインタラクティブなタクティク。

## ゴールパターン

**適用対象**: 任意のゴール。検索結果をサジェスチョンとして表示する。

## 構文
```lean
exact?                   -- ゴールを閉じる補題を検索
apply?                   -- ゴールに適用可能な補題を検索
rw?                      -- 書き換え可能な補題規則を検索
exact? using [h₁, h₂]   -- 仮定のサブセットを使用して検索
```

## 必須 import
Lean4 core 組み込み。

## Pros
- 名前を覚えていない補題を見つけるのに最適
- 結果を `exact ...` / `apply ...` / `rw [...]` 形式でそのままコピーできる
- 学習時のライブラリ探索に非常に有用

## Cons
- 実行が遅い（ライブラリ全体を探索するため数秒〜数十秒）
- 最終的な証明では `exact?` の結果で書き換えること（`exact?` のまま残さない）
- Mathlib が大きいほど遅くなる
- 見つからない場合もある（探索空間の制限）

## コードサンプル

### サンプル 1: exact? で補題を発見
```lean
example : 0 + n = n := by
  exact? -- "Try this: exact Nat.zero_add n" と表示
```

### サンプル 2: apply? で適用候補を発見
```lean
example (h : n ≤ m) : n ≤ m + 1 := by
  apply? -- 候補リストを表示
```

### サンプル 3: rw? で書き換え規則を発見
```lean
example : a + 0 = a := by
  rw? -- "Try this: rw [Nat.add_zero]" と表示
```

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `exact` | 直接適用 | 補題名が分かっている場合 |
| `apply` | 直接適用 | 適用先が分かっている場合 |
| `simp?` | simp 版検索 | simp only の安定版を得たい場合 |
| `grind?` | grind 版検索 | grind only の安定版を得たい場合 |

## 参照
- [Lean4 公式リファレンス — exact?](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#exact%3F)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
