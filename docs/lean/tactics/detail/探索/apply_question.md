# `apply?` — ゴールに適用可能な補題のライブラリ検索

**カテゴリ**: 検索 | **定義元**: `Lean.Parser.Tactic.apply?` | **ソース**: Lean4 core

## 概要
`apply?` はライブラリ全体を探索し、現在のゴールに `apply` で適用できる補題を検索する。ゴールの結論にユニファイ可能な補題を見つけ、新しいサブゴールとともに候補を提示する。`exact?` がゴールを完全に閉じる補題を探すのに対し、`apply?` は部分的にマッチする補題も含めて検索する。

## ゴールパターン

**適用対象**: 任意のゴール。検索結果をサジェスチョンとして表示する。

## 構文
```lean
apply?                   -- ゴールに適用可能な補題を検索
apply? using [h₁, h₂]   -- 指定仮定の使用を優先して検索
```

## 必須 import
Lean4 core 組み込み。追加 import 不要。

## Pros
- ゴールの結論から逆方向に使える補題を発見できる
- `exact?` で見つからない場合も、サブゴールを残す形で候補を提示
- 結果を `apply lemma_name` 形式でそのままコピー可能
- 未知のライブラリ API を探索するのに非常に有用

## Cons
- ライブラリ全体を探索するため数秒〜数十秒かかる
- 最終的な証明では結果で置き換えること（`apply?` のまま残さない）
- Mathlib が大きいほど探索時間が増加
- 多数の候補が返る場合があり、選別が必要

## コードサンプル

### サンプル 1: 不等式の補題を発見
```lean
-- ⊢ n ≤ n + 1
-- apply? が "Try this: exact Nat.le_succ n" 等を提示
example (n : Nat) : n ≤ n + 1 := by
  apply?
```

### サンプル 2: リストの性質
```lean
-- ⊢ (a :: l).length = l.length + 1
-- apply? が List.length_cons を発見
example (a : α) (l : List α) : (a :: l).length = l.length + 1 := by
  apply?
```

### サンプル 3: using で仮定を指定
```lean
-- h : a < b
-- ⊢ a ≤ b
-- 仮定 h を使う方向で検索
example (a b : Nat) (h : a < b) : a ≤ b := by
  apply?
```

## `exact?` との使い分け

| 観点 | `exact?` | `apply?` |
|---|---|---|
| 検索対象 | ゴールを完全に閉じる補題 | ゴールに `apply` できる補題 |
| 残りゴール | なし | サブゴールが残る場合あり |
| 用途 | 一発で閉じたい | 証明の方向性を探りたい |

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `exact?` | 完全一致検索 | ゴールを一発で閉じたい場合 |
| `rw?` | 書き換え検索 | 等式の書き換え規則を探す場合 |
| `simp?` | simp 検索 | simp で使う補題セットを特定したい場合 |
| `hint` | 複合検索 | 複数の戦略を同時に試したい場合 |
| `aesop` | 自動証明 | 検索ではなく自動で閉じたい場合 |

## 参照
- [Lean4 公式リファレンス — apply?](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
