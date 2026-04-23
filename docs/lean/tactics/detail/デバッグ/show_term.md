# `show_term` — タクティクが生成する証明項を表示

**カテゴリ**: デバッグ | **定義元**: `Lean.Parser.Tactic.showTerm` | **ソース**: Lean4 core

## 概要
`show_term` はタクティクブロックを実行し、生成された証明項（term）を Infoview に表示するタクティク。`by show_term { tac }` の形で使い、`tac` が成功した場合にその内部で構築された項を確認できる。タクティク証明を項証明に置き換えたい場合や、タクティクの内部動作を理解したい場合に有用。

## ゴールパターン

**適用前**（`show_term { exact h.symm }`）
```lean
h : a = b
⊢ b = a
```

**適用後**: ゴールが閉じる。Infoview に `Try this: exact h.symm` 等が表示される。

## 構文
```lean
show_term { tac }          -- tac を実行し、生成された証明項を表示
show_term { tac₁; tac₂ }  -- 複数タクティクの証明項を表示
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `{ tac }` | 表示したいタクティクブロック |

## Pros
- タクティクが生成する証明項を可視化できる
- 項証明への書き換え候補が得られる
- タクティクの挙動の理解・学習に役立つ

## Cons
- 生成される項が非常に大きくなる場合がある（`simp` 等）
- 表示された項がそのまま使えないこともある（メタ変数が残る等）
- デバッグ専用で、最終的には削除する

## コードサンプル

### サンプル 1: 基本的な使い方
```lean
example (a b : Nat) (h : a = b) : b = a := by
  show_term { exact h.symm }
  -- Infoview 出力: Try this: exact h.symm
```

### サンプル 2: omega の生成項を確認
```lean
example (n : Nat) : n + 0 = n := by
  show_term { omega }
  -- Infoview 出力: Try this: omega が生成した内部項が表示される
```

### サンプル 3: simp の生成項を確認
```lean
example (xs : List Nat) : (xs ++ []).length = xs.length := by
  show_term { simp }
  -- Infoview 出力: Try this: exact ... (simp が使った書き換え列)
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `trace_state` | 状態表示 | ゴール・仮定の確認 |
| `extract_goal` | ゴール抽出 | ゴールを独立定理として表示 |
| `decide` | 決定手続き | 生成項なしで命題を判定 |
| `type_check` | 型チェック | 式の型を確認 |

## 参照
- [Lean4 公式リファレンス — show_term](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
