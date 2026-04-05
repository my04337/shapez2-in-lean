# `solve` — ゴールを完全に閉じるタクティクだけを受け入れる

**カテゴリ**: 制御 | **定義元**: `Lean.solveTactic` | **ソース**: Lean4 core

## 概要
`solve` は `first` と似た構文で複数のタクティクを `|` 区切りで試行するが、**ゴールを完全に閉じた場合にのみ成功**とみなす。タクティクが部分的にゴールを変形しただけの場合は失敗扱いとなりロールバックされる。オートメーションで「閉じられるなら閉じる、無理なら何もしない」というパターンを安全に書きたい場合に使う。

## ゴールパターン

**適用前**（`solve | simp | omega`）
```lean
⊢ 0 + n = n
```

**適用後**（simp が完全に閉じた場合）
```lean
-- ゴール完了
```

**適用前**（どのタクティクも閉じられない場合）
```lean
⊢ P
```

**適用後**
```lean
-- エラー: 全候補がゴールを閉鎖できなかった
```

## 構文
```lean
solve | tac1 | tac2           -- tac1, tac2 を順に試行（閉鎖必須）
solve | tac1 | tac2 | tac3    -- 3つ以上も可
solve
  | tac1
  | tac2                      -- 改行スタイル
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `solve \| tac` | tac でゴールを完全に閉鎖（残ればロールバック） |

## Pros
- 部分的な変形を防ぎ、「完全に閉じるか何もしないか」を保証
- `first` + `done` を1つにまとめたセマンティクス
- オートメーションスクリプトの安全性を高める

## Cons
- ゴールを完全に閉じなければ成功しないため、段階的処理には使えない
- 部分的な進捗を許容したい場合は `first` を使う必要がある
- エラーメッセージが `first` と似ているため混同しやすい

## コードサンプル

### サンプル 1: 基本的な使い方
```lean
example (n : Nat) : n + 0 = n := by
  solve | rfl | simp | omega
  -- simp が成功してゴールが完全に閉じる
```

### サンプル 2: 閉じられない場合は失敗
```lean
-- 以下はエラーになる（rw はゴールを閉じない）
-- example (n : Nat) : n + 0 = 0 + n := by
--   solve | rw [Nat.add_zero]
--   -- rw は ⊢ n = 0 + n に変形するが閉鎖しないため失敗
```

### サンプル 3: all_goals と組み合わせて各ゴールを完全処理
```lean
example (a b : Nat) : a + 0 = a ∧ 0 + b = b := by
  constructor
  -- ゴール 1: ⊢ a + 0 = a
  -- ゴール 2: ⊢ 0 + b = b
  all_goals solve | simp | omega
  -- 両ゴールが完全に閉じる
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `first` | 部分的成功も許容 | ゴール変形だけでも成功にするなら `first` |
| `done` | 完了チェック | 特定の位置で全ゴール完了を確認するなら `done` |
| `try` | 失敗の無視 | 失敗を無視したいなら `try` |
| `decide` | 決定可能なゴール | 可判定問題を自動閉鎖するなら `decide` |

## 参照
- [Lean4 公式リファレンス — solve](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
