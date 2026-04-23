# `try` — タクティクを試行し、失敗しても成功扱いにする

**カテゴリ**: 制御 | **定義元**: `Lean.Parser.Tactic.tacticTry_` | **ソース**: Lean4 core

## 概要
`try` は後続のタクティクを実行し、成功すればその効果を適用し、失敗した場合は何も起きなかったものとして成功を返す。つまり「やれたらやる」というセマンティクスを持つ。オートメーション系のタクティク列で、特定のステップが適用できない場合にもエラーにしたくないときに使う。

## ゴールパターン

**適用前**（`try simp` — simp が成功する場合）
```lean
⊢ 0 + n = n
```

**適用後**
```lean
-- ゴールが閉じる（simp が成功）
```

**適用前**（`try simp` — simp が失敗する場合）
```lean
⊢ P
```

**適用後**
```lean
⊢ P
-- ゴールは変化しない（失敗が無視される）
```

## 構文
```lean
try tac          -- tac を試行。失敗しても成功扱い
try tac1; tac2   -- tac1; tac2 の列を試行
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `try tac` | tac が失敗しても状態を巻き戻して成功を返す |

## Pros
- オートメーション列の途中で安全にタクティクを試せる
- `repeat` や `all_goals` と組み合わせて堅牢なスクリプトが書ける
- 条件付きで効く最適化タクティクを気軽に挿入できる

## Cons
- 失敗が隠蔽されるため、デバッグ時にバグの原因が分かりにくくなる
- `try` の多用はタクティク列の意図を不明瞭にする
- 副作用のない失敗と、予期しない失敗を区別できない

## コードサンプル

### サンプル 1: simp が効かなくても続行
```lean
example (n m : Nat) (h : n = m + 1) : n > m := by
  try simp  -- simp は n > m を証明できないが失敗してもよい
  -- ⊢ n > m
  omega  -- omega で閉じる
```

### サンプル 2: repeat と組み合わせて複数ゴールを処理
```lean
example (a b : Nat) (h : a = b) : a = b ∧ a = b := by
  constructor
  -- ゴール 1: ⊢ a = b
  -- ゴール 2: ⊢ a = b
  all_goals try assumption
  -- h で両ゴールが閉じる
```

### サンプル 3: first の簡易代替として
```lean
example (n : Nat) (h : n = 0) : n + 0 = 0 := by
  try rw [Nat.add_zero]
  -- ⊢ n = 0
  try exact h
  -- ゴールが閉じる
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `first` | 複数タクティクの試行 | 複数候補から1つ成功させたいなら `first` |
| `repeat` | 繰り返し | 失敗まで繰り返す場合は `repeat` |
| `solve` | 完全解決の試行 | ゴールを完全に閉じることが条件なら `solve` |

## 参照
- [Lean4 公式リファレンス — try](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
