# `iterate` — タクティクを指定回数だけ繰り返す

**カテゴリ**: 制御 | **定義元**: `Lean.Parser.Tactic.tacticIterate____` | **ソース**: Lean4 core

## 概要
`iterate` は指定した回数だけタクティクを繰り返し適用する。回数を省略した場合は `repeat` と同じく失敗するまで繰り返す。`repeat` と異なり、回数を明示している場合は途中で失敗するとエラーになる。繰り返し回数が分かっているときに使うことで、意図を明示しつつ安全にスクリプトを書ける。

## ゴールパターン

**適用前**（`iterate 3 apply And.intro`）
```lean
⊢ A ∧ B ∧ C ∧ D
```

**適用後**
```lean
⊢ A
⊢ B
⊢ C
⊢ D
```

## 構文
```lean
iterate n tac     -- tac を正確に n 回適用。途中失敗でエラー
iterate tac       -- repeat と同等。失敗まで繰り返す
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `iterate n tac` | tac を n 回適用（n 回未満で失敗するとエラー） |
| `iterate tac` | tac を失敗まで繰り返す（`repeat` と同等） |

## Pros
- 繰り返し回数を明示でき、スクリプトの意図が分かりやすい
- 回数指定時は期待通りの回数適用されないとエラーになるため安全
- `repeat` より厳密な制御が可能

## Cons
- 回数が固定されるため、型の構造が変わると壊れやすい
- 回数を省略すると `repeat` と同じで無限ループのリスクがある
- `repeat` の方が Lean コミュニティではよく見かけるため、可読性で劣る場合がある

## コードサンプル

### サンプル 1: 正確に n 回の適用
```lean
example (ha : A) (hb : B) (hc : C) : (A ∧ B) ∧ C := by
  iterate 2 apply And.intro
  -- (A ∧ B) ∧ C → 2回分解: (A ∧ B) → A と B
  -- ⊢ A
  -- ⊢ B
  -- ⊢ C
  · exact ha
  · exact hb
  · exact hc
```

### サンプル 2: intro を指定回数
```lean
example : P → Q → R → P := by
  iterate 3 intro _
  -- 3回 intro して仮定を導入
  -- ⊢ P
  assumption
```

### サンプル 3: 回数省略で失敗まで繰り返し
```lean
example : P → Q → R → R := by
  iterate intro
  -- 失敗するまで intro を繰り返す（3回適用される）
  -- hp : P, hq : Q, hr : R ⊢ R
  assumption
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `repeat` | 失敗まで繰り返し | 回数不明なら `repeat` |
| `try` | 1回の試行 | 1回だけ試すなら `try` |
| `all_goals` | 全ゴール適用 | ゴール数だけ繰り返すなら `all_goals` |

## 参照
- [Lean4 公式リファレンス — iterate](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
