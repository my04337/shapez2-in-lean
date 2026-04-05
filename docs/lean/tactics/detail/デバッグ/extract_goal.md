# `extract_goal` — 現在のゴールを独立定理として抽出

**カテゴリ**: デバッグ | **定義元**: `Mathlib.Tactic.extractGoalTac` | **ソース**: Mathlib

## 概要
`extract_goal` は現在のゴールを独立した定理ステートメントとして Infoview に表示するタクティク。複雑な証明の途中で「今証明しようとしていること」を明確にしたい場合や、ゴールを別の補題として切り出したい場合に使う。表示される定理は仮定を引数として含む完全な型シグネチャになる。

## ゴールパターン

**適用前**（任意のゴール）
```lean
a b : Nat
h : a ≤ b
⊢ a + (b - a) = b
```

**適用後**（ゴールは変化しない。Infoview に以下が出力される）
```
theorem extracted_1 (a b : Nat) (h : a ≤ b) : a + (b - a) = b := by
  sorry
```

## 構文
```lean
extract_goal              -- 現在のゴールを定理として抽出
extract_goal myName       -- 定理名を指定
```

## 必須 import
```lean
import Mathlib.Tactic.ExtractGoal
```

## オプション一覧
| 構文 | 意味 |
|---|---|
| `extract_goal` | デフォルト名 `extracted_N` で出力 |
| `extract_goal name` | 指定した名前で出力 |

## Pros
- 証明の途中ゴールを独立補題として明示できる
- 抽出された定理をコピーして実際の補題として利用できる
- sorry 箇所のゴールを正確に把握するのに便利

## Cons
- Mathlib 依存
- 証明に影響を与えないため、最終的には削除する
- ローカル定義がある場合、抽出された定理の引数が多くなる

## コードサンプル

### サンプル 1: 基本的なゴール抽出
```lean
import Mathlib.Tactic.ExtractGoal

example (n : Nat) (h : n > 0) : n ≥ 1 := by
  extract_goal
  -- Infoview 出力:
  -- theorem extracted_1 (n : Nat) (h : n > 0) : n ≥ 1 := by sorry
  omega
```

### サンプル 2: 名前を指定して抽出
```lean
import Mathlib.Tactic.ExtractGoal

example (a b : Nat) : a + b = b + a := by
  extract_goal
  -- Infoview 出力:
  -- theorem extracted_1 (a b : Nat) : a + b = b + a := by sorry
  omega
```

### サンプル 3: 複雑な証明の途中で使う
```lean
import Mathlib.Tactic.ExtractGoal

example (xs : List Nat) (h : xs.length > 0) : xs ≠ [] := by
  intro heq
  extract_goal
  -- Infoview 出力: heq を含む完全なステートメントが表示される
  simp [heq] at h
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `trace_state` | 状態表示 | 全仮定とゴールの一覧を見たい場合 |
| `sorry` | プレースホルダ | ゴール確認後に仮閉じ |
| `show_term` | 項表示 | 生成される証明項を確認 |
| `have` | 補題導入 | 抽出した補題を実際に使う |

## 参照
- [Mathlib4 ドキュメント — ExtractGoal](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/ExtractGoal.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
