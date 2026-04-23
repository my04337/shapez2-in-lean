# `sorry` — 未完了の証明プレースホルダ

**カテゴリ**: デバッグ | **定義元**: `Lean.Parser.Tactic.tacticSorry` | **ソース**: Lean4 core

## 概要
`sorry` は任意のゴールを無条件に閉じるタクティク。証明が未完了であることを示すプレースホルダとして使う。`sorry` を含む定理は公理的に健全ではなく、コンパイル時に警告が出力される。開発中の段階的証明構築、証明スケッチの作成、型チェックの確認に利用する。

## ゴールパターン

**適用前**（任意のゴール）
```lean
⊢ P
```

**適用後**: ゴールが閉じる（警告付き）

## 構文
```lean
sorry                     -- 現在のゴールを閉じる（警告あり）
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
なし。`sorry` は引数を取らない。

## Pros
- 任意のゴールを即座に閉じられるため、証明の骨格を先に構築できる
- 型チェックを通しながら段階的に証明を完成させられる
- 依存する定理の型シグネチャを先に確定できる

## Cons
- `sorry` を含む証明は健全ではない（偽の命題も証明できてしまう）
- 警告が出るため、最終的には全て解消する必要がある
- `sorry` に依存する他の定理も信頼できなくなる

## コードサンプル

### サンプル 1: 証明骨格の構築
```lean
theorem my_theorem (n : Nat) : n + 0 = n := by
  sorry
  -- declaration uses 'sorry' 警告が表示される
```

### サンプル 2: 段階的な証明（一部を sorry で残す）
```lean
theorem and_comm_example (h : P ∧ Q) : Q ∧ P := by
  constructor
  · -- ⊢ Q
    exact h.2
  · -- ⊢ P
    sorry  -- TODO: h.1 で閉じる
```

### サンプル 3: 項レベルの sorry
```lean
def myFunction (n : Nat) : String :=
  if n = 0 then "zero"
  else sorry  -- TODO: 実装する
  -- ⊢ String （項レベルでも sorry は使える）
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `admit` | sorry の別名 | 同じ意味（Lean4 では `sorry` を使う） |
| `trace_state` | 状態表示 | sorry の前にゴールを確認 |
| `extract_goal` | ゴール抽出 | sorry のゴールを独立定理として抽出 |
| `show_term` | 項表示 | 生成される証明項を確認 |

## 参照
- [Lean4 公式リファレンス — sorry](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#sorry)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
