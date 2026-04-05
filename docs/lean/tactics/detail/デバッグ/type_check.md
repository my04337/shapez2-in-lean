# `type_check` — 式の型チェックとトレース出力

**カテゴリ**: デバッグ | **定義元**: `tacticType_check_` | **ソース**: Lean4 core

## 概要
`type_check` は与えられた式を型チェックし、その型を Infoview にトレース出力するタクティク。式が well-typed かどうかの確認や、複雑な式の推論された型を知りたい場合に使う。ゴールは変化しない。`#check` コマンドのタクティク版として利用できる。

## ゴールパターン

**適用前**（`type_check Nat.add_comm`）
```lean
⊢ P
```

**適用後**（ゴールは変化しない。Infoview に型が表示される）
```lean
⊢ P
-- Infoview: Nat.add_comm : ∀ (n m : Nat), n + m = m + n
```

## 構文
```lean
type_check expr            -- expr の型をチェックしてトレース出力
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `type_check expr` | 式 expr の型をチェックして Infoview に表示 |

## Pros
- 証明の途中で式の型を確認できる
- ゴールを変えずに安全に使える
- `#check` が使えないタクティクブロック内で代替手段になる

## Cons
- デバッグ専用で、最終的には削除する
- 式がエラーの場合はエラーメッセージが出る
- VS Code の Infoview でホバーすれば型が見えるため、多くの場合は不要

## コードサンプル

### サンプル 1: 補題の型を確認
```lean
example (n m : Nat) : n + m = m + n := by
  type_check Nat.add_comm
  -- Infoview: Nat.add_comm : ∀ (n m : Nat), n + m = m + n
  exact Nat.add_comm n m
```

### サンプル 2: 仮定の型を確認
```lean
example (h : ∀ x : Nat, x > 0 → x ≥ 1) : 5 ≥ 1 := by
  type_check h 5
  -- Infoview: h 5 : 5 > 0 → 5 ≥ 1
  exact h 5 (by omega)
```

### サンプル 3: 複雑な式の推論型を確認
```lean
example (xs : List Nat) : xs.length ≥ 0 := by
  type_check xs.length
  -- Infoview: xs.length : Nat
  omega
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `trace_state` | 状態表示 | ゴール・仮定の全体を確認 |
| `show_term` | 項表示 | タクティクの生成項を確認 |
| `extract_goal` | ゴール抽出 | ゴールを独立定理として表示 |
| `#check` | コマンド | タクティクブロック外で型を確認 |

## 参照
- [Lean4 公式リファレンス — type_check](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
