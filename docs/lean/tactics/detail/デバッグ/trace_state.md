# `trace_state` — 現在の証明状態を表示

**カテゴリ**: デバッグ | **定義元**: `Lean.Parser.Tactic.traceState` | **ソース**: Lean4 core

## 概要
`trace_state` は現在の証明状態（全ゴールと仮定）を Lean Infoview にトレース出力するタクティク。証明の途中経過を確認するために使う。通常は VS Code のカーソル位置で Infoview が状態を表示するが、`trace_state` を使うとその時点の状態を明示的にログに残せる。証明の進行を段階的に確認したい場合に有用。

## ゴールパターン

**適用前**
```lean
h : P
⊢ Q
```

**適用後**（ゴールは変化しない）
```lean
h : P
⊢ Q
-- Infoview / メッセージに現在の状態が表示される
```

## 構文
```lean
trace_state               -- 現在の全ゴール・仮定を表示
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
なし。`trace_state` は引数を取らない。

## Pros
- 証明状態を明示的にログに残せる
- 複雑なタクティク列の途中でデバッグに使える
- ゴールや仮定を変更しないため安全に挿入できる

## Cons
- VS Code の Infoview があれば通常は不要
- 出力がメッセージログに残るので最終的には削除すべき
- CI/CD 環境ではログが冗長になる

## コードサンプル

### サンプル 1: 基本的な使い方
```lean
example (a b : Nat) (h : a = b) : b = a := by
  trace_state
  -- ゴール表示: a b : Nat, h : a = b ⊢ b = a
  exact h.symm
```

### サンプル 2: タクティク間に挿入して変化を追跡
```lean
example (n : Nat) : n + 0 = 0 + n := by
  trace_state
  -- ⊢ n + 0 = 0 + n
  simp [Nat.add_zero, Nat.zero_add]
  trace_state
  -- ゴールなし（閉じた場合は表示なし）
```

### サンプル 3: 複数ゴールの確認
```lean
example (h : P ∧ Q) : Q ∧ P := by
  constructor
  trace_state
  -- case left: h : P ∧ Q ⊢ Q
  -- case right: h : P ∧ Q ⊢ P
  · exact h.2
  · exact h.1
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `sorry` | プレースホルダ | ゴール確認後に仮閉じ |
| `extract_goal` | ゴール抽出 | 現在のゴールを独立定理として出力 |
| `show_term` | 項表示 | 生成される証明項を確認 |
| `type_check` | 型チェック | 式の型を確認 |

## 参照
- [Lean4 公式リファレンス — trace_state](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
