# `run_tac` — TacticM コードの直接実行

**カテゴリ**: 制御 | **定義元**: `Lean.Parser.Tactic.runTac` | **ソース**: Lean4 core

---

## 概要

`run_tac` はタクティクモード内で `TacticM Unit` 型の do ブロックを直接実行するタクティクである。
メタプログラミングでカスタムタクティクを定義せずにその場で `TacticM` のコードを書いて実行できる。
ゴールの検査、仮定の操作、メタ変数の操作などを `Lean.Elab.Tactic` API を直接呼び出して行える。
デバッグやプロトタイピングに有用だが、本番コードではカスタムタクティクの定義が望ましい。

---

## ゴールパターン

**適用対象**: 任意（実行するコード次第）

**適用前**
```lean
⊢ P
```

**適用後**
```lean
-- 実行した TacticM コードの結果に依存
```

---

## 構文

```lean
run_tac do
  <TacticM code>

run_tac <expr>     -- TacticM Unit 型の式
```

---

## 必須 import

Lean4 core 組み込みのため不要。ただし `Lean.Elab.Tactic` 系の API を使う場合は適宜 import が必要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `run_tac do ...` | do ブロック内の `TacticM` コードを実行 |
| `run_tac expr` | `TacticM Unit` 型の式を実行 |

---

## Pros（使うべき場面）

- カスタムタクティクを定義せずにメタプログラミングを即座に試せる
- ゴールや仮定の内部構造をプログラム的に検査・操作できる
- プロトタイピングやデバッグに便利

---

## Cons（注意・失敗ケース）

- 可読性が低く、メンテナンスが困難
- 本番コードではカスタムタクティクとして `elab` で定義すべき
- `TacticM` API の知識が必要で、学習コストが高い

---

## コードサンプル

### サンプル 1: ゴールの表示

```lean
import Lean

example : 1 + 1 = 2 := by
  -- ⊢ 1 + 1 = 2
  run_tac do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalType ← goal.getType
    Lean.logInfo m!"Goal type: {goalType}"
  -- ゴールの型がメッセージとして表示される
  rfl
```

### サンプル 2: 仮定の列挙

```lean
import Lean

example (a b : Nat) (h : a = b) : b = a := by
  -- ⊢ b = a
  run_tac do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let ctx ← goal.getDecl
    for decl in ctx.lctx do
      if !decl.isImplementationDetail then
        Lean.logInfo m!"{decl.userName} : {decl.type}"
  -- 仮定が表示される
  omega
```

### サンプル 3: evalTactic でタクティクを動的実行

```lean
import Lean

example : True := by
  -- ⊢ True
  run_tac do
    Lean.Elab.Tactic.evalTactic (← `(tactic| trivial))
  -- ゴールなし（証明完了）
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `decide` | 自動判定 | 決定可能な命題の自動証明。メタプログラミング不要 |
| `native_decide` | ネイティブ判定 | ネイティブコード実行による判定 |
| `norm_num` | 数値正規化 | 数値計算の自動化。`run_tac` より高水準 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Lean4 メタプログラミングブック](https://leanprover-community.github.io/lean4-metaprogramming-book/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
