# `<;>` — 直前のタクティクが生成した全サブゴールに適用

**カテゴリ**: 制御 | **定義元**: `Lean.Parser.Tactic.«tactic_<;>_»` | **ソース**: Lean4 core

## 概要
`<;>` は左辺のタクティクを実行した後、それによって生成された**すべてのサブゴール**に右辺のタクティクを適用するコンビネータ。`all_goals` と似ているが、`<;>` は直前の1タクティクが生成したゴールだけを対象とする点が異なる。`cases` や `constructor` の直後に共通処理を1行で書きたい場合に頻用される。

## ゴールパターン

**適用前**（`constructor <;> simp`）
```lean
⊢ A ∧ B
```

**適用後**（simp が両サブゴールを閉じた場合）
```lean
-- ゴール完了
```

## 構文
```lean
tac1 <;> tac2           -- tac1 の全サブゴールに tac2 を適用
tac1 <;> (tac2; tac3)   -- 括弧でタクティク列を渡す
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `tac1 <;> tac2` | tac1 で分岐した全ゴールに tac2 を適用。1つでも失敗すると全体失敗 |

## Pros
- 分岐後の共通処理を1行で簡潔に書ける
- セミコロンによるタクティク列とは異なるスコープ制御が可能
- `cases ... <;> simp` のようなイディオムは非常に頻出する

## Cons
- すべてのサブゴールで成功する必要がある（`all_goals` と同じ）
- 部分的成功を許容したい場合は `<;> try tac` を使う必要がある
- 左辺タクティクのサブゴールのみ対象のため、既存ゴールには影響しない

## コードサンプル

### サンプル 1: cases と組み合わせて一括処理
```lean
example (b : Bool) : (b || true) = true := by
  cases b <;> rfl
  -- false || true = true と true || true = true の両方が rfl で閉じる
```

### サンプル 2: constructor 後に simp
```lean
example (n : Nat) : n + 0 = n ∧ 0 + n = n := by
  constructor <;> simp
  -- 両サブゴールが simp で閉じる
```

### サンプル 3: try と組み合わせて部分的成功
```lean
example (a : Nat) (h : a = 1) : a = 1 ∧ 1 + 1 = 2 := by
  constructor <;> try assumption
  -- ゴール 1 (a = 1) は assumption で閉じる
  -- ゴール 2 (1 + 1 = 2) は assumption 失敗 → try で無視
  -- 残り: ⊢ 1 + 1 = 2
  rfl
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `all_goals` | 全ゴールに適用 | 既存の全ゴールに適用するなら `all_goals` |
| `;`（セミコロン） | タクティク列 | 逐次実行なら `;`。`<;>` は分配的に全サブゴールへ適用 |
| `any_goals` | 部分的成功 | 一部成功で十分なら `any_goals` |
| `focus` | 単一ゴール | 1つだけに集中するなら `focus` |

## 参照
- [Lean4 公式リファレンス — <;>](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
