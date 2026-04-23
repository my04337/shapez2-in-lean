# `rcases` — 再帰的ケース分解

**カテゴリ**: 分解 | **定義元**: `Lean.Parser.Tactic.rcases` | **ソース**: Lean4 core (Batteries)

## 概要
`rcases` は帰納型の値を再帰的にパターンマッチで分解する。`cases` の強化版で、ネストした角括弧パターン `⟨a, b⟩` やパイプ `a | b` を使った深い分解が一度に書ける。`And`, `Exists`, `Or` などの分解に頻繁に使われる。

## ゴールパターン

**適用前**
```lean
h : P ∧ (Q ∨ R)
⊢ S
```

**適用後**（`rcases h with ⟨hp, hq | hr⟩`）
```lean
-- ゴール 1:
hp : P
hq : Q
⊢ S

-- ゴール 2:
hp : P
hr : R
⊢ S
```

## 構文
```lean
rcases h with ⟨a, b⟩          -- 積（∧, Sigma等）の分解
rcases h with a | b            -- 和（∨, Sum等）の分解
rcases h with ⟨a, b | c⟩      -- ネスト分解
rcases h with ⟨⟨a, b⟩, c⟩    -- 深いネスト
rcases h with rfl              -- 等式の場合は即代入
rcases h with _                -- 名前をつけず破棄
rcases h with ⟨a, -, b⟩       -- 要素をスキップ
```

## 必須 import
Lean4 core / Batteries 組み込み。追加 import なし。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `⟨a, b⟩` | 積型を分解 |
| `a \| b` | 和型を分解（各ケース） |
| `rfl` | 等式仮定を即座に代入 |
| `_` | 名前を付けず匿名化 |
| `-` | フィールドを破棄 |

## Pros（使うべき場面）
- 深くネストした構造（∧/∨/∃ の組み合わせ）を1行で分解可能
- パターン記法が直感的で可読性が高い
- `rfl` パターンで等式の代入を同時に行える

## Cons（注意・失敗ケース）
- 仮定の型がパターンに合わないとエラー
- 帰納型のフィールド数とパターンが不一致だとエラー
- 非常に複雑なパターンは可読性が落ちる → `obtain` で型注釈を付けた方がよいことも

## コードサンプル

### サンプル 1: And の分解
```lean
example (h : P ∧ Q) : P := by
  rcases h with ⟨hp, _⟩
  exact hp
```

### サンプル 2: Or の分解
```lean
example (h : P ∨ Q) : Q ∨ P := by
  rcases h with hp | hq
  · right; exact hp
  · left; exact hq
```

### サンプル 3: Exists の分解
```lean
example {α : Type*} {P Q : α → Prop} (h : ∃ x, P x ∧ Q x) : ∃ x, Q x := by
  rcases h with ⟨x, _, hq⟩
  exact ⟨x, hq⟩
```

### サンプル 4: rfl パターン
```lean
example {P : Nat → Prop} (h : ∃ x, x = 5 ∧ P x) : P 5 := by
  rcases h with ⟨_, rfl, hp⟩
  exact hp
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `obtain` | `have` + `rcases` | 型注釈を付けて分解したい場合。`obtain ⟨a, b⟩ : T := proof` |
| `rintro` | `intro` + `rcases` | 仮定を導入しながら即座に分解 |
| `cases` | 基本のケース分解 | `with` 節で各ケースを `\| con => tac` で扱う |
| `match` | パターンマッチ | タームモードでの場合分け |

## 参照
- [Lean4 公式リファレンス — rcases](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#rcases)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。