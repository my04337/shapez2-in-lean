# `cases` / `induction` — ケース分析・帰納法

**カテゴリ**: 分解 | **定義元**: `Lean.Parser.Tactic.cases` / `Lean.Parser.Tactic.induction` | **ソース**: Lean4 core

## 概要
`cases` は帰納型の値をコンストラクタごとに場合分けする。`induction` は帰納法の仮説を伴う場合分けを行う。`with` 節で各ケースに名前を付け、個別にタクティクを適用する。

## ゴールパターン

**適用前** (`cases n`)
```lean
n : Nat
⊢ P n
```

**適用後**
```lean
-- ケース 1: ⊢ P 0
-- ケース 2: (n✝ : Nat) ⊢ P (n✝ + 1)
```

**適用前** (`induction n`)
```lean
n : Nat
⊢ P n
```

**適用後**
```lean
-- ケース zero: ⊢ P 0
-- ケース succ: (n✝ : Nat), (ih : P n✝) ⊢ P (n✝ + 1)
```

## 構文
```lean
cases h                             -- h を場合分け
cases h with                        -- with 節で各ケースに名前
  | none => tac₁
  | some val => tac₂
induction n with                    -- 帰納法
  | zero => tac₁
  | succ n ih => tac₂
cases h : x                        -- h に等式を保存
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `with \| con args => tac` | 各コンストラクタの名前とタクティクを指定 |
| `h : x` | `x` に関する等式を仮定 `h` に保存 |
| `generalizing x` | induction の前に x を一般化 |

## Pros
- Lean4 のネイティブ場合分けで最も基本的
- `with` 節で名前付けが明確で可読性が高い
- `induction` は帰納法の仮説を自動生成

## Cons
- 深いネスト分解は `rcases` / `obtain` の方が簡潔
- `cases` はパターンの再帰的分解ができない（1段ずつ）
- 帰納法の仮説の一般化を忘れると弱い仮説になる（`generalizing` が必要）

## コードサンプル

### サンプル 1: Option の場合分け
```lean
example (o : Option Nat) : o = none ∨ ∃ n, o = some n := by
  cases o with
  | none => left; rfl
  | some n => right; exact ⟨n, rfl⟩
```

### サンプル 2: Nat の帰納法
```lean
theorem add_zero (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.succ_add, ih]
```

### サンプル 3: cases h で等式保存
```lean
example (h : n < 2) : n = 0 ∨ n = 1 := by
  cases n with
  | zero => left; rfl
  | succ n => right; omega
```

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `cases'` | Lean 3 互換の cases（Mathlib） |
| `cases_type` | 指定型の仮定を自動で cases する |
| `cases_type!` | `cases_type` を再帰的に適用する |
| `casesm` | パターンに一致する仮定を cases する |
| `casesm!` | `casesm` を再帰的に適用する |

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `rcases` | 再帰的分解 | ネストした分解を一行で |
| `match` | パターンマッチ | タームモードでの場合分け |
| `split` | if/match分割 | ゴールのif/matchを分割 |
| `omega` | 算術 | Nat場合分け後の不等式処理 |

## 参照
- [Lean4 公式リファレンス — cases/induction](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#tactic-ref-inductive)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
