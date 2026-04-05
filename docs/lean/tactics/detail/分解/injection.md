# `injection` — コンストラクタの単射性による等式分解

**カテゴリ**: 分解 | **定義元**: `Lean.Parser.Tactic.injection` | **ソース**: Lean4 core

## 概要
`injection` は帰納型のコンストラクタの単射性（injectivity）を利用して、等式を引数レベルの等式に分解する。例えば `Nat.succ a = Nat.succ b` から `a = b` を導出する。また、異なるコンストラクタ間の等式（例: `Nat.zero = Nat.succ n`）からは矛盾を直接導出できる。

## ゴールパターン

**適用前**（`injection h`）
```lean
h : List.cons a as = List.cons b bs
⊢ P
```

**適用後**
```lean
h : List.cons a as = List.cons b bs
⊢ a = b → as = bs → P
```

**適用前**（`injection h with h₁ h₂`）
```lean
h : List.cons a as = List.cons b bs
⊢ P
```

**適用後**
```lean
h₁ : a = b
h₂ : as = bs
⊢ P
```

## 構文
```lean
injection h                     -- 等式 h から引数の等式を導出
injection h with h₁ h₂          -- 導出された等式に名前を付ける
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `injection h` | 等式 h をコンストラクタの引数レベルに分解 |
| `with h₁ h₂ ...` | 導出された等式に明示的な名前を付ける |

## Pros
- コンストラクタの単射性を直接利用でき、等式の分解が明確
- 異なるコンストラクタ間の矛盾（`no confusion`）を自動導出
- 帰納型の等式証明において基本的かつ強力

## Cons
- コンストラクタの等式でない仮定には適用不可
- `with` を省略すると仮定名が自動生成され可読性が下がる
- `simp` や `omega` で十分な場面もあり、直接使う機会は限定的

## コードサンプル

### サンプル 1: Nat.succ の単射性
```lean
example (h : n + 1 = m + 1) : n = m := by
  injection h
  -- h₁ : n = m が導かれ、ゴールが自動的に閉じる
```

### サンプル 2: 異なるコンストラクタで矛盾
```lean
example (h : some a = none) : False := by
  injection h
  -- ゴールが自動的に閉じられる（no confusion）
```

### サンプル 3: List.cons の引数分解
```lean
example (h : x :: xs = y :: ys) : x = y ∧ xs = ys := by
  injection h with h₁ h₂
  -- h₁ : x = y, h₂ : xs = ys
  exact ⟨h₁, h₂⟩
```

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `injections` | `injection` を全仮定に再帰的に適用する |

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `cases` | 帰納型の場合分け | 等式でなく値自体を場合分けする場合 |
| `rcases` | 再帰的分解 | 仮定の構造的分解 |
| `congr` | 合同による等式分解 | ゴール側の等式を引数レベルに分解する場合 |

## 参照
- [Lean4 公式リファレンス — injection](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#injection)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
