# `ext` / `funext` — 外延性による等式証明

**カテゴリ**: 構造 | **定義元**: `Lean.Parser.Tactic.ext` / `Lean.Parser.Tactic.funext` | **ソース**: Lean4 core

## 概要
`ext` は構造体や関数の等式を、成分ごとの等式に分解する。`funext` は関数の等式 `f = g` を `∀ x, f x = g x` に帰着する。`@[ext]` 属性で拡張可能。

## ゴールパターン

**適用前** (`funext`)
```lean
f g : Nat → Int
⊢ f = g
```

**適用後**
```lean
x : Nat
⊢ f x = g x
```

**適用前** (`ext`)
```lean
⊢ p = q  -- (p q : α × β)
```

**適用後**
```lean
-- ゴール 1: ⊢ p.1 = q.1
-- ゴール 2: ⊢ p.2 = q.2
```

## 構文
```lean
funext x                -- 関数外延性: x を導入
funext x y              -- 複数引数を導入
ext                     -- @[ext] 補題を適用
ext x                   -- 変数名を指定
ext ⟨a, b⟩             -- パターンで分解
```

## 必須 import
Lean4 core 組み込み。Mathlib の @[ext] 補題を使う場合は対応する import。

## Pros
- 関数の等式証明で最初に使うべきタクティク
- 構造体の等式を成分ごとに分解できる
- `@[ext]` 属性で任意の型に拡張可能

## Cons
- `@[ext]` 補題がない型では使えない
- 外延的に等しくない場合は証明不可能に（方向が合っているか確認が必要）
- `funext` は dependent functions に対して注意が必要

## コードサンプル

### サンプル 1: 関数の等式
```lean
example : (fun n : Nat => n + 0) = (fun n => n) := by
  funext n
  simp
```

### サンプル 2: 構造体の等式
```lean
example (p q : Nat × Int) (h1 : p.1 = q.1) (h2 : p.2 = q.2) : p = q := by
  ext
  · exact h1
  · exact h2
```

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `congr` | 構造分解 | 関数適用の等式を引数の等式に分解 |
| `simp` | 簡約 | 外延性より簡約で済む場合 |
| `subst` | 変数消去 | 等式仮定で変数を代入 |

## 参照
- [Lean4 公式リファレンス — ext](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#funext)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
