# `tauto` — 命題論理のトートロジー証明

**カテゴリ**: 論理 | **定義元**: `Mathlib.Tactic.Tauto.tauto` | **ソース**: Mathlib

## 概要
`tauto` は命題論理のトートロジー（`∧`, `∨`, `→`, `↔`, `¬`, `True`, `False`）を自動証明する。`decide` とは異なり、命題変数が具体的でなくても動作する。古典論理（排中律）も扱う。

## ゴールパターン

**適用前**
```lean
⊢ P ∨ ¬P
```

**適用後**: ゴールが閉じる

## 構文
```lean
tauto                   -- 命題論理で自動証明
```

## 必須 import
```lean
import Mathlib.Tactic.Tauto
```

## Pros
- 命題論理のトートロジーを一発で閉じる
- 排中律を含む古典論理も対応
- `∧`, `∨`, `→`, `↔`, `¬`, `True`, `False`, `∃` (命題レベル) を処理

## Cons
- 述語論理（量化子を含む複雑な論理）は扱えない場合がある
- `aesop` や `grind` の方が強い場面もある
- Mathlib import が必要

## コードサンプル

### サンプル 1: 排中律
```lean
example : P ∨ ¬P := by tauto
```

### サンプル 2: 含意のチェイン
```lean
example (h₁ : P → Q) (h₂ : Q → R) : P → R := by tauto
```

### サンプル 3: De Morgan
```lean
example : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := by tauto
```

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `aesop` | 汎用証明探索 | 命題論理以外も含む場合 |
| `decide` | 決定手続き | Decidable な具体的命題 |
| `omega` | 算術 | 算術を含む場合 |
| `simp` | 簡約 | 論理式を簡約で済む場合 |
| `contradiction` | 矛盾 | 仮定に矛盾がある場合 |

## 参照
- [Mathlib4 ドキュメント — Tauto](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Tauto.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
