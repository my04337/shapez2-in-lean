# `itauto` — 直観主義命題論理の完全決定手続き

**カテゴリ**: 論理 | **定義元**: `Mathlib.Tactic.ITauto.itauto` | **ソース**: Mathlib

## 概要
`itauto` は直観主義命題論理（`∧`, `∨`, `→`, `↔`, `¬`, `True`, `False`）の完全な決定手続き。`tauto` と似ているが、内部実装が異なり、直観主義論理での妥当性を厳密に判定する。バリアント `itauto!` は古典論理に拡張し、SAT ソルバ的なアプローチで排中律を含む命題も処理する。

## ゴールパターン

**適用前**
```lean
⊢ 命題論理の式  -- ∧, ∨, →, ↔, ¬, True, False の組み合わせ
```

**適用後**: ゴールが閉じる（妥当でない場合は失敗）

## 構文
```lean
itauto                   -- 直観主義命題論理で判定
itauto!                  -- 古典論理に拡張（排中律を使用）
```

## 必須 import
```lean
import Mathlib.Tactic.ITauto
```

## Pros
- 直観主義命題論理に対して**完全**（妥当な式は必ず証明できる）
- `tauto` では閉じない微妙なケースを処理できることがある
- `itauto!` で古典論理にシームレスに切り替え可能
- 生成される証明項が比較的小さい

## Cons
- Mathlib import が必要
- 述語論理（全称・存在量化子）は扱えない
- 命題変数の数が多いと指数的に遅くなる可能性がある
- `tauto` や `aesop` で十分な場合はそちらが一般的に使われる

## コードサンプル

### サンプル 1: 直観主義論理で Peirce の法則の弱形
```lean
-- ⊢ ¬¬(P ∨ ¬P)
-- 直観主義論理でも二重否定排中律は証明可能
example : ¬¬(P ∨ ¬P) := by itauto
```

### サンプル 2: itauto! で古典論理の命題を証明
```lean
-- ⊢ ((P → Q) → P) → P
-- Peirce の法則: 古典論理でのみ成立
example (P Q : Prop) : ((P → Q) → P) → P := by tauto
```

### サンプル 3: 複雑な含意のチェイン
```lean
-- h₁ : P → Q, h₂ : Q → R, h₃ : R → S
-- ⊢ P → S
example (P Q R S : Prop) (h₁ : P → Q) (h₂ : Q → R) (h₃ : R → S) : P → S := by tauto
```

## `tauto` との比較

| 観点 | `tauto` | `itauto` |
|---|---|---|
| 基本論理 | 古典（排中律を使う） | 直観主義（デフォルト） |
| 古典拡張 | デフォルトで古典 | `itauto!` で明示的に拡張 |
| 完全性 | 命題論理で完全 | 直観主義命題論理で完全 |
| 実装 | Lean/Mathlib タクティク | 専用の判定アルゴリズム |
| 証明項サイズ | やや大きい場合あり | 比較的小さい |

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `itauto!` | 古典論理も含めて探索する強化版 |

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `tauto` | 命題論理 | 古典論理がデフォルトで十分な場合 |
| `aesop` | 汎用探索 | 命題論理を超える自動化が必要な場合 |
| `decide` | 決定手続き | `Decidable` な具体的命題 |
| `omega` | 算術 | 算術を含む場合 |
| `grind` | SMT ベース | より強力な自動化が必要な場合 |

## 参照
- [Mathlib4 ドキュメント — ITauto](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/ITauto.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
