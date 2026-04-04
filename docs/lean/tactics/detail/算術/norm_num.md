# `norm_num` — 数値式の計算・正規化

**カテゴリ**: 算術 | **定義元**: `Mathlib.Tactic.NormNum.normNum` | **ソース**: Mathlib

## 概要
`norm_num` は数値リテラルを含む式を計算・正規化する。`2 + 3 = 5` のような具体的な計算や、`7` が素数であることの証明などに使う。プラグインシステムで拡張可能。

## ゴールパターン

**適用前**
```lean
⊢ (2 : Nat) + 3 = 5
```

**適用後**: ゴールが閉じる

## 構文
```lean
norm_num                 -- ゴールの数値式を計算
norm_num at h            -- 仮定 h の数値式を計算
norm_num [lemma]         -- 追加補題を使用
```

## 必須 import
```lean
import Mathlib.Tactic.NormNum
```

## オプション一覧
| 構文 | 意味 |
|---|---|
| `at h` | 仮定 h に適用 |
| `at *` | 全仮定とゴールに適用 |
| `[e₁, e₂]` | 追加の simp 補題を使用 |

## Pros
- 数値リテラルの計算に確実（`decide` より高速な場合が多い）
- 素数判定 (`Nat.Prime 7`) なども自動証明
- `@[norm_num]` プラグインで拡張可能

## Cons
- 変数を含む式は扱えない → `ring`, `omega`, `simp` を使う
- あくまで数値正規化であり、代数的な等式は `ring` の方が適切
- Mathlib import が必要

## コードサンプル

### サンプル 1: 基本計算
```lean
example : (7 : Nat) * 8 = 56 := by norm_num
```

### サンプル 2: 不等式
```lean
example : (3 : Int) < 5 := by norm_num
```

### サンプル 3: 素数判定
```lean
example : Nat.Prime 17 := by norm_num
```

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `omega` | 線形算術 | 変数を含む Nat/Int 不等式 |
| `decide` | 決定手続き | Decidable な命題全般 |
| `ring` | 環の等式 | 変数を含む代数的等式 |
| `simp` | 簡約 | 数値以外も含む汎用簡約 |

## 参照
- [Mathlib4 ドキュメント — NormNum](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/NormNum/Basic.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
