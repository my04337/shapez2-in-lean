# `field_simp` — 体の除算を消去

**カテゴリ**: 代数 | **定義元**: `Mathlib.Tactic.FieldSimp.fieldSimp` | **ソース**: Mathlib

## 概要
`field_simp` は体 (`Field`) やそれに近い構造で、分母をゼロでないことの仮定を使って消去し、除算のないゴールに変換する。続けて `ring` を適用するのが定石。

## ゴールパターン

**適用前**
```lean
x : ℚ
hx : x ≠ 0
⊢ 1 / x * x = 1
```

**適用後** （`field_simp` 後）
```lean
⊢ x = x  -- （ring で閉じる）
```

## 構文
```lean
field_simp               -- 分母を自動消去
field_simp [h₁, h₂]     -- 追加の分母≠0 補題を使用
field_simp at h          -- 仮定 h に適用
```

## 必須 import
```lean
import Mathlib.Tactic.FieldSimp
```

## オプション一覧
| 構文 | 意味 |
|---|---|
| `[h₁, h₂]` | 追加の分母≠0 補題 |
| `at h` | 仮定に適用 |
| `at *` | 全仮定とゴールに適用 |

## Pros
- 除算を含むゴールを `ring` で処理できる形に変換
- 分母≠0 の条件を自動的にコンテキストから検索
- `field_simp` → `ring` の2手で体の等式の大半が解ける

## Cons
- `Field` インスタンスがない型（`Nat`, `Int`）では動作しない
- 分母≠0 の仮定がコンテキストにないと失敗 → 明示的に `[hx]` で渡す
- 非常に複雑な式では正規化が不完全なことがある

## コードサンプル

### サンプル 1: 基本
```lean
example (x : ℚ) (hx : x ≠ 0) : x / x = 1 := by
  field_simp
```

### サンプル 2: field_simp + ring
```lean
example (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    1 / a + 1 / b = (a + b) / (a * b) := by
  field_simp
  ring
```

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `ring` | 後処理 | field_simp で分母消去後に ring で等式証明 |
| `simp` | 汎用簡約 | 除算を含まない場合 |
| `norm_num` | 数値計算 | 具体的な数値のみのとき |

## 参照
- [Mathlib4 ドキュメント — FieldSimp](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/FieldSimp.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
