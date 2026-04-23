# `simp_rw` — バインダ貫通型の書き換え

**カテゴリ**: 書換 | **定義元**: `Mathlib.Tactic.simp_rw` | **ソース**: Mathlib

## 概要
`simp_rw` は `simp only` の書き換え能力と `rw` の明示的規則指定を組み合わせたタクティク。`rw` と異なり、`∀`・`∃`・`fun` などのバインダの内部にも書き換えが浸透する。各規則は `simp only` で全出現に適用された後、次の規則に進む。

## ゴールパターン

**適用前**
```lean
⊢ ∀ x, f x = g x → P (f x)
```

**適用後**（`simp_rw [h]`、`h : ∀ x, f x = g x`）
```lean
⊢ ∀ x, g x = g x → P (g x)
```

## 構文
```lean
simp_rw [h]               -- h をバインダ内含め全出現に適用
simp_rw [← h]             -- 逆方向
simp_rw [h₁, h₂]          -- h₁ を全出現に適用後、h₂ を適用
simp_rw [h] at hyp        -- 仮定で適用
simp_rw [h] at *          -- 全体に適用
```

## 必須 import
```lean
import Mathlib.Tactic.SimpRw
```

## オプション一覧
| 構文 | 意味 |
|---|---|
| `[e₁, e₂, ...]` | 規則を左から順に全出現に適用 |
| `[← e]` | 逆方向で適用 |
| `at h` | 仮定 h に適用 |
| `at *` | 全仮定とゴールに適用 |

## Pros
- `rw` が到達できないバインダ内部にも書き換えが浸透する
- 全出現を一括で書き換えるため、`nth_rw` や `conv` が不要になる場面がある
- `simp only` と違い、指定規則のみを使うため予測しやすい

## Cons
- `simp` の内部ループを使うため、`rw` より少し遅い
- 全出現が書き換わるため、一部だけ書き換えたい場合は不向き
- `simp` の補題データベースは使わない（`simp only` 相当）
- 規則の適用順序が結果に影響するため注意が必要

## コードサンプル

### サンプル 1: バインダ内部の書き換え
```lean
import Mathlib.Tactic.SimpRw

example (f g : Nat → Nat) (h : ∀ x : Nat, f x = g x) :
    (∀ x, f x = 0) ↔ (∀ x, g x = 0) := by
  simp_rw [h]
  -- ⊢ (∀ x, g x = 0) ↔ (∀ x, g x = 0)
```

### サンプル 2: rw では失敗する場面
```lean
import Mathlib.Tactic.SimpRw

example (h : ∀ x, x + 0 = x) : (fun n => n + 0) = (fun n => n) := by
  -- rw [h] は失敗する（バインダ内部に到達できない）
  simp_rw [h]
  -- ⊢ (fun n => n) = (fun n => n)
```

### サンプル 3: 複数規則の順次適用
```lean
import Mathlib.Tactic.SimpRw

example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a + a = c + c := by
  simp_rw [h₁, h₂]
  -- h₁ で全 a → b、次に h₂ で全 b → c
  -- ⊢ c + c = c + c
```

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `rw` | 表層のみ | バインダ外の単純な書き換え |
| `simp only` | simp 補題ベース | simp 補題を活用した簡約 |
| `conv` | 位置指定 | 特定位置のみバインダ内書き換え |
| `nth_rw` | n番目のみ | 特定の出現のみ書き換え |

## 参照
- [Mathlib4 ドキュメント — simp_rw](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/SimpRw.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
