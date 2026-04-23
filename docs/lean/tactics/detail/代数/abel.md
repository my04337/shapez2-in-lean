# `abel` — 加法可換モノイド/群上の等式証明

**カテゴリ**: 代数 | **定義元**: `Mathlib.Tactic.Abel.tacticAbel` | **ソース**: Mathlib

---

## 概要

`abel` は加法的可換モノイド (`AddCommMonoid`) または加法的可換群 (`AddCommGroup`) の等式を自動証明する。加法 (`+`)・減算 (`-`)・スカラー倍 (`n • x`, `n * x`) のみを含む式を正規形に変換し、両辺が一致すれば証明完了。
`ring` が乗算を含む環の等式を扱うのに対し、`abel` は加法構造のみに特化している。

## ゴールパターン

**Before:**
```lean
G : Type*
inst : AddCommGroup G
a b c : G
⊢ a + b + c = c + b + a
```

**After:**
```lean
-- ゴールが閉じる（no goals）
```

## 構文

```lean
abel                  -- ゴールの等式を証明
abel_nf               -- ゴールを正規形に書き換え（閉じない場合もある）
abel_nf at h          -- 仮定 h を正規化
abel_nf at *          -- ゴールと全仮定を正規化
```

## 必須 import

```lean
import Mathlib.Tactic.Abel
```

## Pros（使うべき場面）

- 加法的可換モノイド/群の等式をワンショットで閉じる
- 抽象的な群（具体的な数値型に限らない）で動作する
- スカラー倍 (`n • x`) も正しく処理する
- `abel_nf` で仮定の正規化も可能

## Cons（注意・失敗ケース）

- 乗算（`a * b` で `a`, `b` が両方変数）を含む等式は扱えない → `ring` を使うこと
- 非可換群には対応しない → `group` を使うこと（乗法群の場合）
- 不等式は対象外 → `linarith` / `nlinarith` を使うこと
- `sub_nonneg` 等の順序的性質は証明できない

## コードサンプル

### 例 1: 加法群の交換

```lean
import Mathlib.Tactic.Abel

-- ⊢ a + b + c = c + b + a
example [AddCommGroup G] (a b c : G) : a + b + c = c + b + a := by
  abel
```

加法の交換法則と結合法則を自動的に適用して閉じる。

### 例 2: 減算を含む等式

```lean
import Mathlib.Tactic.Abel

-- ⊢ a - b + b = a
example [AddCommGroup G] (a b : G) : a - b + b = a := by
  abel
```

`-b + b = 0` を自動的に認識し、消去する。

### 例 3: スカラー倍を含む等式

```lean
import Mathlib.Tactic.Abel

-- ⊢ 2 • a + 3 • a = 5 • a
example [AddCommMonoid G] (a : G) : 2 • a + 3 • a = 5 • a := by
  abel
```

自然数スカラー倍 (`n • a`) の係数を正しく集計する。

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `abel!` | `norm_num` を併用してより強力に正規化する |
| `abel1` | 1 ステップのみ適用する |
| `abel1!` | `abel1` + `norm_num` |
| `abel_nf` | 正規形への書き換え（ゴールを閉じない） |
| `abel_nf!` | `abel_nf` + `norm_num` |

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `ring` | 上位 | 乗算を含む可換環の等式。加法のみなら `abel` で十分 |
| `ring_nf` | 上位 | 環式の正規化。乗算を含む場合に使う |
| `group` | 類似 | 乗法群（非可換を含む）の等式。`abel` は加法的可換群に特化 |
| `omega` | 補完 | `Nat` / `Int` の線形算術。具体的な数値型なら `omega` を優先 |
| `linear_combination` | 拡張 | 仮定を線形結合してゴールを証明。残余ゴールを `abel` で処理することもある |
| `module` | 拡張 | 加群・ベクトル空間の等式。スカラー乗法を含む場合に使う |

## 参照

- [Mathlib4 docs — abel](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Abel.html)

---

> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
