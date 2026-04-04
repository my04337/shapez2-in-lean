# `open` — タクティクブロック内で名前空間を開く

**カテゴリ**: 制御 | **定義元**: `Lean.Parser.Tactic.open` | **ソース**: Lean4 core

---

## 概要

`open` はタクティクブロック内で名前空間を一時的に開くタクティクである。
通常 `open` はコマンドレベルで使用するが、タクティク版はスコープが後続のタクティクブロックに限定される。
名前空間の接頭辞を省略して短い名前でアクセスできるようにする。
長い修飾名をタイプする手間を減らし、証明の可読性を向上させる。

---

## ゴールパターン

**適用対象**: 任意（ゴールの型は変化しない）

**適用前**
```lean
⊢ P
```

**適用後**
```lean
-- ゴールは変化しない（名前解決のみ変更）
⊢ P
```

---

## 構文

```lean
open Namespace in
<tactic>

open Namespace₁ Namespace₂ in
<tactic>

open Namespace (name₁ name₂) in     -- 特定の名前のみ
<tactic>
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `open N in tac` | 名前空間 `N` をスコープ内で開く |
| `open N₁ N₂ in tac` | 複数の名前空間を開く |
| `open N (x y) in tac` | `N` から `x`, `y` のみをインポート |
| `open scoped N in tac` | scoped 属性のみを有効化 |

---

## Pros（使うべき場面）

- 長い修飾名（`Nat.succ_lt_succ`、`List.map_nil` 等）を短縮できる
- スコープが限定されるため、名前衝突のリスクが低い
- `scoped` 版で記法やインスタンスを局所的に有効化できる

---

## Cons（注意・失敗ケース）

- 名前が他の名前空間と衝突する場合、曖昧性エラーが発生する
- あまりに多くの名前空間を開くと、意図しない名前解決が行われる
- 短い名前では何の補題か分かりにくくなるため、レビュー時の可読性に注意

---

## コードサンプル

### サンプル 1: Nat 名前空間の開放

```lean
example (n : Nat) (h : n > 0) : n - 1 + 1 = n := by
  -- ⊢ n - 1 + 1 = n
  open Nat in
  exact succ_pred_eq_of_pos h
```

### サンプル 2: 複数名前空間

```lean
example (l : List Nat) : (l.map id).length = l.length := by
  -- ⊢ (List.map id l).length = l.length
  open List Function in
  simp [map_id]
```

### サンプル 3: scoped 記法の有効化

```lean
example (s t : Set Nat) (h : s ⊆ t) (x : Nat) (hx : x ∈ s) : x ∈ t := by
  -- ⊢ x ∈ t
  open scoped Set in
  exact h hx
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `set_option ... in` | 類似構文 | オプション変更をスコープ内に限定 |
| `simp` | 名前利用 | `open` で短縮した名前を `simp` の補題リストに使う |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
