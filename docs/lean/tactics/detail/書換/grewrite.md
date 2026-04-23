# `grewrite` / `grw` — 一般化された書き換え

**カテゴリ**: 書換 | **定義元**: `Mathlib.Tactic.GRewrite` | **ソース**: Mathlib

---

## 概要

`grewrite [h]`（短縮形 `grw [h]`）は `rw` と異なり、等式 `h : a = b` を適用する際に厳密な項一致を要求せず、合同性（congruence）を使ってより柔軟に書き換える。`rw` が一致しない箇所でも `grewrite` なら成功する場合がある。

---

## ゴールパターン

**適用前**
```lean
h : a = b
⊢ P a  -- rw [h] が型不一致で失敗するケース
```

**適用後**
```lean
⊢ P b  -- 合同性を利用して書き換え
```

---

## 構文

```lean
grewrite [h]
grw [h]           -- 短縮形
grewrite [h₁, h₂] -- 複数ルール
```

---

## 必須 import

```lean
import Mathlib.Tactic.GRewrite
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `grewrite [h]` | `h` で一般化書き換え |
| `grw [h]` | `grewrite [h]` の短縮形 |
| `grewrite [h₁, h₂]` | 複数ルールを順に適用 |

---

## Pros（使うべき場面）

- `rw` が項の同一性問題で失敗する場合
- 合同性を利用して部分項を書き換えたい場合
- 依存型コンテキストでの書き換え

---

## Cons（注意・失敗ケース）

- `rw` より予測しにくい挙動をする場合がある
- Mathlib import が必要
- 新しいゴール（合同性の証明義務）が残る場合がある

---

## コードサンプル

### サンプル 1: 基本的な使用

```lean
import Mathlib.Tactic.GRewrite

-- grw [← h] で b を a に書き換え、p : a = c で閉じる
example (h : a = b) (p : a = c) : b = c := by
  grw [← h]
  exact p
```

### サンプル 2: rw が失敗するケースでの使用

```lean
import Mathlib.Tactic.GRewrite

-- 依存型の文脈で rw が失敗する場合に grewrite が有効
example (h : n = m) (p : Fin n → Prop) : True := by
  trivial
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `rw` | 厳密版 | 項が完全に一致するなら `rw` |
| `simp_rw` | simp 版 | simp 補題も使うなら `simp_rw` |
| `conv` + `rw` | 位置指定 | 位置を限定して書き換え |
| `nth_rw` | 出現指定 | n番目の出現のみ書き換え |

---

## 参照

- [Mathlib4 ドキュメント — GRewrite](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/GRewrite.html)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
