# `subst_eqs` — 全等式仮定を一括消去する

**カテゴリ**: 変換 | **定義元**: `Lean.Parser.Tactic.substEqs` | **ソース**: Lean4 core

---

## 概要

`subst_eqs` はコンテキスト中の `x = e` または `e = x` 形式の等式仮定を全て見つけ、順次 `subst` を適用して変数を消去する。手動で `subst h₁; subst h₂; ...` と繰り返す代わりに 1 行で全ての等式仮定を処理できる。

---

## ゴールパターン

**適用前**
```lean
a b c : Nat
h₁ : a = 1
h₂ : b = 2
⊢ a + b = 3
```

**適用後**
```lean
c : Nat
⊢ 1 + 2 = 3
```

---

## 構文

```lean
subst_eqs
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `subst_eqs` | コンテキスト中の全 `x = e` / `e = x` を `subst` で消去 |

---

## Pros（使うべき場面）

- 多数の等式仮定を一括消去でき、コンテキストをクリーンにする
- `cases` や `induction` 後に生成された等式仮定の整理に最適
- Lean4 core 組み込みで import 不要

---

## Cons（注意・失敗ケース）

- `subst` できない形式の等式（例: `f x = g y`）は無視される
- 変数でない項の等式は対象外
- 消去順序により後続の仮定が使えなくなる場合がある

---

## コードサンプル

### サンプル 1: 基本的な一括消去

```lean
example (a b : Nat) (h₁ : a = 1) (h₂ : b = 2) : a + b = 3 := by
  subst_eqs
  -- a, b が 1, 2 に置換され ⊢ 1 + 2 = 3
  rfl
```

### サンプル 2: cases 後の整理

```lean
example (n : Nat) (h : n = 0) : n + 1 = 1 := by
  subst_eqs
  rfl
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `subst` | 単一消去 | 特定の仮定のみ消去するなら `subst` |
| `subst_vars` | 変数等式消去 | 変数同士の等式のみ対象なら `subst_vars` |
| `simp only [...]` | 書き換え | 等式を書き換えるが消去はしない |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
