# `subst_vars` — 変数等式仮定を一括消去する

**カテゴリ**: 変換 | **定義元**: `Lean.Parser.Tactic.substVars` | **ソース**: Lean4 core

---

## 概要

`subst_vars` はコンテキスト中の `x = y`（変数同士の等式）を全て見つけ、一括で `subst` を適用して変数を消去する。`subst_eqs` と似ているが、`subst_vars` はより限定的に変数同士の等式のみを対象とする。`cases` 後に自動生成される等式の整理に有用。

---

## ゴールパターン

**適用前**
```lean
a b : Nat
h : a = b
⊢ a + 1 = b + 1
```

**適用後**
```lean
b : Nat
⊢ b + 1 = b + 1
```

---

## 構文

```lean
subst_vars
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `subst_vars` | 変数同士の全等式仮定を `subst` で消去 |

---

## Pros（使うべき場面）

- 変数等式が多量に発生する場合（match/cases 後）に一括整理
- Lean4 core 組み込みで import 不要
- `subst` を繰り返す定型パターンを 1 行に

---

## Cons（注意・失敗ケース）

- `x = expr`（expr が変数でない場合）は対象外 → `subst_eqs` を使う
- 依存型により `subst` できない等式はスキップされる
- 消去順序の制御はできない

---

## コードサンプル

### サンプル 1: 変数等式の消去

```lean
example (a b : Nat) (h : a = b) : a = b := by
  subst_vars
  -- a が b に置換される
  rfl
```

### サンプル 2: 複数等式

```lean
example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  subst_vars
  rfl
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `subst` | 単一消去 | 特定の仮定のみ消去 |
| `subst_eqs` | 全等式消去 | 変数以外の等式も含めて消去するなら `subst_eqs` |
| `simp` | 簡約 | 書き換えルールとして使うなら `simp` |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
