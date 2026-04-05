# `ext1` — 外延性補題を1ステップだけ適用する

**カテゴリ**: 導入 | **定義元**: `Lean.Elab.Tactic.Ext.ext1` | **ソース**: Lean4 core

---

## 概要

`ext1` は `ext` の 1 ステップ版で、`@[ext]` 属性の外延性補題を 1 回だけ適用する。`ext` が再帰的に全てのフィールドを分解するのに対し、`ext1` は最外層のみ分解する。段階的に制御したい場合に使う。

---

## ゴールパターン

**適用前**
```lean
⊢ f = g   -- where f g : α → β
```

**適用後**
```lean
x : α
⊢ f x = g x
```

---

## 構文

```lean
ext1
ext1 x
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `ext1` | 1ステップ外延性を適用（自動命名） |
| `ext1 x` | 変数名を `x` に指定 |

---

## Pros（使うべき場面）

- `ext` の分解深さを 1 ステップに制限したい場合
- ネストした構造で段階的に分解したい場合
- import 不要（core 組み込み）

---

## Cons（注意・失敗ケース）

- 多段階分解には `ext` の方が簡潔
- `@[ext]` 補題がない場合は失敗
- `ext1` を繰り返すなら `ext` を使う方が良い

---

## コードサンプル

### サンプル 1: 関数等式の 1 ステップ分解

```lean
example (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by
  ext1 x
  -- x : Nat ⊢ f x = g x
  exact h x
```

### サンプル 2: ext との比較

```lean
-- ext は再帰的に全分解する
-- ext1 は 1 ステップのみ
example (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by
  ext1 x
  exact h x
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `ext` | 再帰版 | 全ステップ分解なら `ext` |
| `funext` | 関数外延性 | 関数等式に特化 |
| `congr` | 合同分解 | 引数の差異に分解 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
