# `refine'` — 自動メタ変数生成版 refine

**カテゴリ**: 補題適用 | **定義元**: `Lean.Elab.Tactic.evalRefine'` | **ソース**: Lean4 core

---

## 概要

`refine'` は `refine` の旧版で、`_` をメタ変数としてサブゴールを自動生成する。`refine` が `?_` を明示的なプレースホルダとして使うのに対し、`refine'` は暗黙引数やインスタンス引数も含めて全ての `_` をサブゴール化する。

---

## ゴールパターン

**適用前**
```lean
⊢ Q
```

**適用後**（`refine' f _ _`）
```lean
⊢ A    -- 第1引数の型
⊢ B    -- 第2引数の型
```

---

## 構文

```lean
refine' e
```

- `_` はサブゴールとして残る
- `refine` より多くのサブゴールが生成される場合がある

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `refine' e` | `e` を適用し、`_` をサブゴール化 |

---

## Pros（使うべき場面）

- `refine` で `?_` を書くのが面倒な場合
- 暗黙引数も含めて制御したい場合
- Lean 3 からの移植で `refine` を使っていた場合

---

## Cons（注意・失敗ケース）

- `refine` の方がゴール数を制御しやすい
- 想定外の暗黙引数がサブゴール化される場合がある
- 新規コードでは `refine` を推奨

---

## コードサンプル

### サンプル 1: 基本的な使用

```lean
example : ∃ n : Nat, n = 0 := by
  refine' ⟨_, _⟩
  · exact 0
  · rfl
```

### サンプル 2: refine との違い

```lean
-- refine: ?_ のみサブゴール化
-- refine': 全ての _ がサブゴール化
example : ∃ n : Nat, n = 0 := by
  refine ⟨?_, ?_⟩
  · exact 0
  · rfl
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `refine` | 推奨版 | `?_` で制御するなら `refine` |
| `exact` | 完全版 | プレースホルダ不要なら `exact` |
| `apply` | 関数適用 | 最終引数をサブゴール化 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
