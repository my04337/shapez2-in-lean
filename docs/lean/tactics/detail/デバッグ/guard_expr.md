# `guard_expr` — 式の等価性テスト

**カテゴリ**: デバッグ | **定義元**: `Lean.Elab.Tactic.guardExpr` | **ソース**: Lean4 core

---

## 概要

`guard_expr e =ₐ f` は式 `e` と `f` がα同値（α-equivalent、変数名の差異を除いて構造的に同一）かテストし、異なる場合はエラーで失敗する。証明スクリプトの中間状態を検証するデバッグ用タクティク。

---

## ゴールパターン

任意のゴールに対して使用可能。ゴールを変更しない。

---

## 構文

```lean
guard_expr e =ₐ f
guard_expr e = f       -- defEq テスト
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `guard_expr e =ₐ f` | α同値テスト |
| `guard_expr e = f` | 定義的等価テスト（defEq） |

---

## Pros（使うべき場面）

- 証明中の式が期待通りかテスト
- テストスクリプト内でのアサーション
- 補題適用結果の検証

---

## Cons（注意・失敗ケース）

- デバッグ専用で証明を進めない
- 最終的な証明からは除去すべき
- α同値と defEq の違いに注意

---

## コードサンプル

### サンプル 1: 式の検証

```lean
example : True := by
  guard_expr (1 + 1 : Nat) =ₐ (1 + 1 : Nat)
  trivial
```

### サンプル 2: defEq テスト

```lean
example : True := by
  guard_expr (2 : Nat) = (1 + 1 : Nat)
  trivial
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `guard_target` | ゴール検証 | ゴール自体を検証 |
| `guard_hyp` | 仮定検証 | 仮定の型を検証 |
| `trace` | 表示 | 式をログ出力 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
