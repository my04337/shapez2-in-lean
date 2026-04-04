# `guard_hyp` — 仮定の型テスト

**カテゴリ**: デバッグ | **定義元**: `Lean.Elab.Tactic.guardHyp` | **ソース**: Lean4 core

---

## 概要

`guard_hyp h : T` はコンテキスト中の仮定 `h` の型が `T` と定義的に等しいかテストし、異なればエラーで失敗する。証明スクリプトの中間状態を検証するデバッグ用タクティク。

---

## ゴールパターン

任意のゴールに対して使用可能。ゴールを変更しない。

---

## 構文

```lean
guard_hyp h : T
guard_hyp h :ₐ T     -- α同値テスト
guard_hyp h := v      -- 値テスト（let 束縛）
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `guard_hyp h : T` | `h` の型が `T` と defEq か |
| `guard_hyp h :ₐ T` | `h` の型が `T` とα同値か |
| `guard_hyp h := v` | `h` の値が `v` か（let束縛用） |

---

## Pros（使うべき場面）

- 仮定の型が期待通りか確認
- テストスクリプトでのアサーション
- タクティク適用後の状態検証

---

## Cons（注意・失敗ケース）

- デバッグ専用で証明を進めない
- 最終的な証明からは除去すべき
- 仮定名が変わるとテストが壊れる

---

## コードサンプル

### サンプル 1: 仮定の型検証

```lean
example (h : 1 + 1 = 2) : True := by
  guard_hyp h : 1 + 1 = 2
  trivial
```

### サンプル 2: intro 後の検証

```lean
example : ∀ n : Nat, n = n := by
  intro n
  guard_hyp n : Nat
  rfl
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `guard_target` | ゴール検証 | ゴールの型を検証 |
| `guard_expr` | 式検証 | 任意の式を検証 |
| `trace` | 表示 | 仮定をログ出力 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
