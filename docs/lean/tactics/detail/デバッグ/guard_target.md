# `guard_target` — ゴールの型テスト

**カテゴリ**: デバッグ | **定義元**: `Lean.Elab.Tactic.guardTarget` | **ソース**: Lean4 core

---

## 概要

`guard_target = T` は現在のゴールの型が `T` と定義的に等しいかテストし、異なればエラーで失敗する。証明スクリプトの各ステップでゴールが期待通りに変化しているか確認するデバッグ用タクティク。

---

## ゴールパターン

任意のゴールに対して使用可能。ゴールを変更しない。

---

## 構文

```lean
guard_target = T
guard_target =ₐ T     -- α同値テスト
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `guard_target = T` | ゴールが `T` と defEq か |
| `guard_target =ₐ T` | ゴールが `T` とα同値か |

---

## Pros（使うべき場面）

- ゴールの変化を逐次検証
- テストスクリプトのアサーション
- 複雑な証明のデバッグ

---

## Cons（注意・失敗ケース）

- デバッグ専用で証明を進めない
- 最終的な証明からは除去すべき
- 表示形と内部表現が異なる場合がある

---

## コードサンプル

### サンプル 1: ゴールの検証

```lean
example : 1 + 1 = 2 := by
  guard_target = 1 + 1 = 2
  rfl
```

### サンプル 2: タクティク適用後の確認

```lean
example : ∀ n : Nat, n = n := by
  intro n
  guard_target = n = n
  rfl
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `guard_hyp` | 仮定検証 | 仮定の型を検証 |
| `guard_expr` | 式検証 | 任意の式を検証 |
| `trace` | 表示 | ゴールをログ出力 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
