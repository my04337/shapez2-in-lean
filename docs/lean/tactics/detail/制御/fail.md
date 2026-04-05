# `fail` — 常に失敗するタクティク

**カテゴリ**: 制御 | **定義元**: `Lean.Parser.Tactic.fail` | **ソース**: Lean4 core

---

## 概要

`fail` は常に失敗するタクティクである。オプションでエラーメッセージを指定できる。主にメタプログラミングやタクティクのテスト・デバッグで使い、`first`・`try`・`fail_if_success` と組み合わせて制御フローを構築する用途がある。

---

## ゴールパターン

**適用前**
```lean
⊢ P
```

**適用後**: 常に失敗（ゴール変化なし）

---

## 構文

```lean
fail
fail "custom error message"
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `fail` | デフォルトメッセージで失敗 |
| `fail "msg"` | 指定メッセージで失敗 |

---

## Pros（使うべき場面）

- タクティクのテストで「ここに到達してはいけない」ことを表明
- `first [tac₁, fail "msg"]` のようなフォールバック制御
- メタプログラミングでの分岐制御

---

## Cons（注意・失敗ケース）

- 証明を閉じる用途には使えない（常に失敗する）
- 実際の証明スクリプトに残すべきではない
- `sorry` と混同しないこと（`sorry` は成功してゴールを閉じる）

---

## コードサンプル

### サンプル 1: テストでの使用

```lean
-- fail_if_success の中で使うパターン
example : True := by
  fail_if_success fail
  trivial
```

### サンプル 2: メッセージ付き

```lean
-- first と組み合わせてフォールバック
example : 1 = 1 := by
  first
  | rfl
  | fail "rfl should have worked"
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `fail_if_success` | 否定テスト | タクティクが成功しないことを確認するなら `fail_if_success` |
| `sorry` | プレースホルダー | ゴールを仮閉じするなら `sorry`（`fail` は閉じない） |
| `skip` | no-op | 何もしないが成功するなら `skip` |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
