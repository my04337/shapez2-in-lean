# `fail_if_success` — タクティクが失敗することを検証する

**カテゴリ**: 制御 | **定義元**: `Lean.Parser.Tactic.failIfSuccess` | **ソース**: Lean4 core

---

## 概要

`fail_if_success tac` は内部タクティク `tac` が成功した場合に失敗し、`tac` が失敗した場合に成功する否定テスト用タクティクである。タクティクの「到達不能性」のアサーションやリグレッションテストに利用される。`tac` が成功した場合もゴールには影響を与えない。

---

## ゴールパターン

**適用前**
```lean
⊢ P
```

**適用後**: ゴール変化なし（`tac` が失敗した場合のみ成功）

---

## 構文

```lean
fail_if_success tac
fail_if_success
  tac₁
  tac₂
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `fail_if_success tac` | `tac` が失敗すれば成功、成功すれば失敗 |

---

## Pros（使うべき場面）

- 「このタクティクではゴールが閉じない」ことをテストする
- リグレッションテスト: 将来のバージョンで動作が変わらないことを検証
- メタプログラミングでの否定条件分岐

---

## Cons（注意・失敗ケース）

- ゴールを閉じるタクティクではない
- 内部タクティクの副作用（warning 等）は抑制されない場合がある
- テスト以外の実際の証明で使うべきではない

---

## コードサンプル

### サンプル 1: simp では閉じないことの検証

```lean
-- rfl は n ≠ 0 を証明できないため、fail_if_success が期待通り「成功」する
example (n : Nat) (h : n > 0) : n ≠ 0 := by
  fail_if_success rfl  -- rfl は失敗（n ≠ 0 は等式ではない）
  omega
```

### サンプル 2: 否定テスト

```lean
-- rfl で閉じない等式をテスト
example : True := by
  fail_if_success exact (rfl : 1 = 2)
  trivial
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `fail` | 常に失敗 | 無条件の失敗は `fail` |
| `try` | 失敗の無視 | 失敗を無視して続行するなら `try` |
| `done` | 完了検証 | ゴールがないことを検証するなら `done` |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
