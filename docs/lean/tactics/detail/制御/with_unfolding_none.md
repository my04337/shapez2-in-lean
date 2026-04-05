# `with_unfolding_none` — 定義展開を一切せずにタクティクを実行する

**カテゴリ**: 制御 | **定義元**: `Lean.Parser.Tactic.withUnfoldingNone` | **ソース**: Lean4 core

---

## 概要

`with_unfolding_none tac` は透明度を最小に設定し、定義の展開を一切行わない状態で `tac` を実行する。`rfl` 等が定義展開に頼らず純粋な構文的等価性のみで動作するかをテストする用途で使う。

---

## ゴールパターン

任意のゴールに適用可能。

---

## 構文

```lean
with_unfolding_none tac
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `with_unfolding_none tac` | 定義展開なしで `tac` を実行 |

---

## Pros（使うべき場面）

- 定義展開に頼らない証明かどうかのテスト
- デバッグで「何が展開されているか」を切り分ける

---

## Cons（注意・失敗ケース）

- ほとんどのタクティクが失敗する（展開なしでは一致しない）
- テスト・デバッグ専用
- 実際の証明には使わない

---

## コードサンプル

### サンプル 1: 構文的に等しい場合のみ rfl が通る

```lean
example : (fun x : Nat => x) = (fun x : Nat => x) := by
  with_unfolding_none rfl
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `with_reducible` | 狭い展開 | reducible のみ展開 |
| `with_unfolding_all` | 全展開 | 全定義を展開 |
| `with_reducible_and_instances` | 中間 | reducible + インスタンス |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
