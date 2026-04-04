# `with_reducible_and_instances` — reducible + インスタンス透明度でタクティクを実行する

**カテゴリ**: 制御 | **定義元**: `Lean.Parser.Tactic.withReducibleAndInstances` | **ソース**: Lean4 core

---

## 概要

`with_reducible_and_instances tac` は透明度を `reducible` + 型クラスインスタンスに制限した状態で `tac` を実行する。`with_reducible` より少し広い展開範囲で、型クラスインスタンスの定義を展開するが、一般の `@[semireducible]` 定義は展開しない。

---

## ゴールパターン

任意のゴールに適用可能。

---

## 構文

```lean
with_reducible_and_instances tac
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `with_reducible_and_instances tac` | reducible + インスタンスのみ展開して `tac` を実行 |

---

## Pros（使うべき場面）

- 型クラスインスタンスは展開したいが他の定義は展開したくない場合
- `with_reducible` では不足だが `with_unfolding_all` は過剰な場合の中間

---

## Cons（注意・失敗ケース）

- 通常の証明では不要（上級者向け透明度制御）
- 展開範囲の把握が難しい

---

## コードサンプル

### サンプル 1: 基本的な使い方

```lean
example : True := by
  with_reducible_and_instances trivial
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `with_reducible` | 狭い展開 | インスタンスも不要なら |
| `with_unfolding_all` | 全展開 | 全定義を展開するなら |
| `with_unfolding_none` | 展開なし | 一切展開しないなら |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
