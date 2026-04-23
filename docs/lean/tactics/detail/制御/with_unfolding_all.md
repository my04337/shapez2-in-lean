# `with_unfolding_all` — opaque 以外全てを展開してタクティクを実行する

**カテゴリ**: 制御 | **定義元**: `Lean.Parser.Tactic.withUnfoldingAll` | **ソース**: Lean4 core

---

## 概要

`with_unfolding_all tac` は透明度を最大（`all`）に設定し、`opaque` 以外の全ての定義を展開可能にした状態で `tac` を実行する。通常では展開されない定義も含めて展開するため、最も包括的な簡約が可能。

---

## ゴールパターン

任意のゴールに適用可能。

---

## 構文

```lean
with_unfolding_all tac
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `with_unfolding_all tac` | opaque 以外全て展開可能にして `tac` を実行 |

---

## Pros（使うべき場面）

- `rfl` や `decide` が通常の透明度では動かない場合の最終手段
- デバッグで全展開した状態を確認したい場合

---

## Cons（注意・失敗ケース）

- 過剰展開によりパフォーマンスが大幅に低下しうる
- ゴールが巨大に展開されて読めなくなる場合がある
- 最終証明では避けるべき（脆弱な証明になる）

---

## コードサンプル

### サンプル 1: 基本的な使い方

```lean
example : True := by
  with_unfolding_all trivial
```

### サンプル 2: 通常では通らない rfl

```lean
def myConst : Nat := 0

example : myConst = 0 := by
  with_unfolding_all rfl
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `with_reducible` | 狭い展開 | reducible のみ |
| `with_reducible_and_instances` | 中間 | reducible + インスタンス |
| `with_unfolding_none` | 展開なし | 一切展開しない |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
