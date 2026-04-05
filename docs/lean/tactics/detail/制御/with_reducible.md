# `with_reducible` — reducible 透明度のみでタクティクを実行する

**カテゴリ**: 制御 | **定義元**: `Lean.Parser.Tactic.withReducible` | **ソース**: Lean4 core

---

## 概要

`with_reducible tac` は透明度を `reducible` に制限した状態で `tac` を実行する。`@[reducible]` 属性が付いた定義のみ展開される。`simp` や `rfl` が過剰に定義を展開することを防ぎ、性能改善やゴールの予測可能性向上に使う。

---

## ゴールパターン

任意のゴールに適用可能。内部タクティクの動作のみが制限される。

---

## 構文

```lean
with_reducible tac
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `with_reducible tac` | `@[reducible]` のみ展開して `tac` を実行 |

---

## Pros（使うべき場面）

- `simp` や `rfl` の展開範囲を制限してパフォーマンス改善
- 意図しない定義展開を防止
- 透明度制御による証明の安定化

---

## Cons（注意・失敗ケース）

- 展開範囲が狭すぎて `tac` が失敗する場合がある
- 通常の証明では不要（パフォーマンスチューニング向け）
- デバッグ時の使い分けが難しい

---

## コードサンプル

### サンプル 1: 基本的な使い方

```lean
example : True := by
  with_reducible trivial
```

### サンプル 2: simp の展開制限

```lean
@[reducible] def myVal : Nat := 42

example : myVal = 42 := by
  with_reducible rfl
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `with_reducible_and_instances` | 拡張版 | インスタンスも展開するなら |
| `with_unfolding_all` | 全展開 | 全定義を展開するなら |
| `with_unfolding_none` | 展開なし | 一切展開しないなら |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
