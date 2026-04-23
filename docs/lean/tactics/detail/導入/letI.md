# `letI` — 展開可能なインスタンスを追加する

**カテゴリ**: 導入 | **定義元**: `Lean.Parser.Tactic.tacticLetI_` | **ソース**: Lean4 core

---

## 概要

`letI` は `let` と同様に展開可能なローカル定義を追加するが、型クラスインスタンスとしてもアクセス可能にする。`haveI` が不透明な仮定を追加するのに対し、`letI` は展開可能な定義として追加する。定義の中身にアクセスする必要がある場合に使う。

---

## ゴールパターン

**適用前**
```lean
⊢ P  -- インスタンスが必要
```

**適用後**（`letI : C := e`）
```lean
inst✝ : C := e
⊢ P
```

---

## 構文

```lean
letI : TypeClass := expr
letI h : TypeClass := expr
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `letI : C := e` | `C` を展開可能インスタンスとして追加 |
| `letI h : C := e` | 名前 `h` を付けて追加 |

---

## Pros（使うべき場面）

- インスタンスの定義を展開してほしい場合（`dsimp` や `simp` で内部にアクセス）
- `haveI` では不透明すぎる場合の代替
- core 組み込みで import 不要

---

## Cons（注意・失敗ケース）

- 展開可能なため式が大きくなる場合がある
- 不透明で良いなら `haveI` の方が軽量
- ローカルスコープでのみ有効

---

## コードサンプル

### サンプル 1: Inhabited インスタンスの追加

```lean
example : True := by
  letI : Inhabited Nat := ⟨42⟩
  trivial
```

### サンプル 2: haveI との違い

```lean
-- letI: 定義が展開可能
-- haveI: 定義が不透明
example : True := by
  letI : Inhabited Nat := ⟨0⟩
  -- default は 0 に展開される
  trivial
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `haveI` | 不透明版 | 定義を隠したいなら `haveI` |
| `let` | 非インスタンス版 | インスタンスとして不要なら `let` |
| `have` | 非インスタンス不透明 | 通常の仮定追加 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
