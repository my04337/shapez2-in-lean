# `unfold_projs` — 型クラス射影を展開する

**カテゴリ**: 簡約 | **定義元**: `Lean.Parser.Tactic.unfoldProjs` | **ソース**: Lean4 core

---

## 概要

`unfold_projs` はゴール中の型クラス射影（projection）を展開するタクティクである。例えば `HAdd.hAdd` をその実装に展開する。型クラスの具体的な実装を直接操作したい場合の前処理として使用する。

---

## ゴールパターン

**適用前**
```lean
⊢ HAdd.hAdd a b = ...
```

**適用後**: 射影が具体的な実装に展開される

---

## 構文

```lean
unfold_projs
unfold_projs at h
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `unfold_projs` | ゴール中の型クラス射影を展開 |
| `unfold_projs at h` | 仮定に適用 |

---

## Pros（使うべき場面）

- 型クラス射影の内部実装を確認・操作したい場合
- `dsimp` では展開されない射影を展開する必要がある場合
- core 組み込みで import 不要

---

## Cons（注意・失敗ケース）

- 展開後の式が複雑になることが多い
- 通常は `simp` や `dsimp` で十分
- 射影がない場合は効果なし

---

## コードサンプル

### サンプル 1: 基本的な射影展開

```lean
example (a b : Nat) : a + b = Nat.add a b := by
  unfold_projs
  rfl
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `unfold` | 定義展開 | 一般的な定義展開 |
| `dsimp` | 定義的簡約 | simp 補題を使った軽量簡約 |
| `delta` | δ展開 | unfold の低レベル版 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
