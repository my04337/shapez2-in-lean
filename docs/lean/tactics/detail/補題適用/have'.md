# `have'` — let に近い have

**カテゴリ**: 補題適用 | **定義元**: `Lean.Elab.Tactic.evalHave'` | **ソース**: Lean4 core

---

## 概要

`have'` は `have` と同様に新たな仮定をコンテキストに追加するが、`let` のように定義の展開が可能な形で追加する場合がある。`have` が不透明な仮定を追加するのに対し、`have'` は名前を匿名のまま残し、ゴールに直接統合する形で使われる。

---

## ゴールパターン

**適用前**
```lean
⊢ Q
```

**適用後**（`have' h : P := proof`）
```lean
h : P
⊢ Q
```

---

## 構文

```lean
have' h : T := proof
have' : T := proof      -- 匿名
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `have' h : T := proof` | 名前付きで仮定追加 |
| `have' : T := proof` | 匿名で仮定追加 |

---

## Pros（使うべき場面）

- `have` の代替で、より限定的なスコープの仮定追加
- パターンマッチと組み合わせる場合
- `have` で名前衝突が起きる場合の回避

---

## Cons（注意・失敗ケース）

- `have` で十分な場合がほとんど
- 挙動の違いが微妙で混乱しやすい
- 使用頻度は低い

---

## コードサンプル

### サンプル 1: 基本的な使用

```lean
example : True := by
  have' h : 1 = 1 := rfl
  trivial
```

### サンプル 2: have との比較

```lean
-- have: 不透明な仮定を追加
-- have': ほぼ同じだが名前の扱いが微妙に異なる
example : True := by
  have h : 1 = 1 := rfl
  trivial
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `have` | 標準版 | 通常はこちらを使う |
| `let` | 展開可能版 | 定義を展開したいなら `let` |
| `obtain` | 分解版 | パターン分解が必要なら `obtain` |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
