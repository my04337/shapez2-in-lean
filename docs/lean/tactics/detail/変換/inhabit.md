# `inhabit` — Nonempty 仮定から Inhabited インスタンスを生成する

**カテゴリ**: 変換 | **定義元**: `Mathlib.Tactic.Inhabit.inhabit` | **ソース**: Mathlib

---

## 概要

`inhabit α` は `Nonempty α` の仮定（または推論可能な事実）から `Inhabited α` インスタンスをコンテキストに追加するタクティクである。`Classical.choice` を使用するため古典論理に依存する。`Inhabited` が必要な API を呼び出す前処理として使う。

---

## ゴールパターン

**適用前**
```lean
h : Nonempty α
⊢ P
```

**適用後**（`inhabit α`）
```lean
h : Nonempty α
inst✝ : Inhabited α
⊢ P
```

---

## 構文

```lean
inhabit α
```

- `α`: `Inhabited` インスタンスを生成したい型

---

## 必須 import

```lean
import Mathlib.Tactic.Inhabit
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `inhabit α` | `Nonempty α` から `Inhabited α` を生成してコンテキストに追加 |

---

## Pros（使うべき場面）

- `Nonempty` はあるが `Inhabited` が求められる場面で変換できる
- `default` や `Array.get!` 等の API 呼び出しに必要なインスタンスを供給
- 1 行で完了し、手動の `Classical.choice` 呼び出しを不要にする

---

## Cons（注意・失敗ケース）

- `Classical.choice` を使うため構成的証明には不適
- `Nonempty α` が仮定にもなく推論もできない場合は失敗する
- Mathlib import が必要

---

## コードサンプル

### サンプル 1: Nonempty から Inhabited を生成

```lean
import Mathlib.Tactic.Inhabit

example (h : Nonempty Nat) : ∃ n : Nat, n = n := by
  inhabit Nat
  exact ⟨default, rfl⟩
```

### サンプル 2: 抽象型での使用

```lean
import Mathlib.Tactic.Inhabit

example {α : Type} (h : Nonempty α) : ∃ a : α, a = a := by
  inhabit α
  exact ⟨default, rfl⟩
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `haveI` | インスタンス追加 | 任意のインスタンスを追加するなら `haveI` |
| `classical` | 古典論理有効化 | 排中律全体を有効にするなら `classical` |
| `nontriviality` | Nontrivial 追加 | `Nontrivial` インスタンスが必要なら `nontriviality` |

---

## 参照

- [Mathlib4 ドキュメント — Inhabit](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Inhabit.html)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
