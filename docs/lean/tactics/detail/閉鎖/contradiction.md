# `contradiction` — 矛盾する仮定からゴールを閉じる

**カテゴリ**: 閉鎖 | **定義元**: `Lean.Parser.Tactic.contradiction` | **ソース**: Lean4 core

---

## 概要

`contradiction` は、ローカルコンテキスト内に矛盾する仮定の組が存在する場合にゴールを閉じるタクティクである。
`h : False`、`h₁ : P` と `h₂ : ¬P`、`h : True = False`、`h : 0 = 1` のようなコンストラクタの不一致など、
様々なパターンの矛盾を自動的に検出する。
ゴールの型に依存せず、仮定から `False` を導出できれば任意のゴールを閉じることができる。

---

## ゴールパターン

**適用前**
```lean
h : False
⊢ P
```

**適用後**
```lean
-- ゴールなし（証明完了）
```

---

## 構文

```lean
contradiction
```

引数は取らない。

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `contradiction` | コンテキスト内の矛盾を自動検出してゴールを閉じる |

オプションはない。検出パターンは Lean コンパイラに組み込まれている。

---

## Pros（使うべき場面）

- `False` が仮定にある場合、ゴールの型を問わず即座に閉じられる
- `h : P` と `h' : ¬P` の対を自動検出する
- 帰納型のコンストラクタ不一致（`Nat.zero = Nat.succ n`）を検出する
- `cases` や `match` で到達不能ケースを処理する際に頻出

---

## Cons（注意・失敗ケース）

- 矛盾が直接的でない場合（推論ステップが必要な場合）は失敗する
- `¬P` が `P → False` に展開されない場合がある（`unfold Not` が必要な場合がある）
- `omega` や `simp` で導出可能な矛盾でも、`contradiction` 単体では検出できないケースがある
- 型クラスの不一致など複雑な矛盾パターンには対応しない

---

## コードサンプル

### サンプル 1: False 仮定

```lean
example (h : False) : 1 = 2 := by
  -- h : False
  -- ⊢ 1 = 2
  contradiction
  -- ゴールなし（証明完了）
```

### サンプル 2: P と ¬P の矛盾

```lean
example (h₁ : P) (h₂ : ¬P) : Q := by
  -- h₁ : P, h₂ : ¬P
  -- ⊢ Q
  contradiction
  -- ゴールなし（証明完了）
```

### サンプル 3: コンストラクタ不一致

```lean
example (h : 0 = 1) : False := by
  -- h : 0 = 1
  -- ⊢ False
  contradiction
  -- ゴールなし（証明完了）
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `exfalso` | 前処理 | ゴールを `False` に変換する。`contradiction` は `False` 導出とゴール閉鎖を同時に行う |
| `omega` | 拡張 | 線形算術の矛盾を検出。`contradiction` が失敗する数値矛盾に対応 |
| `simp_all` | 拡張 | 簡約を伴う矛盾検出。より広範だが重い |
| `absurd` | 手動版 | `absurd h₁ h₂` で `h₁ : P` と `h₂ : ¬P` から明示的に矛盾を導く |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
