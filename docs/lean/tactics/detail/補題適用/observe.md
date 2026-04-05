# `observe` — ライブラリ検索で仮定を自動追加

**カテゴリ**: 補題適用 | **定義元**: `Mathlib.Tactic.LibrarySearch.observe` | **ソース**: Mathlib

---

## 概要

`observe` は `exact?` の仕組みを利用して、指定した型の命題をライブラリから自動で検索し、
証明した上でローカルコンテキストに仮定として追加するタクティクである。
`have h : T := by exact?` のショートカットとして機能し、
ライブラリに存在する補題を使って中間命題を導入する際に便利。

---

## ゴールパターン

**適用対象**: 任意（仮定を追加するのみでゴールは変化しない）

**適用前**
```lean
⊢ P
```

**適用後** (`observe h : T`)
```lean
h : T       -- ライブラリ検索で自動証明された仮定
⊢ P
```

---

## 構文

```lean
observe h : T                    -- T を exact? で証明し h として追加
observe h := e                   -- 項 e の型を推論して追加
observe : T                      -- 名前省略（this に束縛）
```

---

## 必須 import

```lean
import Mathlib.Tactic.Observe
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `observe h : T` | 型 `T` をライブラリ検索で証明し仮定に追加 |
| `observe h := e` | 項 `e` の型を推論して追加 |
| `observe : T` | 名前省略で `this` に束縛 |

---

## Pros（使うべき場面）

- 補題の正確な名前を知らなくても、型さえ分かれば仮定を追加できる
- `have h : T := by exact?` よりも簡潔な記法
- 探索的な証明作業で、必要な補題の存在確認と導入を同時に行える

---

## Cons（注意・失敗ケース）

- ライブラリ検索に時間がかかる場合がある（特に大規模なインポート時）
- 求める型の命題がライブラリに存在しない場合は失敗する
- 最終的な証明では `exact?` が提案した具体的な補題名に置き換えるのが望ましい

---

## コードサンプル

### サンプル 1: 基本的な仮定の追加

```lean
import Mathlib.Tactic.Observe

example (n : Nat) (h : n > 0) : n ≥ 1 := by
  -- ⊢ n ≥ 1
  observe h' : n ≥ 1
  -- h' : n ≥ 1  （ライブラリ検索で証明される）
  exact h'
```

### サンプル 2: 名前省略で this を使用

```lean
import Mathlib.Tactic.Observe

example (a b : Nat) (ha : a > 0) (hb : b > 0) : a + b > 0 := by
  -- ⊢ a + b > 0
  observe : a + b > 0
  -- this : a + b > 0
  exact this
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `have` | 手動版 | 証明を手動で書く場合。`observe` は自動検索 |
| `exact?` | 検索 | ゴールを閉じる補題を検索。`observe` は仮定追加版 |
| `apply?` | 検索 | `apply` できる補題を検索 |
| `library_search` | 旧名 | `exact?` の旧名。`observe` は仮定導入版 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
