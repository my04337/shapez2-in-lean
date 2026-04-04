# `replace` — 既存の同名仮定を除去して新しい仮定に置換

**カテゴリ**: 補題適用 | **定義元**: `Lean.Parser.Tactic.replace` | **ソース**: Lean4 core

---

## 概要

`replace` は `have` と同様にローカルコンテキストに仮定を追加するが、同名の既存仮定がある場合はそれを**除去**してから追加する。
`have` が同名仮定をシャドウ（上書きせず隠す）するだけなのに対し、`replace` は古い仮定を完全に消去する。
仮定を段階的に強化・変形していく証明スタイルで、コンテキストをクリーンに保つのに有用である。

---

## ゴールパターン

**適用対象**: 任意（ゴールの型に制約なし）

**適用前**
```lean
h : A
⊢ P
```

**適用後** (`replace h : B := ...`)
```lean
h : B
⊢ P
```

（元の `h : A` は消去される）

---

## 構文

```lean
replace h : T := e              -- 既存の h を消去し、新しい h : T を追加
replace h : T := by tac          -- タクティクで証明
replace h := e                   -- 型を推論に任せる
replace h : T := by              -- ブロック内で証明
  tac₁
  tac₂
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `replace h : T := e` | 既存の `h` を消去し、`h : T` を追加 |
| `replace h := e` | 型推論に任せて置換 |
| `replace h : T := by ...` | タクティクブロックで証明しつつ置換 |

---

## Pros（使うべき場面）

- 仮定を段階的に変形する証明で、コンテキストが煩雑にならない
- `have` + `clear` の 2 ステップを 1 行で書ける
- 仮定名を再利用するため、後続のタクティクで名前を変更する必要がない
- `specialize` の代替として、より自由な変形が可能

---

## Cons（注意・失敗ケース）

- **破壊的**: 元の仮定は完全に失われる。元の仮定を後で使う可能性がある場合は `have` を使う
- 同名の仮定が存在しない場合、`have` と同じ動作になる（エラーにはならない）
- 証明サブゴール内で元の `h` を参照すると、古い `h` がまだ使える場合がある点に注意

---

## コードサンプル

### サンプル 1: 仮定の強化

```lean
example (h : 5 ≥ 3) : 5 > 2 := by
  -- h : 5 ≥ 3
  -- ⊢ 5 > 2
  replace h : 5 > 2 := by omega
  -- h : 5 > 2
  -- ⊢ 5 > 2
  exact h
```

### サンプル 2: 仮定の変形（型の変更）

```lean
example (h : ∀ n : Nat, n + 0 = n) : 7 + 0 = 7 := by
  -- h : ∀ (n : Nat), n + 0 = n
  -- ⊢ 7 + 0 = 7
  replace h := h 7
  -- h : 7 + 0 = 7
  -- ⊢ 7 + 0 = 7
  exact h
```

### サンプル 3: have との違い（シャドウ vs 消去）

```lean
-- have はシャドウ: 古い h が残る
example (h : True) : True := by
  have h : 1 = 1 := rfl    -- 古い h : True は隠れるが存在する
  exact True.intro

-- replace は消去: 古い h が消える
example (h : True) : True := by
  replace h : 1 = 1 := rfl  -- 古い h : True は消去される
  exact True.intro
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `have` | 非破壊版 | 同名仮定をシャドウするが消去しない。元の仮定を残したい場合 |
| `specialize` | 特殊化 | 全称量化の具体化に特化。`replace` はより汎用的な仮定変形 |
| `clear` | 仮定消去 | 仮定を消去するだけ。`replace` は消去＋新規追加を同時に行う |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
