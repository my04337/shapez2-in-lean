# `rename` — 仮定の名前を変更

**カテゴリ**: 変換 | **定義元**: `Lean.Parser.Tactic.rename` | **ソース**: Lean4 core

---

## 概要

`rename` はローカルコンテキスト中の仮定の名前を変更するタクティクである。
型パターンに一致する仮定を検索し、指定した新しい名前に変更する。
自動生成された不可読な名前（`h✝`、`a✝` 等）を人間可読な名前に置き換える際に便利。
`rename_i` は名前なし（イナクセシブル）仮定のリネームに特化した変種。

---

## ゴールパターン

**適用対象**: 任意（仮定のリネームのみで、ゴールの型は変化しない）

**適用前**
```lean
h✝ : P → Q
⊢ R
```

**適用後** (`rename (P → Q) => hpq`)
```lean
hpq : P → Q
⊢ R
```

---

## 構文

```lean
rename T => newName           -- 型 T の仮定を newName に変更
rename_i name₁ name₂ ...     -- イナクセシブル仮定を順にリネーム
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `rename T => name` | 型 `T` に一致する仮定を `name` にリネーム |
| `rename_i n₁ n₂` | イナクセシブル仮定を先頭から順にリネーム |

---

## Pros（使うべき場面）

- 自動生成名を可読性の高い名前に変換し、証明の読みやすさを向上
- `cases`、`induction` 後に生成された `h✝` 系の名前を整理できる
- `rename_i` は `with` 節を使えない場面での名前付けに便利

---

## Cons（注意・失敗ケース）

- 型パターンに一致する仮定が複数ある場合、曖昧でエラーになることがある
- リネームのみで証明は進まないため、過度な使用は冗長
- `with` 節で最初から名前を付けられる場合はそちらが望ましい

---

## コードサンプル

### サンプル 1: 型パターンによるリネーム

```lean
example (h : Nat → Bool) (h' : Bool) : Bool := by
  -- h : Nat → Bool, h' : Bool
  -- ⊢ Bool
  rename (Nat → Bool) => f
  -- f : Nat → Bool, h' : Bool
  -- ⊢ Bool
  exact f 0
```

### サンプル 2: cases 後のリネーム

```lean
example (n : Nat) : n = 0 ∨ n > 0 := by
  cases n
  · -- ⊢ Nat.zero = 0 ∨ Nat.zero > 0
    left; rfl
  · -- n✝ : Nat ⊢ n✝ + 1 = 0 ∨ n✝ + 1 > 0
    rename_i k
    -- k : Nat ⊢ k + 1 = 0 ∨ k + 1 > 0
    right; omega
```

### サンプル 3: rename_i で複数仮定を一度にリネーム

```lean
example (h : ∃ x : Nat, ∃ y : Nat, x + y = 10) : True := by
  obtain ⟨_, _, _⟩ := h
  -- ⊢ True  （w✝, w✝¹, h✝ が生成される）
  rename_i a b hab
  -- a : Nat, b : Nat, hab : a + b = 10
  -- ⊢ True
  trivial
```

---

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `rename'` | Lean 3 互換の rename（Mathlib） |
| `rename_bvar` | 束縛変数の名前を変更する |

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `intro` | 名前付き導入 | 全称量化子の導入時に最初から名前を付ける |
| `cases ... with` | 名前付き分解 | `with` 節で各ケースの名前を指定する |
| `obtain` | パターン分解 | 存在命題の分解時に名前を付けられる |
| `clear` | 仮定除去 | 不要な仮定を削除する |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
