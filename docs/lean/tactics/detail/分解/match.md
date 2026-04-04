# `match` — タクティクモードでのパターンマッチ

**カテゴリ**: 分解 | **定義元**: `Lean.Parser.Tactic.match` | **ソース**: Lean4 core

---

## 概要

`match` はタクティクモードでパターンマッチを行うタクティクである。
ターム（項）モードの `match` と同様に帰納型の値をコンストラクタごとに分解するが、
各アーム（分岐）の右辺にはタクティクブロックを記述する。
`cases` と似た機能を提供するが、`match` はより直接的なパターン式を書ける点や、
複数の値を同時にマッチできる点が異なる。

---

## ゴールパターン

**適用対象**: 帰納型の値が関与するゴール

**適用前**
```lean
n : Nat
⊢ P n
```

**適用後** (`match n with | ...`)
```lean
-- アーム 1: ⊢ P 0
-- アーム 2: (k : Nat) ⊢ P (k + 1)
```

---

## 構文

```lean
match x with
| pat₁ => tac₁
| pat₂ => tac₂

match x, y with              -- 複数値の同時マッチ
| pat₁, pat₂ => tac
| pat₃, pat₄ => tac

match h : x with             -- h に等式を保存
| pat₁ => tac₁
| pat₂ => tac₂
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `match x with \| pat => tac` | 基本的なパターンマッチ |
| `match x, y with ...` | 複数値の同時マッチ |
| `match h : x with ...` | マッチ結果を等式として保存 |

---

## Pros（使うべき場面）

- ターム側の `match` とほぼ同じ構文で書けるため、直感的
- 複数の値を同時にマッチでき、ケースの組み合わせを一度に処理できる
- `h : x` 構文で等式を保存できる

---

## Cons（注意・失敗ケース）

- `cases` と異なり、`with` 節でコンストラクタ名による指定ができない
- 帰納法の仮説は生成されない（帰納法が必要な場合は `induction` を使う）
- パターンの網羅性チェックは行われるが、ワイルドカード `_` を使いすぎると可読性が低下する

---

## コードサンプル

### サンプル 1: Nat の場合分け

```lean
example (n : Nat) : n = 0 ∨ n ≥ 1 := by
  -- ⊢ n = 0 ∨ n ≥ 1
  match n with
  | 0 => left; rfl
  -- ⊢ 0 = 0 ∨ 0 ≥ 1 → left; rfl で閉じる
  | k + 1 => right; omega
  -- ⊢ k + 1 = 0 ∨ k + 1 ≥ 1 → right; omega で閉じる
```

### サンプル 2: 複数値の同時マッチ

```lean
example (b₁ b₂ : Bool) : (b₁ && b₂) = true → b₁ = true := by
  -- ⊢ (b₁ && b₂) = true → b₁ = true
  match b₁, b₂ with
  | true, true => intro _; rfl
  | true, false => intro h; simp at h
  | false, _ => intro h; simp at h
```

### サンプル 3: 等式を保存するマッチ

```lean
example (o : Option Nat) : o.isSome = true → ∃ n, o = some n := by
  -- ⊢ o.isSome = true → ∃ n, o = some n
  match o with
  | some n =>
    -- o が some n になる
    intro _
    exact ⟨n, rfl⟩
  | none =>
    -- o = none → isSome = false → 矛盾
    intro habs; simp at habs
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `cases` | 類似 | `cases` はコンストラクタ名ベースで `with` 節が使える |
| `rcases` | 再帰分解 | ネストした分解を一行で記述できる |
| `split` | if/match 分割 | ゴール中の `if`/`match` を自動で分割する |
| `induction` | 帰納法 | 帰納法の仮説が必要な場合に使う |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
