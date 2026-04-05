# `eapply` — 遅延ユニフィケーション付き apply

**カテゴリ**: 補題適用 | **定義元**: `Lean.Parser.Tactic.eapply` | **ソース**: Lean4 core

---

## 概要

`eapply` は `apply` の変種で、ユニフィケーションで解決可能なサブゴールの生成を遅延させるタクティクである。
通常の `apply` はすべての暗黙引数に対してサブゴールを生成するが、
`eapply` は後続のユニフィケーションで自動的に埋まる可能性のあるメタ変数を保留し、
残りのサブゴールのみを生成する。
これにより不要なサブゴールの生成を抑え、証明を簡潔にできる。

---

## ゴールパターン

**適用対象**: 補題・関数の適用が可能なゴール

**適用前**
```lean
⊢ Q
```

**適用後** (`eapply h` where `h : P₁ → P₂ → Q`)
```lean
-- ユニフィケーションで解決できないサブゴールのみ生成
⊢ P₁
⊢ P₂
```

---

## 構文

```lean
eapply h              -- h を適用、遅延可能なゴールを保留
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `eapply h` | `h` を適用、ユニフィケーション可能なサブゴールを遅延 |

---

## Pros（使うべき場面）

- `apply` よりサブゴール数が少なくなり、証明が簡潔になる場合がある
- 依存型の引数が後続のゴール解決で自動決定される場合に有効
- 存在命題の証明で witness を後回しにできる

---

## Cons（注意・失敗ケース）

- 遅延したメタ変数が最終的に解決されないと証明が完了しない
- `apply` で問題なくサブゴールが生成される場合は `apply` の方が予測しやすい
- 遅延の挙動がバージョンによって変わる可能性がある

---

## コードサンプル

### サンプル 1: 存在命題での使用

```lean
example : ∃ n : Nat, n + 1 = 3 := by
  -- ⊢ ∃ n, n + 1 = 3
  eapply Exists.intro
  -- ⊢ ?w + 1 = 3  （witness ?w は遅延される）
  show 2 + 1 = 3  -- ?w を 2 に確定
  rfl
```

### サンプル 2: 推移律の適用

```lean
example (a b c : Nat) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  -- ⊢ a ≤ c
  eapply Nat.le_trans
  -- ⊢ a ≤ ?m  （中間値 ?m は遅延される）
  · exact h₁
  -- ?m が b に決定される
  · exact h₂
```

### サンプル 3: apply との比較

```lean
-- apply は全てのサブゴールを生成
-- eapply はユニフィケーション可能なものを遅延
example (f : Nat → Nat → Nat) (h : ∀ x y, f x y = f y x) :
    f 1 2 = f 2 1 := by
  -- ⊢ f 1 2 = f 2 1
  eapply h
  -- ゴールなし（x=1, y=2 がユニフィケーションで解決）
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `apply` | 標準版 | 全サブゴールを明示的に生成。通常はこちら |
| `refine` | プレースホルダ版 | `_` でプレースホルダを明示的に配置 |
| `exact` | 完全適用 | 引数を全て指定して閉じる |
| `fapply` | 全生成版 | 遅延せず全てのサブゴールを生成する |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
