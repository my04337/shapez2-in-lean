# `specialize` — ローカル仮定の全称量化子を具体値でインスタンス化

**カテゴリ**: 補題適用 | **定義元**: `Lean.Parser.Tactic.specialize` | **ソース**: Lean4 core

---

## 概要

`specialize` は、ローカルコンテキスト中の全称量化付き仮定に具体的な引数を与えて特殊化するタクティクである。
`h : ∀ x, P x` に対して `specialize h a` を実行すると、`h` が `h : P a` に置き換わる。
関数型の仮定にも使えるため、`h : A → B → C` の `A` を満たす証明を渡して `h : B → C` に縮めることもできる。
仮定を破壊的に書き換えるため、元の汎用的な仮定は失われる。

---

## ゴールパターン

**適用対象**: 仮定依存（ローカルコンテキストに全称量化または関数型の仮定が必要）

**適用前**
```lean
h : ∀ x : Nat, x > 0 → x ≥ 1
⊢ P
```

**適用後** (`specialize h 5`)
```lean
h : 5 > 0 → 5 ≥ 1
⊢ P
```

---

## 構文

```lean
specialize h a                  -- 1 引数を具体化
specialize h a b                -- 複数引数を同時に具体化
specialize h a (by omega)       -- タクティクで引数を証明
specialize h rfl                -- 等式の証明を渡す
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `specialize h a` | `h` の最初の引数を `a` で具体化 |
| `specialize h a b` | `h` の先頭 2 引数を同時に具体化 |
| `specialize h a (by tac)` | 引数をタクティクで証明しつつ具体化 |

---

## Pros（使うべき場面）

- 汎用的な仮定を特定のケースに絞り込み、後続の証明を簡潔にできる
- `have h' := h a` よりも簡潔で、古い仮定が自動的に置き換わるためコンテキストが煩雑にならない
- 関数型の引数を順に消費して仮定を段階的に単純化できる

---

## Cons（注意・失敗ケース）

- **破壊的**: 元の汎用仮定 `h` は失われる。同じ `h` を別の値で再利用したい場合は `have h' := h a` を使う
- 仮定がローカルコンテキストに存在しない場合はエラー
- 暗黙引数が多い仮定では、意図しない引数が消費されることがある
- `specialize` はゴールを変化させない（仮定のみ変化する）

---

## コードサンプル

### サンプル 1: 全称量化の具体化

```lean
example (h : ∀ n : Nat, n + 0 = n) : 5 + 0 = 5 := by
  -- h : ∀ (n : Nat), n + 0 = n
  -- ⊢ 5 + 0 = 5
  specialize h 5
  -- h : 5 + 0 = 5
  -- ⊢ 5 + 0 = 5
  exact h
```

### サンプル 2: 関数型の引数を消費

```lean
example (h : Nat → Nat → Nat) : h 1 2 = h 1 2 := by
  -- h : Nat → Nat → Nat
  -- ⊢ h 1 2 = h 1 2
  specialize h 1 2
  -- h : Nat
  -- ⊢ h = h
  rfl
```

### サンプル 3: タクティクで条件を証明しつつ特殊化

```lean
example (h : ∀ n : Nat, n > 0 → n ≥ 1) : 3 ≥ 1 := by
  -- h : ∀ (n : Nat), n > 0 → n ≥ 1
  -- ⊢ 3 ≥ 1
  specialize h 3 (by omega)
  -- h : 3 ≥ 1
  -- ⊢ 3 ≥ 1
  exact h
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `apply` | 逆方向推論 | ゴール側から仮定を適用。`specialize` は仮定側を変形 |
| `have` | 非破壊版 | `have h' := h a` で元の `h` を残しつつ特殊化コピーを作成 |
| `replace` | 同名上書き | `replace h := h a` も同様の効果だが、`specialize` の方が意図が明確 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
