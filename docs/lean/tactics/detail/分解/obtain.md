# `obtain` — 仮定の導入と同時分解

**カテゴリ**: 分解 | **定義元**: `Lean.Parser.Tactic.obtain` | **ソース**: Lean4 core

## 概要
`obtain` は `have` と `rcases` を組み合わせたタクティクで、型注釈付きの仮定を導入しつつ、即座にパターン分解する。`∃` や `∧` の証明を構築してから分解する一連の流れを1行で書ける。`rcases` と同じパターン記法が使える。

## ゴールパターン

**適用前**（`obtain ⟨x, hx⟩ : ∃ n, P n := proof`）
```lean
⊢ Q
```

**適用後**
```lean
x : Nat
hx : P x
⊢ Q
```

**適用前**（`obtain ⟨a, b⟩ := h`）
```lean
h : P ∧ Q
⊢ R
```

**適用後**
```lean
a : P
b : Q
⊢ R
```

## 構文
```lean
obtain ⟨a, b⟩ := h                  -- 既存の仮定を分解
obtain ⟨x, hx⟩ : ∃ n, P n := proof  -- 型注釈付きで導入・分解
obtain ⟨a, b⟩ : A ∧ B := by tac     -- タクティクで証明して分解
obtain ⟨a, rfl⟩ := h                 -- rfl パターンで等式を代入
obtain ⟨a, b | c⟩ := h               -- ネストした分解
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `⟨a, b⟩ := h` | 既存仮定 h を分解 |
| `⟨a, b⟩ : T := proof` | 型 T の証明を与えて分解 |
| `rfl` | 等式仮定を即座に代入 |
| `_`, `-` | 名前を付けず破棄／スキップ |

## Pros
- `have` + `rcases` を1行で書ける
- 型注釈を明示できるため、可読性が高い
- 証明の構造が「何を得たいか」で表現できる

## Cons
- `rcases` だけで十分な場合は冗長になることがある
- 型注釈を省略すると `rcases` と同じ挙動になるため使い分けが曖昧
- 和型（`Or`）の分解はゴールが分岐するため、`rcases` の方が見通しがよい場合もある

## コードサンプル

### サンプル 1: 存在量化の分解
```lean
example (h : ∃ n : Nat, n > 0 ∧ n < 10) : ∃ n, n < 10 := by
  obtain ⟨n, _, hlt⟩ := h
  -- n : Nat, hlt : n < 10 ⊢ ∃ n, n < 10
  exact ⟨n, hlt⟩
```

### サンプル 2: 型注釈付きで新しい仮定を導入
```lean
example (n : Nat) (h : n ≠ 0) : ∃ m, n = m + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    exact ⟨n - 1, by omega⟩
  -- m : Nat ⊢ ∃ m, m + 1 = m + 1
  exact ⟨m, rfl⟩
```

### サンプル 3: And の分解
```lean
example (h : P ∧ Q ∧ R) : R ∧ P := by
  obtain ⟨hp, _, hr⟩ := h
  -- hp : P, hr : R ⊢ R ∧ P
  exact ⟨hr, hp⟩
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `rcases` | パターン分解 | 既存仮定の分解だけなら `rcases` で十分 |
| `have` | 仮定導入 | 分解不要なら `have` のみ |
| `rintro` | 導入+分解 | ゴールが `∀` / `→` 形式のとき |

## 参照
- [Lean4 公式リファレンス — obtain](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#rcases)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
