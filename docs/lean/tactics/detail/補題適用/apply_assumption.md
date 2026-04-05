# `apply_assumption` — 仮定を自動検索して `apply` する

**カテゴリ**: 補題適用 | **定義元**: `Lean.Parser.Tactic.applyAssumption` | **ソース**: Lean4 core

---

## 概要

`apply_assumption` は、ローカルコンテキスト中の仮定を順に走査し、結論部がゴールにユニファイできるものを見つけて自動的に `apply` するタクティクである。
`assumption` がゴールと型が完全一致する仮定を探して `exact` するのに対し、`apply_assumption` は関数型の仮定の結論部でマッチし、前提をサブゴールとして残す。
仮定名を明示する必要がないため、自動化パイプラインや汎用的な証明スクリプトで有用。

---

## ゴールパターン

**適用対象**: 仮定依存（結論部がゴールにマッチする仮定が必要）

**適用前**
```lean
h₁ : A → B
h₂ : C → D
⊢ B
```

**適用後** (`apply_assumption`)
```lean
-- h₁ が選択される
-- ⊢ A
```

---

## 構文

```lean
apply_assumption                          -- 仮定を自動検索して apply
apply_assumption (config := { ... })       -- 設定をカスタマイズ
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `apply_assumption` | デフォルト設定で仮定を検索・適用 |
| `apply_assumption (config := { transparency := .reducible })` | 透過度を指定 |

---

## Pros（使うべき場面）

- 仮定名を覚える必要がなく、コンテキストが大きい場合に便利
- 自動化タクティクの構成要素として使える（`solve_by_elim` などの内部で利用される）
- `apply` を試す仮定が多数ある場合、手動で試す手間を省ける
- ゴールが変化しても仮定名に依存しないため、リファクタリングに強い

---

## Cons（注意・失敗ケース）

- 複数の仮定がマッチする場合、最初に見つかったものが選ばれ、意図しない仮定が適用される可能性がある
- マッチする仮定がない場合はエラーになる
- どの仮定が適用されたか証明を読む人には不明瞭。可読性の観点では `apply h` の方が望ましい
- 暗黙引数の解決で意図しないユニフィケーションが起きることがある

---

## コードサンプル

### サンプル 1: 基本的な使い方

```lean
example (h : P → Q) (hp : P) : Q := by
  -- h : P → Q, hp : P
  -- ⊢ Q
  apply_assumption
  -- h が選択され apply される
  -- ⊢ P
  exact hp
```

### サンプル 2: 複数の仮定がある場合

```lean
example (h₁ : A → B) (h₂ : B → C) (ha : A) : C := by
  -- h₁ : A → B, h₂ : B → C, ha : A
  -- ⊢ C
  apply_assumption
  -- h₂ が選択される（結論部が C にマッチ）
  -- ⊢ B
  apply_assumption
  -- h₁ が選択される（結論部が B にマッチ）
  -- ⊢ A
  exact ha
```

### サンプル 3: assumption との対比

```lean
-- assumption: 完全一致する仮定を exact
example (h : P) : P := by
  assumption   -- exact h と同等

-- apply_assumption: 結論部でマッチして apply
example (h : P → Q) (hp : P) : Q := by
  apply_assumption   -- apply h と同等、サブゴール ⊢ P が残る
  assumption
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `assumption` | 完全一致版 | ゴールと型が完全一致する仮定を検索。サブゴールは生成しない |
| `apply` | 明示版 | 適用する仮定を名前で指定。可読性が高い |
| `exact` | 項指定版 | 完全な証明項を直接渡す。自動検索は行わない |
| `solve_by_elim` | 連鎖版 | `apply_assumption` を再帰的に繰り返して証明を探索 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
