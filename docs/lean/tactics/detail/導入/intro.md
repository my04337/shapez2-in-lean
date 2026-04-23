# `intro` — 全称量化子・含意の仮説導入

**カテゴリ**: 導入 | **定義元**: `Lean.Parser.Tactic.intro` | **ソース**: Lean4 core

---

## 概要

`intro` は、ゴールが `∀ x, P x` や `P → Q` の形のとき、束縛変数や仮定をローカルコンテキストに導入する。自然演繹における「∀ 導入」「→ 導入」に対応する基本タクティクであり、ほぼすべての証明で最初に使う。複数の名前を一度に指定でき、パターンマッチも限定的にサポートする。

---

## ゴールパターン

**適用前**
```lean
⊢ ∀ (n : Nat), n + 0 = n
```

**適用後** (`intro n`)
```lean
n : Nat
⊢ n + 0 = n
```

**適用前**（含意）
```lean
⊢ P → Q → P
```

**適用後** (`intro hp hq`)
```lean
hp : P
hq : Q
⊢ P
```

---

## 構文

```lean
intro x               -- 1 つの変数を導入
intro x y z           -- 複数の変数を一度に導入
intro (x : Nat)       -- 型注釈付き
intro _               -- 名前を付けずに導入（使わない仮定）
intro ⟨a, b⟩          -- 匿名コンストラクタでパターンマッチ
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 説明 |
|---|---|
| `intro x` | 名前 `x` で導入 |
| `intro _` | 無名で導入（ワイルドカード） |
| `intro (x : T)` | 型注釈付きで導入 |
| `intro ⟨a, b⟩` | パターンマッチ（構造体・存在など） |

---

## Pros（使うべき場面）

- `∀` / `→` を含むゴールの証明開始時にほぼ必ず使う
- 名前を明示することでコンテキストが読みやすくなる
- `intro _` で不要な仮定を名前なしで処理できる

---

## Cons（注意・失敗ケース）

- ゴールが `∀` / `→` の形でないと失敗する
- パターンマッチの能力は `rintro` に比べると限定的
- 導入する名前の数がゴールの束縛数を超えるとエラーになる

---

## コードサンプル

### サンプル 1: 基本的な ∀ の導入
```lean
example : ∀ (n : Nat), n = n := by
  intro n
  -- n : Nat
  -- ⊢ n = n
  rfl
```

### サンプル 2: 含意の仮定導入
```lean
example : ∀ (P Q : Prop), P → Q → P := by
  intro P Q hp _hq
  -- P Q : Prop
  -- hp : P
  -- _hq : Q
  -- ⊢ P
  exact hp
```

### サンプル 3: パターンマッチ付き導入
```lean
example : (∃ n : Nat, n = 0) → True := by
  intro ⟨n, hn⟩
  -- n : Nat
  -- hn : n = 0
  -- ⊢ True
  trivial
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `intros` | 上位互換 | 名前を省略して全変数を一括導入したい場合 |
| `rintro` | 上位互換 | `rcases` 相当のパターンマッチが必要な場合 |
| `introv` | 変種 | 型変数のみ自動命名で導入 |
| `fun` | Term モード | タクティクモード外でのラムダ抽象 |

---

## 参照
- [Lean4 公式リファレンス — intro](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#intro-intros)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
