# `choose` — 存在量化からの選択関数抽出

**カテゴリ**: 特化 | **定義元**: `Mathlib.Tactic.Choose.choose` | **ソース**: Mathlib

## 概要
`choose` は `∀ x, ∃ y, P x y` 形式の仮定から選択関数 `f : X → Y` と性質 `∀ x, P x (f x)` を抽出するタクティク。選択公理（`Classical.choice`）を利用して、存在量化の証拠から具体的な関数を構成する。ネストされた `∀∃` にも対応し、複数の選択関数を一度に抽出できる。

## ゴールパターン

**適用前**（`choose f hf using h`）
```lean
h : ∀ x : α, ∃ y : β, P x y
⊢ Q
```

**適用後**
```lean
f : α → β
hf : ∀ x, P x (f x)
⊢ Q
```

## 構文
```lean
choose f hf using h           -- 仮定 h から f と hf を抽出
choose f g hfg using h        -- ネストされた ∀∃∃ から複数関数を抽出
choose! f hf using h          -- Classical.choice を使わない版（Decidable 前提）
```

## 必須 import
```lean
import Mathlib.Tactic.Choose
```

## オプション一覧
| 構文 | 意味 |
|---|---|
| `choose f hf using h` | 仮定 h から関数 f と性質 hf を抽出 |
| `choose! f hf using h` | 計算的選択（`Decidable` 前提） |
| `choose f g hfg using h` | 入れ子の存在量化から複数関数を抽出 |

## Pros
- `∀∃` パターンから使いやすい関数を自動構成
- ネストされた存在量化にも対応
- 抽出した関数を後続の証明で自由に使える

## Cons
- `Classical.choice` に依存するため、構成的証明には使えない
- 一般的な `∃` のみ（`∀` なし）の場合は `obtain` で十分
- 選択関数の具体的な定義は不明（非構成的）

## コードサンプル

### サンプル 1: 基本的な選択関数の抽出
```lean
import Mathlib.Tactic.Choose

example (h : ∀ n : Nat, ∃ m : Nat, m > n) : ∃ f : Nat → Nat, ∀ n, f n > n := by
  choose f hf using h
  -- f : Nat → Nat
  -- hf : ∀ n, f n > n
  exact ⟨f, hf⟩
```

### サンプル 2: ネストされた存在量化
```lean
import Mathlib.Tactic.Choose

example (h : ∀ x : Nat, ∃ y z : Nat, x + y = z) :
    ∃ (f g : Nat → Nat), ∀ x, x + f x = g x := by
  choose f g hfg using h
  -- f : Nat → Nat
  -- g : Nat → Nat
  -- hfg : ∀ x, x + f x = g x
  exact ⟨f, g, hfg⟩
```

### サンプル 3: 列の構成への応用
```lean
import Mathlib.Tactic.Choose

example {α : Type*} (P : α → α → Prop) (h : ∀ x, ∃ y, P x y) (a : α) :
    ∃ f : Nat → α, f 0 = a ∧ ∀ n, P (f n) (f (n + 1)) := by
  choose next hnext using h
  -- next : α → α, hnext : ∀ x, P x (next x)
  exact ⟨fun n => Nat.rec a (fun _ x => next x) n, rfl, fun n => by
    induction n with
    | zero => exact hnext a
    | succ n ih => exact hnext _⟩
```

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `choose!` | 存在性の分解時に型推論をより積極的に行う |

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `obtain` | 存在の分解 | 単発の `∃` 分解には `obtain` |
| `rcases` | パターン分解 | 仮定のパターン分解全般 |
| `use` | 存在の証明 | `∃` ゴールに証拠を提供 |

## 参照
- [Mathlib4 ドキュメント — choose](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Choose.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
