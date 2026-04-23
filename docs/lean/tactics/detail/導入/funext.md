# `funext` — 関数外延性による等式証明

**カテゴリ**: 導入 | **定義元**: `Lean.Parser.Tactic.funext` | **ソース**: Lean4 core

---

## 概要

`funext` は関数の等式 `f = g` を「任意の入力 `x` に対して `f x = g x`」に帰着する関数外延性（function extensionality）タクティク。ゴールが `⊢ f = g`（ただし `f g : α → β`）の形のとき適用でき、新たな変数 `x : α` を導入して `⊢ f x = g x` に変換する。複数引数の関数にも対応する。

---

## ゴールパターン

**適用前**
```lean
f g : Nat → Int
⊢ f = g
```

**適用後** (`funext x`)
```lean
f g : Nat → Int
x : Nat
⊢ f x = g x
```

**適用前**（複数引数）
```lean
⊢ (fun a b => a + b) = (fun a b => b + a)
```

**適用後** (`funext a b`)
```lean
a b : Nat
⊢ a + b = b + a
```

---

## 構文

```lean
funext x               -- 変数 x を導入して外延性適用
funext x y             -- 複数引数を同時に導入
funext _               -- 名前なしで導入
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 説明 |
|---|---|
| `funext x` | 変数 `x` を名前付きで導入 |
| `funext x y` | 複数変数を一括導入 |
| `funext _` | 無名変数で導入 |

---

## Pros（使うべき場面）

- 関数の等式証明で最初に使うべき標準タクティク
- `∀ x, f x = g x` を示すだけでよいという自然な方針に帰着できる
- 複数引数の関数でも一度に外延性を適用可能

---

## Cons（注意・失敗ケース）

- ゴールが関数型の等式でないと適用できない
- 依存関数 `(x : α) → β x` では型が複雑になる場合がある
- 構造体の等式には `ext` の方が適切（`funext` は関数等式専用）

---

## コードサンプル

### サンプル 1: 基本的な関数等式
```lean
example : (fun n : Nat => n + 0) = (fun n => n) := by
  funext n
  -- n : Nat
  -- ⊢ n + 0 = n
  exact Nat.add_zero n
```

### サンプル 2: 複数引数の関数
```lean
example : (fun a b : Nat => a + b) = (fun a b => b + a) := by
  funext a b
  -- a b : Nat
  -- ⊢ a + b = b + a
  exact Nat.add_comm a b
```

### サンプル 3: ラムダ式の簡約と組み合わせ
```lean
example : (fun x : Nat => x * 1) = (fun x => x) := by
  funext x
  -- x : Nat
  -- ⊢ x * 1 = x
  exact Nat.mul_one x
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `ext` | 汎用外延性 | 構造体の等式にも対応する一般的な外延性 |
| `congr` | 構造分解 | 関数適用の等式を引数ごとの等式に分解 |
| `simp` | 簡約 | 外延性を使わず簡約で済む場合 |

---

## 参照
- [Lean4 公式リファレンス — funext](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#funext)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
