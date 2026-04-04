# `rcongr` — 合同性を再帰的に適用してバインダ内部まで分解する

**カテゴリ**: 変換 | **定義元**: `Mathlib.Tactic.Congr.rcongr` | **ソース**: Mathlib

---

## 概要

`rcongr` は等式ゴール `f a₁ ... = f b₁ ...` に対し、`congr` を再帰的に適用し、さらにバインダ（ラムダ式・∀ 等）の内部にも入り込んで `funext` 的な分解も行う。`congr` + `funext` + `congr` + ... を自動的に繰り返す強化版。変数名を指定することもできる。

---

## ゴールパターン

**適用前**
```lean
⊢ List.map (fun x => f x + 1) l = List.map (fun x => g x + 1) l
```

**適用後**（`rcongr x`）
```lean
x : α
⊢ f x = g x
```

---

## 構文

```lean
rcongr
rcongr x y
```

- 名前を指定するとバインダ変数に名前を付ける
- 名前省略時は自動命名

---

## 必須 import

```lean
import Mathlib.Tactic.Congr
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `rcongr` | 再帰的に合同性を適用（自動命名） |
| `rcongr x y` | バインダ変数を `x`, `y` と命名 |

---

## Pros（使うべき場面）

- バインダ内部の差異まで自動的に掘り下げてくれる
- `congr` + `funext` の繰り返しを 1 行にまとめられる
- `List.map`、`Set.image` 等の高階関数の等式証明に強い

---

## Cons（注意・失敗ケース）

- 深すぎる分解で不要なサブゴールが生成される場合がある
- Mathlib import が必要
- `congrm` ほど精密な位置指定はできない

---

## コードサンプル

### サンプル 1: List.map の等式

```lean
import Mathlib.Tactic.Congr

example (f g : Nat → Nat) (h : ∀ x, f x = g x) (l : List Nat) :
    l.map f = l.map g := by
  rcongr x
  -- x : Nat ⊢ f x = g x
  exact h x
```

### サンプル 2: 自動的な再帰分解

```lean
import Mathlib.Tactic.Congr

example (a b : Nat) (h : a = b) : (a, a + 1) = (b, b + 1) := by
  rcongr
  -- rcongr が h を自動で使用して閉じる
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `congr` | 基本版 | 1 段階の合同分解なら `congr` |
| `congrm` | パターン版 | パターンで位置指定するなら `congrm` |
| `funext` | 関数拡張 | 関数等式のみなら `funext` |
| `ext` | 外延性 | `@[ext]` 属性を使った分解なら `ext` |

---

## 参照

- [Mathlib4 ドキュメント — rcongr](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Congr.html)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
