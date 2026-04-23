# `refold_let` — 展開された let 定義を折り畳む

**カテゴリ**: 簡約 | **定義元**: `Mathlib.Tactic.refoldLetStx` | **ソース**: Mathlib

---

## 概要

`refold_let x y` はコンテキスト中の `let` 定義 `x := e` に対し、ゴールや仮定中の `e` を `x` に戻す（折り畳む）タクティクである。`set` や `dsimp` で展開されてしまった定義を元に戻す場合に使う。`extract_lets` の逆操作に近い。

---

## ゴールパターン

**適用前**
```lean
x : Nat := 5
⊢ 5 + 5 = 10
```

**適用後**（`refold_let x`）
```lean
x : Nat := 5
⊢ x + x = 10
```

---

## 構文

```lean
refold_let x
refold_let x y
refold_let x at h
```

---

## 必須 import

```lean
import Mathlib.Tactic.FoldLet
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `refold_let x` | ゴール中の `x` の定義値を `x` に折り畳む |
| `refold_let x at h` | 仮定 `h` にも適用 |

---

## Pros（使うべき場面）

- `dsimp` や `simp` で展開された let 定義を元に戻す
- ゴールの可読性を回復
- `set` で導入した定義名を再利用

---

## Cons（注意・失敗ケース）

- コンテキストに `let` 定義がない場合は効果なし
- Mathlib import が必要
- 部分的な一致では折り畳まない

---

## コードサンプル

### サンプル 1: 基本的な折り畳み

```lean
import Mathlib.Tactic.FoldLet

example : (let x := 5; x + x) = 10 := by
  extract_lets x
  -- x : Nat := 5 ⊢ x + x = 10
  rfl
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `extract_lets` | 逆操作 | let を引き上げるなら `extract_lets` |
| `set` | 定義導入 | 新しい let 定義の導入 |
| `unfold` | 定義展開 | 定義を展開する |

---

## 参照

- [Mathlib4 ドキュメント — FoldLet](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/FoldLet.html)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
