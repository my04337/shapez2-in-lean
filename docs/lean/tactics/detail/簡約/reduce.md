# `reduce` — カーネルの完全簡約を実行する

**カテゴリ**: 簡約 | **定義元**: `Lean.Parser.Tactic.reduce` | **ソース**: Lean4 core

---

## 概要

`reduce` はカーネルレベルの完全簡約（β、δ、ι、ζ 簡約）をゴールに適用するタクティクである。`dsimp` よりも深い簡約を行い、定義を完全に展開・計算する。計算結果を直接ゴールに反映したい場合に使う。

---

## ゴールパターン

**適用前**
```lean
⊢ 2 + 3 = 5
```

**適用後**
```lean
⊢ 5 = 5
```

---

## 構文

```lean
reduce
reduce at h
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `reduce` | ゴールを完全簡約 |
| `reduce at h` | 仮定 `h` を完全簡約 |

---

## Pros（使うべき場面）

- 数値計算を完全に実行したい場合
- `dsimp` では不足な深い定義展開が必要な場合
- Lean4 core 組み込みで import 不要

---

## Cons（注意・失敗ケース）

- 大きな式では極端に遅くなる場合がある
- ゴールが巨大に展開されて読めなくなるリスク
- `norm_num` や `decide` の方が適切なことが多い

---

## コードサンプル

### サンプル 1: 数値計算

```lean
example : 2 + 3 = 5 := by
  reduce
  rfl
```

### サンプル 2: 定義の完全展開

```lean
def myFun (n : Nat) : Nat := n + 1

example : myFun 3 = 4 := by
  reduce
  rfl
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `dsimp` | 定義的簡約 | `@[simp]` 補題を使った軽量簡約 |
| `norm_num` | 数値計算 | 数値計算の正規化なら `norm_num` が適切 |
| `decide` | 決定手続き | Decidable なら `decide` |
| `native_decide` | 高速決定 | 高速な計算決定 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
