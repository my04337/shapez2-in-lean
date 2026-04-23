# `whnf` — 弱頭部正規形への変換

**カテゴリ**: 簡約 | **定義元**: `Mathlib.Tactic.tacticWhnf__` | **ソース**: Mathlib

---

## 概要

`whnf` はゴール（または仮定）を弱頭部正規形（Weak Head Normal Form, WHNF）に変換するタクティクである。
WHNF は式の最外側（頭部）のみを簡約した形で、
β 簡約（関数適用）、δ 簡約（定義展開）、ι 簡約（マッチの簡約）を頭部に対してのみ行う。
`simp` や `norm_num` が重すぎる場合や、式の先頭構造だけを見たい場合に有効。

---

## ゴールパターン

**適用対象**: 任意（式の頭部を正規化）

**適用前**
```lean
⊢ (fun x => x + 1) 3 = 4
```

**適用後**
```lean
⊢ 3 + 1 = 4
```

---

## 構文

```lean
whnf                           -- ゴールを WHNF に変換
whnf at h                      -- 仮定 h を WHNF に変換
```

---

## 必須 import

```lean
import Mathlib.Tactic.WHNF
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `whnf` | ゴールを弱頭部正規形に変換 |
| `whnf at h` | 仮定 `h` を弱頭部正規形に変換 |
| `whnf at h ⊢` | 仮定とゴールの両方を変換 |

---

## Pros（使うべき場面）

- `simp` より軽量で高速な式の簡約
- 定義の展開やラムダ式の適用を最外層だけ行い、内部構造を保持する
- `match` や `if` の頭部が確定している場合にイータ簡約を行う

---

## Cons（注意・失敗ケース）

- 内部の式は簡約されない（完全な正規化には `simp` や `norm_num` を使う）
- WHNF という概念自体が直感的でない場合がある
- 期待する展開が行われないことがある（定義の `@[reducible]` 属性に依存）

---

## コードサンプル

### サンプル 1: ラムダ式の β 簡約

```lean
import Mathlib.Tactic.WHNF

example : (fun x => x + 1) 3 = 4 := by
  -- ⊢ (fun x => x + 1) 3 = 4
  whnf
  -- ⊢ 3 + 1 = 4  （β 簡約で頭部が展開される）
  rfl
```

### サンプル 2: 定義の展開

```lean
import Mathlib.Tactic.WHNF

def mySucc (n : Nat) := n + 1

example : mySucc 5 = 6 := by
  -- ⊢ mySucc 5 = 6
  whnf
  -- ⊢ 5 + 1 = 6  （mySucc が展開される）
  rfl
```

### サンプル 3: 仮定の簡約

```lean
import Mathlib.Tactic.WHNF

example (h : (fun x => x * 2) 3 = 6) : 3 * 2 = 6 := by
  -- h : (fun x => x * 2) 3 = 6
  -- ⊢ 3 * 2 = 6
  whnf at h
  -- h : 3 * 2 = 6
  exact h
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `simp` | 完全簡約 | 再帰的に補題を適用する完全な簡約。`whnf` より重い |
| `dsimp` | 定義簡約 | 証明項を変えない定義的簡約 |
| `unfold` | 定義展開 | 特定の定義を指定して展開 |
| `norm_num` | 数値正規化 | 数値的な式の完全な正規化 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
