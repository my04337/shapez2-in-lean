# `bv_decide` — ビットベクタの決定手続き

**カテゴリ**: 決定手続き | **定義元**: `Lean.Parser.Tactic.bvDecide` | **ソース**: Lean4 core

## 概要
`bv_decide` は固定幅ビットベクタ (`BitVec n`) に対する決定手続き。SAT ソルバーを利用してビットブラスティングによりゴールを証明する。`decide` よりも高速にビットベクタの等式・不等式を証明可能。

## ゴールパターン

**適用前**
```lean
⊢ (x &&& y : BitVec 32) = (y &&& x : BitVec 32)
```

**適用後**: ゴールが閉じる

## 構文
```lean
bv_decide              -- SAT ソルバーで証明
bv_omega               -- omega のビットベクタ版
```

## 必須 import
Lean4 core 組み込み。

## Pros
- ビットベクタの等式・不等式の完全な決定手続き
- SAT ソルバーベースで高速
- ハードウェア検証、暗号アルゴリズムの検証に適する

## Cons
- `BitVec n` 以外には使えない
- ビット幅が大きいと SAT ソルバーの限界にあたる場合がある
- 証明項が大きくなりうる

## コードサンプル

### サンプル 1: ビット演算の可換性
```lean
example (x y : BitVec 8) : x &&& y = y &&& x := by bv_decide
```

### サンプル 2: bv_omega
```lean
example (x : BitVec 8) : x ≤ 255 := by bv_omega
```

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `decide` | 汎用決定 | Decidable 全般だが遅い |
| `omega` | 線形算術 | Nat/Int の算術 |
| `native_decide` | 高速決定 | ネイティブコンパイルによる決定 |

## 参照
- [Lean4 公式リファレンス — bv_decide](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#bv_decide)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
