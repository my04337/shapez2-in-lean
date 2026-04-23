# `bv_omega` — ビットベクタ向け線形算術ソルバー

**カテゴリ**: 特化 | **定義元**: `Lean.Parser.Tactic.bvOmega` | **ソース**: Lean4 core

## 概要
`bv_omega` は `omega` をビットベクタ (`BitVec n`) に拡張したタクティク。ビットベクタの線形算術（加算・減算・比較・定数倍など）を自動的に証明する。内部的にビットベクタの制約を自然数・整数の制約に変換し、`omega` に委譲する。`bv_decide`（SAT ベース）と異なり、線形算術に限定されるが高速。

## ゴールパターン

**適用前**
```lean
⊢ (x : BitVec 8) ≤ 255
```

**適用後**: ゴールが閉じる

## 構文
```lean
bv_omega    -- ビットベクタ線形算術を omega で解く
```

## 必須 import
Lean4 core 組み込み。

## Pros
- ビットベクタの範囲制約・加減算を高速に証明
- `omega` と同じ使用感で学習コストが低い
- SAT ソルバーを使わないため証明項が比較的コンパクト

## Cons
- 線形算術に限定（ビット演算 `&&&`, `|||` 等は解けない）
- 非線形なビットベクタ演算には `bv_decide` が必要
- ビット幅が型レベルで不明な場合は適用不可

## コードサンプル

### サンプル 1: ビットベクタの範囲制約
```lean
example (x : BitVec 8) : x ≤ 255 := by
  bv_omega
  -- ゴールが閉じる（8ビット値は必ず 255 以下）
```

### サンプル 2: 加算のオーバーフロー境界
```lean
example (x y : BitVec 16) (h : x.toNat + y.toNat < 2 ^ 16) :
    (x + y).toNat = x.toNat + y.toNat := by
  bv_omega
  -- ゴールが閉じる（オーバーフローしない場合の等式）
```

### サンプル 3: ゼロとの比較
```lean
example (x : BitVec 32) (h : x ≠ 0) : 0 < x := by
  bv_omega
  -- ゴールが閉じる
```

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `omega` | 基本形 | `Nat` / `Int` の線形算術 |
| `bv_decide` | SAT ベース | ビット演算含む完全決定手続き |
| `decide` | 汎用決定 | Decidable 全般だが遅い |

## 参照
- [Lean4 公式リファレンス — bv_omega](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#bv_omega)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
