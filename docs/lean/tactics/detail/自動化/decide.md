# `decide` / `native_decide` — Decidable な命題の決定

**カテゴリ**: 決定手続き | **定義元**: `Lean.Parser.Tactic.decide` / `Lean.Parser.Tactic.nativeDecide` | **ソース**: Lean4 core

## 概要
`decide` はゴールが `Decidable` インスタンスを持つ命題のとき、カーネルで真偽を評価して証明する。`native_decide` はネイティブコードにコンパイルして実行するため高速だが、信頼度が下がる。

## ゴールパターン

**適用前**
```lean
⊢ 2 + 2 = 4
```

**適用後**: ゴールが閉じる

## 構文
```lean
decide                  -- カーネル評価で証明
native_decide           -- ネイティブコードで高速証明
```

## 必須 import
Lean4 core 組み込み。

## Pros
- `Decidable` な命題を完全に自動証明
- 有限な列挙型の全探索、Bool 式の評価等に有効
- 証明が `rfl` ベースで簡潔

## Cons
- カーネル評価なので大きなインスタンスで極端に遅い場合がある
- `Decidable` インスタンスがないと使えない
- `native_decide` は信頼できるコンパイラに依存（公理的に完全ではない）
- `Nat.Prime 1000003` のような大数では遅い → `norm_num` の方が効率的

## コードサンプル

### サンプル 1: 基本的な等式
```lean
example : 2 + 3 = 5 := by decide
```

### サンプル 2: Bool の評価
```lean
example : (true && false) = false := by decide
```

### サンプル 3: native_decide で高速化
```lean
example : (List.range 100).length = 100 := by native_decide
```

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `norm_num` | 数値計算 | 数値の計算・素数判定に特化 |
| `omega` | 線形算術 | Nat/Int の不等式 |
| `bv_decide` | ビットベクタ | ビットベクタの決定手続き |
| `simp` | 簡約 | もっと汎用的な簡約 |

## 参照
- [Lean4 公式リファレンス — decide](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#decide)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
