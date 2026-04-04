# `rw` — 等式による書き換え

**カテゴリ**: 書換 | **定義元**: `Lean.Parser.Tactic.rewriteSeq` | **ソース**: Lean4 core

## 概要
`rw` は等式 `a = b` を用いてゴールや仮定中の `a` を `b` に（または `←` で逆方向に）置換する。指定した位置を1回だけ書き換える点が `simp` との違い。

## ゴールパターン

**適用前**
```lean
h : a = b
⊢ f a = f b
```

**適用後**（`rw [h]`）
```lean
⊢ f b = f b  -- rfl で閉じる
```

## 構文
```lean
rw [h]               -- h : a = b で a → b に書き換え
rw [← h]             -- 逆方向: b → a に書き換え
rw [h₁, h₂, h₃]     -- 順次適用
rw [h] at hyp        -- 仮定 hyp を書き換え
rw [h] at hyp₁ hyp₂  -- 複数の仮定を書き換え
rw [h] at *          -- 全体を書き換え
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `[e₁, e₂, ...]` | 複数の書き換え規則を順次適用 |
| `[← e]` | 逆方向で書き換え |
| `at h` | 仮定 h で書き換え |
| `at *` | 全仮定とゴールで書き換え |

## Pros
- 書き換え位置が明確で予測可能
- 逆方向 `←` が使えて柔軟
- 定義定数を指定すると関連する等式補題で展開される
- 書き換え後に `rfl` で閉じることが多く、自動的に閉じてくれる

## Cons
- 最初に見つかった出現のみを書き換える（複数箇所の制御は `conv` が必要）
- `simp` と違い1つの規則ずつしか適用できない
- 書き換え対象がユニファイできないと失敗する（`erw` で緩和可能）
- 非終端 `rw` は脆弱（Mathlib では避けるべき）

## コードサンプル

### サンプル 1: 基本
```lean
example (h : a = b) : a + 1 = b + 1 := by
  rw [h]
```

### サンプル 2: 逆方向
```lean
example (h : a = b) : b + 1 = a + 1 := by
  rw [← h]
```

### サンプル 3: 定義展開
```lean
def double (n : Nat) := n + n
example : double 3 = 6 := by
  rw [double]  -- double の等式補題で展開
```

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `rw!` | より積極的なユニフィケーションで書き換え |
| `rw??` | 適用可能な書き換えルールを探索・提案 |

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `simp [h]` | 繰り返し書き換え | h を全出現に繰り返し適用 |
| `erw` | 緩い rw | ユニフィケーションが厳しいとき |
| `conv` | 位置指定 | 特定の部分式のみ書き換えたい場合 |
| `calc` | 段階的推論 | 複数ステップの等式チェイン |
| `subst` | 変数代入 | `h : x = e` で x を消去 |

## 参照
- [Lean4 公式リファレンス — Rewriting](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#tactic-ref-rw)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
