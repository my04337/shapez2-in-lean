# `native_decide` — ネイティブコンパイルによる高速決定手続き

**カテゴリ**: 決定手続き | **定義元**: `Lean.Parser.Tactic.nativeDecide` | **ソース**: Lean4 core

## 概要
`native_decide` は `Decidable` インスタンスを持つ命題を、カーネル評価ではなくネイティブコードにコンパイル（`#eval` 相当）して真偽を判定する。`decide` と同じ対象を扱うが、大規模な計算で桁違いに高速。ただし、コンパイラの正しさを信頼する公理 `Lean.ofReduceBool` を導入するため、証明の信頼度はやや下がる。

## ゴールパターン

**適用前**
```lean
⊢ Decidable な命題  -- 例: (List.range 1000).length = 1000
```

**適用後**: ゴールが閉じる

## 構文
```lean
native_decide            -- ネイティブコードで高速証明
```

## 必須 import
Lean4 core 組み込み。追加 import 不要。

## Pros
- `decide` と比べ大規模なインスタンスで劇的に高速
- `List.range 10000` や `Fin` 上の全探索など、カーネル評価がタイムアウトするケースに有効
- 構文は `decide` と同一の文脈で使える

## Cons
- コンパイラの正しさを信頼する公理を導入する（完全な型安全ではない）
- Mathlib CI ではデフォルトで使用を推奨しない場面がある
- `decide` と異なり、証明項がカーネルで検証されない
- コンパイル自体に数秒かかるため、小さな命題では `decide` の方が速い

## コードサンプル

### サンプル 1: 大きなリストの等式
```lean
-- ⊢ (List.range 500).length = 500
-- decide だとタイムアウトするケースでも高速に閉じる
example : (List.range 500).length = 500 := by native_decide
```

### サンプル 2: Fin 上の全探索
```lean
-- ⊢ ∀ (x : Fin 8), x.val < 8
-- Fin 8 の全要素を列挙して検証
example : ∀ (x : Fin 8), x.val < 8 := by native_decide
```

### サンプル 3: Bool 関数の大きな入力に対する検証
```lean
-- ⊢ (List.range 100).all (· < 100) = true
-- 100 要素すべてが条件を満たすことをネイティブ実行で確認
example : (List.range 100).all (· < 100) = true := by native_decide
```

## `decide` との使い分け

| 観点 | `decide` | `native_decide` |
|---|---|---|
| 実行方式 | カーネル評価 | ネイティブコンパイル |
| 速度（小規模） | 高速 | コンパイルオーバーヘッドあり |
| 速度（大規模） | 極端に遅い / タイムアウト | 高速 |
| 信頼度 | カーネルが検証 | コンパイラを信頼（公理導入） |
| 推奨場面 | 小〜中規模の具体的命題 | 大規模計算・全探索 |

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `decide` | カーネル版 | 小規模で信頼度を優先する場合 |
| `norm_num` | 数値計算 | 素数判定・数値計算に特化 |
| `omega` | 線形算術 | Nat/Int の不等式・等式 |
| `simp` | 簡約 | 一般的な簡約が十分な場合 |

## 参照
- [Lean4 公式リファレンス — native_decide](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#native_decide)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
