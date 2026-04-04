# `simp?` — simp が使用する補題セットの特定

**カテゴリ**: 検索 | **定義元**: `Lean.Parser.Tactic.simpTrace` | **ソース**: Lean4 core

## 概要
`simp?` は `simp` を実行した上で、実際に使用された補題の最小セットを `simp only [...]` 形式で表示する。`simp` は強力だがどの補題を使ったか不透明なため、`simp?` で明示的な補題リストに変換することで証明の安定性・再現性を向上できる。CI やライブラリでは `simp only [...]` が推奨されるため、`simp?` はその変換ツールとして重要。

## ゴールパターン

**適用対象**: `simp` で簡約可能な任意のゴール。使用した補題リストをサジェスチョンとして表示する。

## 構文
```lean
simp?                        -- simp で使われた補題セットを表示
simp? at h                   -- 仮定 h に対して実行
simp? [extra_lemma]          -- 追加補題を含めて実行
simp? (config := { ... })   -- 設定付きで実行
```

## 必須 import
Lean4 core 組み込み。追加 import 不要。

## Pros
- `simp` → `simp only [...]` への変換で証明を安定化
- Mathlib CI の lint で `simp` 単体より `simp only` が推奨される場面に対応
- 複数の `simp` 補題のうちどれが実際に必要か特定できる
- 通常の `simp` と同じオプション・構文が使える

## Cons
- 実行時間は `simp` と同等（大きなゴールでは遅い場合あり）
- 最終証明では `simp?` の出力で置き換えること（そのまま残さない）
- `simp` 自体で閉じないゴールでは無意味
- 補題セットが大きくなると表示が長くなる

## コードサンプル

### サンプル 1: 基本的な算術の simp 補題を特定
```lean
-- ⊢ a + 0 = a
-- simp? が "Try this: simp only [Nat.add_zero]" と表示
example (a : Nat) : a + 0 = a := by
  simp?
```

### サンプル 2: リスト操作の補題を特定
```lean
-- ⊢ [].length = 0
-- simp? が "Try this: simp only [List.length_nil]" と表示
example : ([] : List Nat).length = 0 := by
  simp?
```

### サンプル 3: 仮定に対して使用
```lean
-- h : a + 0 + 0 = b
-- ⊢ a = b
-- simp? at h で仮定を簡約して必要な補題を特定
example (a b : Nat) (h : a + 0 + 0 = b) : a = b := by
  simp? at h  -- "Try this: simp only [Nat.add_zero] at h" と表示
  exact h
```

## `simp` / `simp only` / `simp?` の関係

| タクティク | 動作 | 用途 |
|---|---|---|
| `simp` | 登録済み全補題で簡約 | 探索・プロトタイプ |
| `simp only [...]` | 指定補題のみで簡約 | 安定した最終証明 |
| `simp?` | `simp` 実行後、使用補題を表示 | `simp` → `simp only` への変換 |

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `simp` | 自動簡約 | 補題セットの特定が不要な場合 |
| `simp only` | 明示簡約 | 補題を明示して安定化した場合 |
| `rw?` | 書き換え検索 | 個別の書き換え規則を探す場合 |
| `exact?` | 完全一致検索 | 簡約ではなく直接閉じたい場合 |
| `norm_num` | 数値計算 | 数値リテラルの計算に特化 |

## 参照
- [Lean4 公式リファレンス — simp](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#simp)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
