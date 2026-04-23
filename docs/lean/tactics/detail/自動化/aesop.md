# `aesop` — ルールベースの汎用証明探索

**カテゴリ**: 自動化 | **定義元**: `Aesop.Frontend.Parser.aesopTactic` | **ソース**: Aesop (Lean4 パッケージ)

## 概要
`aesop` は `@[aesop]` 属性のついたルール（`simp` 補題、`apply` 補題、`cases` ルール等）を組み合わせて証明を探索する汎用自動証明タクティク。バックトラッキング付きの探索を行い、見つかった証明を再構成する。

## ゴールパターン

**適用対象**: 任意のゴール（ルールセット次第）

## 構文
```lean
aesop                             -- デフォルトルールで探索
aesop?                            -- 見つかった証明を表示
aesop (add norm simp [h])         -- simp ルールを追加
aesop (add safe apply [lemma])    -- apply ルールを追加
aesop (add unsafe 50% apply [h])  -- 確率付き unsafe ルール
aesop (erase [rule_name])         -- ルールを除外
```

## 必須 import
```lean
import Aesop
```

## オプション一覧
| 構文 | 意味 |
|---|---|
| `(add norm simp [...])` | simp 正規化ルールを追加 |
| `(add safe apply [...])` | 安全な apply ルールを追加 |
| `(add unsafe N% apply [...])` | N% の確率で試す unsafe ルール |
| `(erase [...])` | 指定ルールを除外 |
| `(config := { maxRuleApplications := n })` | 探索上限を設定 |

## Pros
- `@[aesop]` エコシステムでドメイン特化の自動証明が構築できる
- `aesop_cat` (圏論), `aesop_graph` (グラフ) など専用バリアントが存在
- `aesop?` で再現可能な証明に変換できる

## Cons
- ルールセットが不十分だと何も見つからない
- 探索空間が大きいと遅い
- 探索上限を超えると失敗（`maxRuleApplications` 調整が必要なことも）
- `grind` の方が強力なケースが増えている

## コードサンプル

### サンプル 1: 基本
```lean
example (h : P → Q) (hp : P) : Q := by aesop
```

### サンプル 2: aesop? で安定版に
```lean
example (h : P → Q) (hp : P) : Q := by
  aesop? -- "Try this: exact h hp" など表示
```

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `aesop?` | 成功時に使用したタクティク列を提案する |
| `aesop_unfold` | 展開ルールのみ適用する特化版 |

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `grind` | SMT ベース | より強力な自動化。aesop が失敗する場合の候補 |
| `simp` | 簡約 | simp 補題のみで十分な場合 |
| `tauto` | 命題論理 | 純粋な命題論理の場合 |
| `decide` | 決定手続き | Decidable な場合 |
| `exact?` | 検索 | 単一補題の検索 |

## 参照
- [Aesop 活用ガイド（S2IL プロジェクト向け）](../../aesop-guide.md) — ルール設計基準・良い/悪い使い方・デバッグ方法
- [Aesop リポジトリ](https://github.com/leanprover-community/aesop)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
