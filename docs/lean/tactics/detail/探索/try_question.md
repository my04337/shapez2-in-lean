# `try?` — 登録済みタクティクの試行とサジェスチョン

**カテゴリ**: 検索 | **定義元**: `Lean.Parser.Tactic.tryTrace` | **ソース**: Lean4 core (Lean 4.x+)

## 概要
`try?` は登録されたタクティクを現在のゴールに対して試行し、成功したものをサジェスチョンとして報告する。`hint` と似た役割を持つが、`try?` は Lean4 core に組み込まれており、Mathlib なしで利用可能。成功したタクティクを "Try this:" 形式で表示し、そのまま証明にコピーできる。

## ゴールパターン

**適用対象**: 任意のゴール。成功したタクティクをサジェスチョンとして表示する。

## 構文
```lean
try?                     -- 登録済みタクティクを試行して表示
```

## 必須 import
Lean4 core 組み込み。追加 import 不要。
Mathlib がある場合、`hint` で登録されたタクティクも含めて試行される。

## Pros
- Lean4 core のみで利用可能（Mathlib 不要）
- `exact?`, `rfl`, `trivial`, `decide` など基本タクティクを一括試行
- "Try this:" 形式で結果をそのまま証明に貼り付け可能
- どのタクティクを使えばいいか分からない初学者に有用

## Cons
- 全タクティクを試すため実行が遅い場合がある
- 最終的な証明では結果で置き換えること（`try?` のまま残さない）
- 見つかるタクティクは登録済みのもののみ
- `hint`（Mathlib）の方が登録タクティクが多い場合がある

## コードサンプル

### サンプル 1: 自明な等式
```lean
-- ⊢ 42 = 42
-- try? が "Try this: rfl" と表示
example : 42 = 42 := by
  try?
```

### サンプル 2: 自然数の不等式
```lean
-- ⊢ 3 < 5
-- try? が "Try this: decide" 等を提示
example : 3 < 5 := by
  try?
```

### サンプル 3: 仮定から直接閉じるケース
```lean
-- h : P
-- ⊢ P
-- try? が "Try this: exact h" と表示
example (h : P) : P := by
  try?
```

## `hint` との比較

| 観点 | `try?` | `hint` |
|---|---|---|
| ソース | Lean4 core | Mathlib |
| Mathlib 不要 | ✅ | ❌ |
| 登録タクティク数 | 基本セット | Mathlib 拡張含む |
| `@[hint]` 連携 | 限定的 | 完全対応 |
| 推奨場面 | Mathlib なし / 軽量探索 | Mathlib あり / 網羅的探索 |

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `hint` | Mathlib 版の一括試行 | Mathlib 環境で網羅的に探索したい場合 |
| `exact?` | 補題検索 | 補題レベルの検索に特化 |
| `apply?` | 適用検索 | apply 可能な補題を探す場合 |
| `rw?` | 書き換え検索 | 書き換え規則を探す場合 |
| `simp?` | simp 検索 | simp 補題を特定したい場合 |

## 参照
- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
