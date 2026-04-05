# `hint` — 登録済みタクティクの一括試行

**カテゴリ**: 検索 | **定義元**: `Mathlib.Tactic.Hint.hintStx` | **ソース**: Mathlib

## 概要
`hint` は `@[hint]` 属性で登録されたタクティクを現在のゴールに対して一括で試行し、成功したものを報告する。どのタクティクが有効か分からない場面で、候補を素早く絞り込むメタ的な探索ツール。`exact?` や `apply?` が単一の補題を探すのに対し、`hint` はタクティク自体を探索する。

## ゴールパターン

**適用対象**: 任意のゴール。成功したタクティクをサジェスチョンとして表示する。

## 構文
```lean
hint                     -- 登録済みタクティクを全て試す
```

## 必須 import
```lean
import Mathlib.Tactic.Hint
```

## デフォルトで登録されているタクティク（抜粋）
- `exact?`, `apply?`, `rfl`, `trivial`
- `simp`, `omega`, `norm_num`, `decide`
- `aesop`, `tauto`, `linarith`
- その他 `@[hint]` で登録された Mathlib タクティク

## Pros
- どのタクティクが有効か分からない時に候補を一括発見
- 登録済みの多数のタクティクを自動で試してくれる
- 学習時・探索時に「何を使えばいいか」のヒントが得られる
- カスタムタクティクも `@[hint]` で登録可能

## Cons
- 全タクティクを試すため実行が遅い（数十秒かかる場合あり）
- 最終的な証明では結果で置き換えること（`hint` のまま残さない）
- Mathlib import が必要
- 成功しても最適なタクティクとは限らない（複数成功する場合あり）

## コードサンプル

### サンプル 1: 基本的な命題
```lean
-- ⊢ True
-- hint が "Try this: trivial" 等を複数提示
example : True := by
  hint
```

### サンプル 2: 算術のゴール
```lean
-- ⊢ 1 + 1 = 2
-- hint が "Try this: decide" "Try this: norm_num" 等を提示
example : 1 + 1 = 2 := by
  hint
```

### サンプル 3: 論理式
```lean
-- h : P, hpq : P → Q
-- ⊢ Q
-- hint が "Try this: exact hpq h" "Try this: tauto" 等を提示
example (h : P) (hpq : P → Q) : Q := by
  hint
```

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `exact?` | 補題検索 | 補題レベルの検索に特化 |
| `apply?` | 適用検索 | apply 可能な補題を探す場合 |
| `rw?` | 書き換え検索 | 書き換え規則を探す場合 |
| `simp?` | simp 検索 | simp 補題を特定したい場合 |
| `aesop` | 自動証明 | 検索ではなく自動で閉じたい場合 |

## 参照
- [Mathlib4 ドキュメント — Hint](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Hint.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
