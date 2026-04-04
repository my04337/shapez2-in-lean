# `done` — すべてのゴールが解決済みであることを表明

**カテゴリ**: 制御 | **定義元**: `Lean.Parser.Tactic.done` | **ソース**: Lean4 core

## 概要
`done` はすべてのゴールが解決済みであること（ゴールが0個であること）を表明する。ゴールが残っている場合は、残りのゴール一覧とともにエラーを報告する。証明の末尾に置くことで「ここで証明が完了しているべき」という意図を明示でき、将来の定義変更で証明が不完全になった場合に即座にエラーを検出できる。

## ゴールパターン

**適用前**（ゴールが0個の場合）
```lean
-- (ゴールなし)
```

**適用後**
```lean
-- 成功（何も起きない）
```

**適用前**（ゴールが残っている場合）
```lean
⊢ P
⊢ Q
```

**適用後**
```lean
-- エラー: unsolved goals
-- ⊢ P
-- ⊢ Q
```

## 構文
```lean
done   -- ゴールが残っていればエラー
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
なし。引数もオプションもない。

## Pros
- 証明の完了を明示的にアサートできる
- 将来の変更による回帰を早期検出できる
- `sorry` の消し忘れを防ぐチェックポイントとして使える

## Cons
- 証明が未完成の段階では使えない（常にエラーになる）
- `by tac1; tac2` のブロック末尾では暗黙的に `done` が実行されるため、冗長なことが多い
- インタラクティブな証明開発中は邪魔になることがある

## コードサンプル

### サンプル 1: 基本的な使い方
```lean
example (n : Nat) : n = n := by
  rfl
  done  -- 証明完了を明示（rfl でゴールは閉じている）
```

### サンプル 2: ゴールが残っている場合のエラー
```lean
-- 以下はエラーになる
-- example (n : Nat) : n = n ∧ n ≤ n := by
--   constructor
--   · rfl
--   done  -- エラー: unsolved goals ⊢ n ≤ n
```

### サンプル 3: 複雑な証明での完了チェック
```lean
example (a b : Nat) (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  omega
  done  -- omega で全ゴールが閉じたことを確認
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `solve` | ゴール閉鎖の検証 | タクティクを渡してゴール閉鎖を保証するなら `solve` |
| `sorry` | 証明の一時的なスキップ | 未完成の証明を一時的にパスするなら `sorry` |
| `trivial` | 自明なゴールの閉鎖 | 自動的にゴールを閉じるなら `trivial` |

## 参照
- [Lean4 公式リファレンス — done](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
