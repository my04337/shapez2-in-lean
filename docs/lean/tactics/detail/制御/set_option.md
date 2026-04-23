# `set_option` — タクティクブロック内でオプションを設定

**カテゴリ**: 制御 | **定義元**: `Lean.Parser.Tactic.set_option` | **ソース**: Lean4 core

---

## 概要

`set_option` はタクティクブロック内でLeanのオプション値を一時的に変更するタクティクである。
通常 `set_option` はコマンドレベルで使用するが、タクティク版はスコープが後続のタクティクブロックに限定される。
タイムアウト値の延長、再帰上限の変更、デバッグ出力の有効化などに使用する。

---

## ゴールパターン

**適用対象**: 任意（ゴールの型は変化しない）

**適用前**
```lean
⊢ P
```

**適用後**
```lean
-- ゴールは変化しない（オプションのみ変更）
⊢ P
```

---

## 構文

```lean
set_option <option> <value> in
<tactic>
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `set_option maxHeartbeats N in` | 計算ステップ上限を N に変更 |
| `set_option maxRecDepth N in` | 再帰深度上限を N に変更 |
| `set_option pp.all true in` | Pretty Printer で全情報を表示 |
| `set_option trace.Meta.Tactic.simp true in` | simp のトレース出力を有効化 |

---

## Pros（使うべき場面）

- 重い `simp` や `decide` のタイムアウトを局所的に回避できる
- デバッグ時にトレース出力を特定箇所だけ有効にできる
- スコープが限定されるため、プロジェクト全体への影響がない

---

## Cons（注意・失敗ケース）

- `maxHeartbeats` を大きくしすぎると型チェックが非常に遅くなる
- デバッグ用オプションを残したまま commit しないよう注意
- タクティクブロック外で使いたい場合はコマンドレベルの `set_option` を使う

---

## コードサンプル

### サンプル 1: maxHeartbeats の延長

```lean
example : (List.range 1000).length = 1000 := by
  -- ⊢ (List.range 1000).length = 1000
  set_option maxHeartbeats 400000 in
  native_decide
  -- ゴールなし（証明完了）
```

### サンプル 2: simp トレース出力

```lean
example (a b : Nat) (h : a = b) : b = a := by
  -- ⊢ b = a
  set_option trace.Meta.Tactic.simp true in
  simp [h]
  -- トレース出力でどの補題が使われたか確認できる
```

### サンプル 3: 再帰深度の変更

```lean
example : True := by
  -- ⊢ True
  set_option maxRecDepth 1024 in
  trivial
  -- ゴールなし（証明完了）
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `open ... in` | 名前空間 | スコープ限定の名前空間オープン |
| `simp` | 対象 | `set_option maxHeartbeats` で `simp` のタイムアウトを調整 |
| `decide` | 対象 | 大規模な `decide` に `maxHeartbeats` 延長が必要なことがある |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
