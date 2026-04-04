# `fail_if_no_progress` — 進捗がなければ失敗

**カテゴリ**: 制御 | **定義元**: `Mathlib.Tactic.failIfNoProgress` | **ソース**: Mathlib

---

## 概要

`fail_if_no_progress` は内部のタクティクがゴールを変化させなかった場合に失敗を報告するメタタクティクである。
`simp` や `norm_num` が何もしないのにサイレントに成功するケースを検出し、
繰り返しタクティク（`repeat`、`iterate` 等）の停止条件として利用できる。
証明の堅牢性を向上させ、不要なタクティクの残存を防ぐ。

---

## ゴールパターン

**適用対象**: 任意（内部タクティクの進捗を監視）

**適用前**
```lean
⊢ P
```

**適用後** （内部タクティクが進捗した場合）
```lean
-- 内部タクティクの結果に従う
```

**失敗** （内部タクティクが進捗しなかった場合）
```
tactic 'fail_if_no_progress' made no progress
```

---

## 構文

```lean
fail_if_no_progress <tactic>
fail_if_no_progress
  tac₁
  tac₂
```

---

## 必須 import

```lean
import Mathlib.Tactic.FailIfNoProgress
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `fail_if_no_progress tac` | `tac` が進捗しなければ失敗 |

---

## Pros（使うべき場面）

- `repeat` ループの停止条件として使用し無限ループを防ぐ
- 不要な `simp` の残存を検出できる（進捗なしで警告される）
- 証明のデバッグ時に、どのタクティクが実際に効果を持つか確認できる

---

## Cons（注意・失敗ケース）

- ゴールが変化しなくても仮定が変化する場合、進捗ありと判定されることがある
- 過度に使うと証明が冗長になる
- Mathlib の import が必要

---

## コードサンプル

### サンプル 1: repeat の停止条件

```lean
import Mathlib.Tactic.FailIfNoProgress

example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  -- ⊢ a = c
  repeat fail_if_no_progress rw [h₁]
  -- h₁ を適用後、2回目では進捗なしで repeat 停止
  -- ⊢ b = c
  exact h₂
```

### サンプル 2: simp の進捗確認

```lean
import Mathlib.Tactic.FailIfNoProgress

example (n : Nat) : n + 0 = n := by
  -- ⊢ n + 0 = n
  fail_if_no_progress simp
  -- simp が n + 0 を n に簡約 → 進捗あり → rfl で閉じる
```

### サンプル 3: 進捗なしで失敗する例

```lean
import Mathlib.Tactic.FailIfNoProgress

-- 以下はエラーになる（simp が何も変換しない場合）
-- example (n : Nat) : n = n := by
--   fail_if_no_progress simp [Nat.add_comm]
--   -- tactic 'fail_if_no_progress' made no progress
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `repeat` | 繰り返し | `fail_if_no_progress` で停止条件を制御 |
| `iterate` | 回数指定繰返し | 回数上限付きの繰り返し |
| `first` | 分岐 | 複数タクティクの最初に成功したものを使う |
| `try` | 失敗許容 | 失敗を無視。`fail_if_no_progress` とは逆の役割 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
