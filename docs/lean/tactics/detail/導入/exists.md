# `exists` — 存在量化子のウィットネス提供（core 版）

**カテゴリ**: 導入 | **定義元**: `Lean.Parser.Tactic.«tacticExists_,,»` | **ソース**: Lean4 core

---

## 概要

`exists` は Lean4 core 組み込みの存在量化子証明タクティクで、`⊢ ∃ x, P x` のゴールに対してウィットネスを提供する。内部的には `refine ⟨e, ?_⟩` と同様の動作をし、残ったゴールに `try trivial` を試行する。Mathlib の `use` と似ているが、こちらは追加 import なしで利用可能。

<!-- 情報不十分: exists と use の正確な挙動差異は Lean バージョンにより変動する可能性あり。要確認 -->

---

## ゴールパターン

**適用前**
```lean
⊢ ∃ n : Nat, n = 0
```

**適用後** (`exists 0`)
```lean
⊢ 0 = 0
```

**適用前**（複数ウィットネス）
```lean
⊢ ∃ a b : Nat, a + b = 5
```

**適用後** (`exists 2, 3`)
```lean
⊢ 2 + 3 = 5
```

---

## 構文

```lean
exists e               -- ウィットネス e を提供
exists e₁, e₂         -- 複数の値をカンマ区切りで提供
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 説明 |
|---|---|
| `exists e` | 単一のウィットネスを提供 |
| `exists e₁, e₂` | 入れ子の `∃` に対して順に提供 |

---

## Pros（使うべき場面）

- Lean4 core のみで使える（Mathlib 不要）
- `∃` の証明を 1 行で記述できる
- `use` が使えない環境での代替手段

---

## Cons（注意・失敗ケース）

- Mathlib 環境では `use` の方が機能が豊富（`use` は Sigma 型にも対応）
- `try trivial` で閉じない場合は追加証明が必要
- キーワード `exists` は Lean の予約語ではないが、`∃` 記号と紛らわしい場合がある

---

## コードサンプル

### サンプル 1: 基本的な存在量化子
```lean
example : ∃ n : Nat, n = 0 := by
  exists 0
  -- ゴールは ⊢ 0 = 0 → rfl で自動閉じ
```

### サンプル 2: 複数ウィットネスの提供
```lean
example : ∃ a b : Nat, a + b = 10 := by
  exists 3, 7
  -- ⊢ 3 + 7 = 10  （自動で閉じる）
```

### サンプル 3: 残りの証明が必要なケース
```lean
example : ∃ n : Nat, n > 0 ∧ n % 2 = 0 := by
  exact ⟨4, by norm_num, by native_decide⟩
  -- exists でウィットネスを提供し、残りを norm_num / native_decide で閉じる
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `use` | Mathlib 版 | より豊富な機能（Sigma 型対応等） |
| `constructor` | 汎用 | ∃ 以外の帰納型にも対応するがメタ変数が残る |
| `refine ⟨e, ?_⟩` | Term モード混合 | より細かい制御が必要な場合 |
| `exact ⟨e, h⟩` | Term モード | 証明全体を一度に構成 |

---

## 参照
- [Lean4 公式リファレンス — exists](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#exists)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
