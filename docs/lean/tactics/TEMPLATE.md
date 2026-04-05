# タクティク詳細ページ — 標準テンプレート

> このファイルは `detail/` 以下の各タクティク詳細ページを作成する際のテンプレート仕様書である。

---

## テンプレート

詳細ページは `docs/lean/tactics/detail/<カテゴリ>/TACTIC_NAME.md` に作成する。
ファイル名はタクティク名をそのまま使用する（小文字、記号は適宜変換）。

以下のテンプレートをコピーして使用すること。

---

````markdown
# `tactic_name` — 一行での説明

**カテゴリ**: カテゴリタグ | **定義元**: `Lean.Parser.Tactic.XYZ` | **ソース**: Lean4 core / Mathlib

---

## 概要

2–4 文での説明。何をするタクティクか、どの証明フェーズで使うかを記述する。

---

## ゴールパターン

**適用前のゴール状態（典型例）**
```lean
-- 仮定
h : A ∧ B
-- ゴール
⊢ C
```

**適用後の状態**（`tactic_name h` 実行後）
```lean
h_left : A
h_right : B
⊢ C
```

> 複数のゴールが生成される場合は、ゴールを番号付きで列挙する。

---

## 構文

```lean
-- 最小形
tactic_name expr

-- バリアント
tactic_name [lemma1, lemma2]
tactic_name at h
tactic_name only [lemma] at h ⊢
```

---

## 必須 import

```lean
import Mathlib.Tactic.TacticName
```

*Lean4 core 組み込みの場合はこのセクションを省略。*

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `only [l₁, l₂]` | 指定した補題のみ使用（デフォルト補題集合を使わない） |
| `at h` | ゴールではなく仮定 `h` に適用 |
| `at *` | 全仮定とゴールに適用 |
| `[- id]` | `id` を除外 |

---

## Pros（使うべき場面）

- 条件 A である → このタクティクが最適/最速
- 条件 B である → 他の選択肢より確実に動く

---

## Cons（注意・失敗ケース）

- 失敗条件: ゴールが X の形でないとき
- パフォーマンス: `only` を付けないと遅い・不安定
- 脆弱性: `simp` と違い `simp only` を最終証明では推奨

---

## コードサンプル

### サンプル 1: 基本的な使い方

```lean
-- ゴール: h : P ∧ Q ⊢ P
example (h : P ∧ Q) : P := by
  rcases h with ⟨hp, _⟩
  exact hp
```

### サンプル 2: オプション付き

```lean
example : 2 + 2 = 4 := by
  simp only [Nat.add_def]
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `cases` | より基本的な代替 | `rcases` がパターン指定不可の場合は `cases` を使う |
| `obtain` | 組み合わせ | `have h := ...; rcases h with ...` の簡略形 |
| `rintro` | 組み合わせ | `intro` + `rcases` を同時に行う |

---

## 参照

- [Lean4 公式リファレンス — tactic_name](URL)
- [Mathlib ドキュメント](URL)
````

---

## Pros / Cons 記法規則

index.md の Pros/Cons 列を埋める際のルール:

### 共通ルール
- 1 セルに 1–2 項目まで（スペースの都合）
- 長文不可。1 行 30 字以内を目安
- 箇条書きは Markdown テーブルのため改行できない → `，` で区切る

### Pros の書き方
- 「どんなときに使うと最も有効か」を簡潔に
- 形式: `[条件] → ◎` または 自然文
- 例: `線形 Nat/Int 不等式 → 完全決定`, `simp 系より安定`

### Cons の書き方
- 「なぜ失敗するか」「どんな罠があるか」を具体的に
- 形式: `[失敗条件] → ✗` または 自然文
- 例: `実数・体には不適（linarith を使うこと）`, `証明最終版では simp only 化必須`

---

## 出典フッタ規則

各詳細ページの末尾に以下の出典フッタを記載すること:

```markdown
---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（MIT License）。
```
