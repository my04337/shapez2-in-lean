# `apply` / `exact` / `refine` — 補題・仮定の適用

**カテゴリ**: 補題適用 | **定義元**: `Lean.Parser.Tactic.apply` / `Lean.Parser.Tactic.exact` / `Lean.Parser.Tactic.refine` | **ソース**: Lean4 core

## 概要
ゴールに対して定理・補題・仮定を適用する3つの基本タクティク。`exact` はゴールを完全に閉じる項を与え、`apply` は結論が一致する補題を適用して前提をサブゴールにし、`refine` は穴 `?_` 付きの項を与えてサブゴールを生成する。

## ゴールパターン

### `exact e`
**適用前**: `⊢ P`
**適用後**: ゴールが閉じる（`e : P` のとき）

### `apply h`
**適用前**: `h : A → B → P` と `⊢ P`
**適用後**:
```lean
-- ゴール 1: ⊢ A
-- ゴール 2: ⊢ B
```

### `refine ⟨?_, ?_⟩`
**適用前**: `⊢ A ∧ B`
**適用後**:
```lean
-- ゴール 1: ⊢ A
-- ゴール 2: ⊢ B
```

## 構文
```lean
exact e                  -- e でゴールを閉じる
exact ⟨a, b⟩            -- 匿名コンストラクタで閉じる
apply h                  -- h の結論でゴールをマッチ、前提がサブゴール
apply h _ rfl            -- 一部の引数を指定
refine ⟨?_, ?_, rfl⟩    -- 穴 ?_ をサブゴールに
refine' ⟨_, _, rfl⟩     -- 旧版: _ もサブゴール化
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `exact e` | ゴールを完全に e で閉じる |
| `exact?` | ライブラリから exact で閉じる補題を検索 |
| `apply h` | h の結論をゴールにユニファイ |
| `apply (config := { newGoals := .all }) h` | 生成するサブゴールの順序を制御 |
| `refine e` | 明示的 `?_` のみサブゴール化 |
| `refine' e` | 暗黙の `_` もサブゴール化（旧式） |

## Pros（使うべき場面）
- **`exact`**: 証明の最終ステップ。型が完全に確定している場合
- **`apply`**: 逆方向推論の基本。ゴールから仮定に向かって分解
- **`refine`**: 部分的な項を与えて証明を進める。`exact` よりも柔軟

## Cons（注意・失敗ケース）
- **`exact`**: 型が一致しないと失敗。ユニフィケーション問題が起きやすい
- **`apply`**: 複数の候補がある場合、意図しない補題が選ばれることがある
- **`refine`**: `?_` の位置を間違えるとサブゴールが意図と異なる
- 全般: 型クラス解決の失敗で合成できないことがある

## コードサンプル

### サンプル 1: exact
```lean
example (h : P) : P := by
  exact h
```

### サンプル 2: apply で逆方向推論
```lean
example (h : P → Q) (hp : P) : Q := by
  apply h
  exact hp
```

### サンプル 3: refine で部分的に
```lean
example : ∃ n : Nat, n + 1 = 3 := by
  refine ⟨2, ?_⟩
  rfl
```

### サンプル 4: apply に引数を部分適用
```lean
example (h : ∀ x : Nat, x > 0 → x ≥ 1) : 5 ≥ 1 := by
  apply h
  omega
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `exact?` | 検索版 | ライブラリからゴールを閉じる補題を自動検索 |
| `apply?` | 検索版 | ライブラリからゴールに apply できる補題を自動検索 |
| `constructor` | apply の特化版 | ゴールが帰納型のとき最初のコンストラクタを適用 |
| `have` | 中間ゴール導入 | 新たな中間命題を導入して証明 |
| `specialize` | 仮定の特殊化 | ∀ 仮定に具体値を代入 |

## 参照
- [Lean4 公式リファレンス — Lemmas](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#tactic-ref-lemmas)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。