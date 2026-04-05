# `rfl` — 反射律でゴールを閉じる

**カテゴリ**: 閉鎖 | **定義元**: `Lean.Parser.Tactic.tacticRfl` | **ソース**: Lean4 core

---

## 概要

`rfl` は、ゴールが `a = a` のような反射的等式（左辺と右辺が定義的に等しい）である場合に証明を閉じるタクティクである。
内部的には `Eq.refl` を適用する。`=` だけでなく、`HEq`、`Iff` など `@[refl]` 属性が付与された関係にも対応する。
定義的等価性（definitional equality）によって左辺と右辺が同一と判断できればよく、構文上の一致は不要。

---

## ゴールパターン

**適用前**
```lean
⊢ a = a
```

**適用後**
```lean
-- ゴールなし（証明完了）
```

---

## 構文

```lean
rfl
```

引数は取らない。

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `rfl` | 反射律でゴールを閉じる |

`rfl` にはオプションやバリアントはない。ただし Mathlib には `rfl'`（より積極的にユニフィケーションを行う変種）が存在する。

---

## Pros（使うべき場面）

- `a = a` や定義展開で一致するゴールを即座に閉じられる
- 計算結果の等式（例: `1 + 1 = 2`）は `rfl` で閉じることが多い
- 証明の最終ステップとして非常に頻繁に使われる

---

## Cons（注意・失敗ケース）

- 左辺と右辺が定義的に等しくない場合は失敗する（`simp` や `ring` で正規化が必要）
- 不透明定義（`opaque`）やバリア越しの等価性は判定できない
- `Decidable` インスタンスの違いなど、見た目は同じでも内部表現が異なる場合に失敗することがある

---

## コードサンプル

### サンプル 1: 基本的な反射律

```lean
example : 42 = 42 := by
  -- ⊢ 42 = 42
  rfl
  -- ゴールなし（証明完了）
```

### サンプル 2: 定義展開による一致

```lean
def double (n : Nat) : Nat := n + n

example : double 3 = 6 := by
  -- ⊢ double 3 = 6
  -- double 3 は定義的に 3 + 3 = 6 と等しい
  rfl
  -- ゴールなし（証明完了）
```

### サンプル 3: 構造体の等式

```lean
example : (1, 2) = (1, 2) := by
  -- ⊢ (1, 2) = (1, 2)
  rfl
  -- ゴールなし（証明完了）
```

---

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| [`rfl'`](../補題適用/refine'.md) | 完全簡約後に `rfl` を適用する |

## 関連タクティク| `exact` | 汎化 | `rfl` は `exact rfl` の省略形。`exact` は任意の項を渡せる |
| `rfl'` | 変種（Mathlib） | `rfl'` はより積極的にユニフィケーションを試みるが、Mathlib が必要 |
| `ac_rfl` | 拡張 | 可換性・結合性を考慮した反射律。`a + b = b + a` 等に対応 |
| `eq_refl` | 同義 | `Eq.refl` を直接使う項レベルの証明 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
- [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
