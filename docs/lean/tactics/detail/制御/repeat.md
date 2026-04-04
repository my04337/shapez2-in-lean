# `repeat` — タクティクを失敗するまで繰り返す

**カテゴリ**: 制御 | **定義元**: `Lean.Parser.Tactic.tacticRepeat_` | **ソース**: Lean4 core

## 概要
`repeat` は指定したタクティクを、失敗するまで繰り返し適用する。毎回の適用が成功する限り繰り返し、最初の失敗で停止する。**部分的に失敗した場合はその回の変更がロールバック**され、直前の成功状態が維持される。有限回で失敗が保証されるタクティクに対して使い、無限ループに注意が必要。

## ゴールパターン

**適用前**（`repeat apply And.intro`）
```lean
⊢ A ∧ B ∧ C
```

**適用後**
```lean
-- 3 回 And.intro が適用され、各 conjunct がサブゴールに
⊢ A
⊢ B
⊢ C
```

## 構文
```lean
repeat tac            -- tac を失敗まで繰り返す
repeat (tac1; tac2)   -- タクティク列を繰り返す
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `repeat tac` | tac を失敗するまで繰り返す（0回成功でも失敗しない） |

## Pros
- 繰り返し構造の分解（`And.intro` 等）を簡潔に書ける
- 停止条件を明示する必要がない（失敗で自動停止）
- 0回適用でも成功扱いのため、空ケースも安全に扱える

## Cons
- 毎回ゴールを変更するタクティクだと無限ループに陥る危険がある
- 何回適用されたか分かりにくいため、デバッグ時に注意が必要
- `iterate n` で回数を明示した方が安全な場面も多い

## コードサンプル

### サンプル 1: And の分解
```lean
example (ha : A) (hb : B) : A ∧ B := by
  repeat apply And.intro
  -- ⨢ A
  -- ⨢ B
  · exact ha
  · exact hb
```

### サンプル 2: リストの各ゴールを rfl で閉じる
```lean
example : (1, 2, 3) = (1, 2, 3) := by
  repeat constructor
  -- 各成分に分解される
  -- すべて rfl で自動閉鎖、またはさらに repeat で処理
```

### サンプル 3: intro を繰り返して仮定を全導入
```lean
example : P → Q → R → P := by
  repeat intro
  -- hp : P, hq : Q, hr : R ⊢ P
  assumption
```

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `repeat'` | ゴールが進展しなくなったら停止する安全版 |
| `repeat1` | 最低 1 回は成功を要求する |
| `repeat1'` | `repeat'` + 最低 1 回の成功を要求 |

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `iterate` | 回数指定の繰り返し | 正確に n 回適用したいなら `iterate n` |
| `try` | 1回の試行 | 1回だけ試行するなら `try` |
| `first` | 分岐 | 複数候補から選択するなら `first` |
| `simp` | 繰り返し書換 | 等式の繰り返し書換には `simp` が適切 |

## 参照
- [Lean4 公式リファレンス — repeat](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
