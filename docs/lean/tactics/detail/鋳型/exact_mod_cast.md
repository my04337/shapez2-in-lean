# `exact_mod_cast` — キャストを正規化して exact 適用

**カテゴリ**: キャスト / 仮定依存 | **定義元**: `Lean.Parser.Tactic.tacticExact_mod_cast_` | **ソース**: Lean4 core

## 概要
`exact_mod_cast` は `norm_cast` によるキャスト正規化を行った上で `exact` を適用するタクティク。ゴールと仮定がキャストの違いだけで一致する場合に、キャスト差異を自動的に吸収してゴールを閉じる。`assumption_mod_cast` は仮定を自動検索する版。

## ゴールパターン

**適用前**（`exact_mod_cast h`）
```lean
n : Nat
h : n < 5
⊢ (↑n : Int) < 5
```

**適用後**: ゴールが閉じる

**適用前**（逆方向のキャスト）
```lean
n : Nat
h : (↑n : Int) < 5
⊢ n < 5
```

**適用後**: ゴールが閉じる

## 構文
```lean
exact_mod_cast h          -- 仮定 h をキャスト正規化して exact
exact_mod_cast expr        -- 式をキャスト正規化して exact
assumption_mod_cast        -- 仮定を自動検索してキャスト正規化
```

## 必須 import
Lean4 core 組み込み。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `exact_mod_cast h` | 仮定 h をキャスト正規化して適用 |
| `exact_mod_cast expr` | 任意の式をキャスト正規化して適用 |
| `assumption_mod_cast` | 仮定を自動検索（`exact_mod_cast` + `assumption`） |

## Pros
- キャストの違いだけで一致する場合にワンステップで閉じられる
- `norm_cast ; exact h` の省略形として可読性が高い
- `Nat ↪ Int ↪ Rat ↪ Real` のキャストチェインを自動処理

## Cons
- キャスト以外の差異がある場合は失敗する
- `norm_cast` の正規化が不完全な場合は動かない
- 複雑なキャストでは明示的な `push_cast` / `norm_cast` の方が制御しやすい

## コードサンプル

### サンプル 1: Nat → Int のキャスト吸収
```lean
example (n : Nat) (h : n < 10) : (↑n : Int) < 10 := by
  exact_mod_cast h
  -- ゴールが閉じる: h の n < 10 がキャスト越しに一致
```

### サンプル 2: Int → Nat 方向のキャスト吸収
```lean
example (n : Nat) (h : (↑n : Int) + 1 > 0) : n + 1 > 0 := by
  exact_mod_cast h
  -- ゴールが閉じる: Int 上の仮定を Nat 上のゴールに適用
```

### サンプル 3: assumption_mod_cast で自動検索
```lean
example (n m : Nat) (h₁ : n < m) (h₂ : m < 100) : (↑n : Int) < ↑m := by
  assumption_mod_cast
  -- 仮定から h₁ : n < m を見つけ、キャスト正規化して適用
```

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `norm_cast` | キャスト正規化 | ゴール全体を正規化（閉じない場合も） |
| `push_cast` | キャスト分配 | キャストを葉に押し込む |
| `exact` | 直接適用 | キャスト差異がない場合 |
| `assumption` | 仮定検索 | キャスト差異がない場合 |
| `omega` | 線形算術 | キャスト込みで算術ゴールを閉じる |

## 参照
- [Lean4 公式リファレンス — norm_cast tactics](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#norm_cast-tactics)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
