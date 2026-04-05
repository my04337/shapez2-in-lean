# `norm_cast` — 型キャストの正規化

**カテゴリ**: キャスト | **定義元**: `Lean.Parser.Tactic.normCast` | **ソース**: Lean4 core (Batteries)

## 概要
`norm_cast` は `@[norm_cast]` / `@[push_cast]` 属性の補題を使い、型キャスト（`Nat → Int`, `Int → Real` 等）を正規化する。`push_cast` はキャストを内側に押し込み、`norm_cast` は全体を正規化してゴールを閉じようとする。

## ゴールパターン

**適用前**
```lean
⊢ (↑n : Int) + (↑m : Int) = ↑(n + m)
```

**適用後**: ゴールが閉じる

## 構文
```lean
norm_cast                 -- キャストを正規化してゴールを閉じる
push_cast                 -- キャストを内側に押す
push_cast at h            -- 仮定のキャストを内側に押す
norm_cast at h            -- 仮定を正規化
```

## 必須 import
Lean4 core / Batteries / Mathlib に @[norm_cast] 補題群あり。基本のタクティク自体は core。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `at h` | 仮定 h に適用 |
| `at *` | 全仮定とゴールに適用 |
| `[h₁, h₂]` | 追加補題を使用 |

## Pros
- `Nat ↪ Int ↪ Real` のようなキャストチェインを自動正規化
- 型変換の煩雑な書き換えを自動化
- `push_cast` と組み合わせてキャストの位置を柔軟に制御

## Cons
- `@[norm_cast]` 補題が不足していると正規化が不完全
- カスタム型のキャストには補題の追加が必要
- 目的と異なる方向にキャストが移動することがある（`push_cast` / `pull_cast` で方向を指定）

## コードサンプル

### サンプル 1: 基本
```lean
example (n m : Nat) : (↑(n + m) : Int) = ↑n + ↑m := by push_cast; ring
```

### サンプル 2: 仮定の正規化
```lean
example (n : Nat) (h : (↑n : Int) < 5) : n < 5 := by exact_mod_cast h
```

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `push_cast` | キャストを内側に | キャストを葉に向けて押す |
| `exact_mod_cast` | exact + cast処理 | キャスト付きで exact |
| `simp` | 汎用簡約 | @[simp] にキャスト補題もある |
| `omega` | 算術 | Nat/Int の算術。キャスト事前処理と組み合わせ |

## 参照
- [Lean4 公式リファレンス — norm_cast](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#norm_cast-tactics)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
