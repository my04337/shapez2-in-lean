# `grind` — SMT ベースの自動証明

**カテゴリ**: 自動化 | **定義元**: `Lean.Parser.Tactic.grind` | **ソース**: Lean4 core

## 概要
`grind` は SMT ソルバーに着想を得た強力な自動証明タクティク。等式推論 (E-matching)、線形整数算術 (lia)、可換環ソルバー (ring)、ケース分割を組み合わせてゴールを解く。Lean 4 v4.15 以降で大幅に強化された。

## ゴールパターン

**適用対象**: 等式・不等式・論理式・リスト操作・配列操作など広範なゴール

## 構文
```lean
grind                              -- デフォルト設定で実行
grind?                             -- 等価な grind only を提案
grind [theorem_name]               -- 追加定理を E-matching に使用
grind only [theorem_name]          -- @[grind] 定理を使わず指定のみ
grind (ematch := n)                -- E-matching ラウンド数を設定
grind (gen := n)                   -- 最大世代数を設定
grind (splits := n)                -- 分岐深度を制限
grind -splitIte                    -- if-then-else の分割を無効化
grind -splitMatch                  -- match の分割を無効化
grind +splitImp                    -- → の分割を有効化
```

## 必須 import
Lean4 core 組み込み（v4.15+）。追加 import なし。

## オプション一覧
| 構文 | 意味 |
|---|---|
| `[name, ...]` | E-matching で追加使用する定理 |
| `only [name, ...]` | @[grind] を無視し指定のみ使用 |
| `(ematch := n)` | E-matching ラウンド数 |
| `(gen := n)` | 最大世代数（探索の深さ制限） |
| `(splits := n)` | 分岐深度の上限 |
| `-splitIte` / `-splitMatch` | 分割の無効化 |
| `+splitImp` | 含意の分割を有効化 |
| `-linarith` | 線形算術ソルバーを無効化 |

## Pros
- 等式推論 + 算術 + ケース分割を統合した強力な自動化
- `lia` (線形整数算術) と `ring` (可換環) ソルバーを内蔵
- `@[grind]` 属性で定理を登録でき、ドメイン特化のカスタマイズが可能
- `grind?` で `grind only` に変換でき安定版が得られる

## Cons
- 比較的新しいタクティクで API が変わる可能性がある
- 探索空間が大きいと遅くなる
- `omega` / `ring` で十分な場合はそちらの方が高速
- デバッグが難しい（失敗理由が分かりにくい）

## コードサンプル

### サンプル 1: 線形算術
```lean
example (x y : Int) : 2 * x + 4 * y ≠ 5 := by grind
```

### サンプル 2: 等式推論
```lean
example (f g : Nat → Nat) (h₁ : ∀ x, f (g x) = x) (h₂ : g b = a) : f a = b := by
  grind
```

### サンプル 3: 可換環
```lean
example [CommRing α] (x : α) : (x + 1) * (x - 1) = x ^ 2 - 1 := by grind
```

## バリアントと派生形

| バリアント | 概要 |
|---|---|
| `grind?` | 成功時に使用した手順を提案する |

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `omega` | 線形 Nat/Int | Nat/Int のみで十分な場合 |
| `ring` | 環の等式 | 純粋な環等式の場合 |
| `lia` | grind の lia のみ | grind の薄いラッパー。線形算術のみ |
| `aesop` | ルールベース探索 | @[aesop] ルールが豊富な場合 |
| `simp` | 簡約 | simp 補題で十分な場合 |
| `linarith` | 体の線形算術 | Real 等の場合 |

## 参照
- [Lean4 公式リファレンス — grind](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#grind)
- [The grind tactic 章](https://lean-lang.org/doc/reference/latest/The--grind--tactic/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
