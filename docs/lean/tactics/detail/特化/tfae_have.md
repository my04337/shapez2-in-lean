# `tfae_have` — TFAE に含意仮定を追加する

**カテゴリ**: 特化 | **定義元**: `Mathlib.Tactic.TFAE` | **ソース**: Mathlib

---

## 概要

`tfae_have i → j` は TFAE（The Following Are Equivalent）証明において、リスト中の `i` 番目の命題から `j` 番目の命題への含意を仮定として追加し、その証明をサブゴールとして生成する。`→`, `←`, `↔` が使える。

---

## ゴールパターン

**適用前**
```lean
⊢ TFAE [P₁, P₂, P₃]
```

**適用後**（`tfae_have 1 → 2`）
```lean
⊢ P₁ → P₂    -- サブゴール（含意の証明）
-- 元のゴールも残る
```

---

## 構文

```lean
tfae_have i → j         -- i → j の含意
tfae_have i ← j         -- j → i の含意
tfae_have i ↔ j         -- 同値
tfae_have h : i → j     -- 名前付き
```

---

## 必須 import

```lean
import Mathlib.Tactic.TFAE
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `tfae_have i → j` | i番目 → j番目の含意を追加 |
| `tfae_have i ← j` | j番目 → i番目の含意を追加 |
| `tfae_have i ↔ j` | 同値を追加 |
| `tfae_have h : i → j` | 仮定名 `h` を指定 |

---

## Pros（使うべき場面）

- TFAE 証明の構造的な構築
- 1-indexed で直感的な指定
- `tfae_finish` と組み合わせて自動完了

---

## Cons（注意・失敗ケース）

- TFAE ゴール以外では使えない
- インデックスが範囲外だとエラー
- 全てのサイクルを作らないと `tfae_finish` が失敗

---

## コードサンプル

### サンプル 1: 含意の追加

```lean
import Mathlib.Tactic.TFAE

example (P Q : Prop) (h₁ : P → Q) (h₂ : Q → P) : TFAE [P, Q] := by
  tfae_have 1 → 2 := h₁
  tfae_have 2 → 1 := h₂
  tfae_finish
```

### サンプル 2: 同値の直接追加

```lean
import Mathlib.Tactic.TFAE

example (P Q : Prop) (h : P ↔ Q) : TFAE [P, Q] := by
  tfae_have 1 ↔ 2 := h
  tfae_finish
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `tfae_finish` | 仕上げ | 全サイクルが揃ったら `tfae_finish` |
| `have` | 汎用版 | TFAE 以外の仮定追加 |
| `constructor` | 同値分解 | 単一 `↔` なら `constructor` |

---

## 参照

- [Mathlib4 ドキュメント — TFAE](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/TFAE.html)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
