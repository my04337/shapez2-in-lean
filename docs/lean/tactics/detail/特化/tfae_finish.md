# `tfae_finish` — TFAE 証明の仕上げ

**カテゴリ**: 特化 | **定義元**: `Mathlib.Tactic.TFAE` | **ソース**: Mathlib

---

## 概要

`tfae_finish` は TFAE（The Following Are Equivalent）の証明を仕上げるタクティクである。`tfae_have` で十分な含意関係を追加した後、残りの同値関係を自動的に閉じる。TFAE リスト内の命題間の推移的閉包を計算してゴールを解決する。

---

## ゴールパターン

**適用前**（十分な `tfae_have` 後）
```lean
⊢ TFAE [P₁, P₂, P₃]
```

**適用後**: 自動閉鎖

---

## 構文

```lean
tfae_finish
```

---

## 必須 import

```lean
import Mathlib.Tactic.TFAE
```

---

## オプション一覧

特になし。`tfae_have` で追加された含意からサイクルを構成し閉じる。

---

## Pros（使うべき場面）

- TFAE 証明の最終ステップ
- 含意のサイクルを自動検出
- 推移的閉包による自動閉鎖

---

## Cons（注意・失敗ケース）

- `tfae_have` が不十分だと失敗
- 全命題間にサイクルが必要
- TFAE 以外のゴールには使えない

---

## コードサンプル

### サンプル 1: 基本的な TFAE

```lean
import Mathlib.Tactic.TFAE

example (P Q : Prop) (hpq : P → Q) (hqp : Q → P) : TFAE [P, Q] := by
  tfae_have 1 → 2 := hpq
  tfae_have 2 → 1 := hqp
  tfae_finish
```

### サンプル 2: 3 項の TFAE

```lean
import Mathlib.Tactic.TFAE

example (P Q R : Prop)
    (hpq : P → Q) (hqr : Q → R) (hrp : R → P) :
    TFAE [P, Q, R] := by
  tfae_have 1 → 2 := hpq
  tfae_have 2 → 3 := hqr
  tfae_have 3 → 1 := hrp
  tfae_finish
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `tfae_have` | 仮定追加 | TFAE の含意を追加 |
| `constructor` | 同値分解 | 単一の `↔` なら `constructor` |
| `tauto` | 命題論理 | 命題論理で閉じるなら `tauto` |

---

## 参照

- [Mathlib4 ドキュメント — TFAE](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/TFAE.html)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
