# `rw_mod_cast` — キャスト正規化 + rw

**カテゴリ**: 書換 | **定義元**: `Mathlib.Tactic.NormCast` | **ソース**: Mathlib

---

## 概要

`rw_mod_cast [h]` は `norm_cast` による型キャスト正規化と `rw` を組み合わせたタクティクである。まずキャストを正規化した状態で `h` を適用し、その後再びキャストを正規化する。キャストが絡む書き換えで `rw` が型不一致で失敗する場合に有効。

---

## ゴールパターン

**適用前**
```lean
⊢ (n : Int) + (m : Int) = ((n + m : Nat) : Int)
```

**適用後**（再書き換えで閉鎖）

---

## 構文

```lean
rw_mod_cast [h₁, h₂]
rw_mod_cast [← h]
```

---

## 必須 import

```lean
import Mathlib.Tactic.NormCast
```

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `rw_mod_cast [h]` | キャスト正規化しつつ `h` で書き換え |
| `rw_mod_cast [← h]` | 逆方向でキャスト正規化書き換え |
| `rw_mod_cast [h₁, h₂]` | 複数ルールを順に適用 |

---

## Pros（使うべき場面）

- `rw` がキャスト不一致で失敗する場合
- `Nat` → `Int` 等のキャストを含む式の書き換え
- `norm_cast` + `rw` の手順を 1 行にまとめたい場合

---

## Cons（注意・失敗ケース）

- キャストが絡まない場合は通常の `rw` で十分
- Mathlib import が必要
- `push_cast` + `rw` で代替できる場合もある

---

## コードサンプル

### サンプル 1: キャスト越しの書き換え

```lean
import Mathlib.Tactic.NormCast

example {n m : Nat} (h : n = m) : (n : Int) * 2 + 1 = (m : Int) * 2 + 1 := by
  rw_mod_cast [h]
```

### サンプル 2: push_cast との比較

```lean
import Mathlib.Tactic.NormCast

-- rw_mod_cast はキャストを自動処理しながら h による書き換えを行う
example {n m : Nat} (h : n = m) : (n : Int) + 1 = (m : Int) + 1 := by
  rw_mod_cast [h]
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `rw` | 基本版 | キャスト不要なら `rw` |
| `norm_cast` | 正規化 | キャスト正規化のみ |
| `push_cast` | 内側分配 | キャストを内側に揃えてから `rw` |
| `assumption_mod_cast` | 仮定版 | キャスト正規化 + assumption |

---

## 参照

- [Mathlib4 ドキュメント — NormCast](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/NormCast.html)

---
> **出典**: [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
