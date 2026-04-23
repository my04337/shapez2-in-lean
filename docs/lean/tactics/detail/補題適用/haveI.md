# `haveI` — インスタンスとして仮定を追加する

**カテゴリ**: 補題適用 | **定義元**: `Lean.Parser.Tactic.tacticHaveI_` | **ソース**: Lean4 core

---

## 概要

`haveI` は `have` と同様に仮定を追加するが、追加された仮定を型クラスインスタンスとしてもアクセス可能にする。`have h : Fintype α := ...` ではインスタンス推論に使われないが、`haveI : Fintype α := ...` ではインスタンスとして推論システムに登録される。

---

## ゴールパターン

**適用前**
```lean
⊢ P  -- Fintype α のインスタンスが必要
```

**適用後**（`haveI : Fintype α := inst`）
```lean
inst✝ : Fintype α
⊢ P
```

---

## 構文

```lean
haveI : TypeClass := proof
haveI h : TypeClass := proof
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

| 構文 | 意味 |
|---|---|
| `haveI : C := e` | `C` をインスタンスとして追加 |
| `haveI h : C := e` | 名前 `h` を付けて追加 |

---

## Pros（使うべき場面）

- 型クラスインスタンスを一時的に追加したい場合
- `Fintype`、`DecidableEq` 等のインスタンスを対象に
- `have` ではインスタンス推論に使われない場合の代替

---

## Cons（注意・失敗ケース）

- 永続的なインスタンス追加には `instance` 宣言を使うべき
- 不透明な仮定として追加される（`letI` は展開可能）
- ローカルスコープでのみ有効

---

## コードサンプル

### サンプル 1: Decidable インスタンスの追加

```lean
example (p : Prop) (h : Decidable p) : p ∨ ¬p := by
  haveI := h
  exact em p
```

### サンプル 2: have との違い

```lean
-- have ではインスタンス推論に使われない
-- haveI ならインスタンス推論で利用可能
example : True := by
  haveI : Inhabited Nat := ⟨0⟩
  trivial
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `have` | 非インスタンス版 | インスタンスとして不要なら `have` |
| `letI` | 展開可能版 | 定義が展開可能なインスタンスなら `letI` |
| `inhabit` | Inhabited 生成 | `Nonempty` → `Inhabited` 変換 |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
