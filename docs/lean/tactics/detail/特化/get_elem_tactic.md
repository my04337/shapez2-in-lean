# `get_elem_tactic` — 配列添字の範囲証明

**カテゴリ**: 特化 | **定義元**: `Lean.Elab.Tactic.getElemTactic` | **ソース**: Lean4 core

---

## 概要

`get_elem_tactic` は `arr[i]` のような添字アクセス時に自動生成される範囲証明義務（`i < arr.size` 等）を解決する特化タクティクである。通常は Lean が自動的に呼び出すが、手動で使うこともできる。

---

## ゴールパターン

**適用前**
```lean
⊢ i < arr.size
```

**適用後**: 自動解決

---

## 構文

```lean
get_elem_tactic
```

---

## 必須 import

Lean4 core 組み込みのため不要。

---

## オプション一覧

特になし。`omega`, `simp`, `assumption` 等を内部的に試行する。

---

## Pros（使うべき場面）

- 添字アクセスの範囲証明
- `arr[i]` の `i < size` を自動証明
- `omega` で閉じられる算術的条件の処理

---

## Cons（注意・失敗ケース）

- 複雑な範囲条件は手動証明が必要
- 通常は Lean のエラボレータが自動呼び出しするため手動使用は稀
- `omega` で閉じられない条件には無力

---

## コードサンプル

### サンプル 1: 配列アクセス

```lean
example (arr : Array Nat) (h : arr.size = 3) : arr.size > 0 := by
  get_elem_tactic <;> omega
```

### サンプル 2: 通常は自動で呼ばれる

```lean
-- Lean のエラボレータが自動的に get_elem_tactic を呼び出す
-- 多くの場合、明示的な呼び出しは不要
def first (arr : Array Nat) (h : 0 < arr.size) : Nat :=
  arr[0]
```

---

## 関連タクティク

| タクティク | 関係 | 使い分け |
|---|---|---|
| `omega` | 算術証明 | 範囲条件を直接証明 |
| `simp` | 簡約 | 範囲条件を簡約で解決 |
| `decide` | 決定 | 具体的な値なら `decide` |

---

## 参照

- [Lean4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
