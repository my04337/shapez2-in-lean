# Batteries / Mathlib 補題カタログ

S2IL で発見・活用済みの補題・型クラス・置換パターンの一覧。
補題の**検索方法**（`exact?` / `#leansearch` / `#loogle` の使い方）は [`mathlib-search-guide.md`](mathlib-search-guide.md) を参照。

---

## 発見済み補題

### BEq 関連

| 補題 | シグネチャ | 前提 | 使用例 |
|------|----------|------|--------|
| `BEq.comm` | `(a == b) = (b == a)` | `LawfulBEq` | `beq_symm` の汎用版。`BEq.comm (a := x)` で型推論を補助 |

**注意**: `BEq.comm` は `LawfulBEq` インスタンスが必要。`deriving DecidableEq, BEq` で生成される型は自動的に `LawfulBEq` を持つ。

### List 操作

| 補題 | シグネチャ | 用途 |
|------|----------|------|
| `List.map_set` | `(l.set i a).map f = (l.map f).set i (f a)` | `List.map` と `List.set` の可換性 |
| `List.filterMap_map` | `(l.map g).filterMap f = l.filterMap (f ∘ g)` | `filterMap` と `map` の合成 |
| `List.filter_map` | `(l.map f).filter p = (l.filter (p ∘ f)).map f` | `filter` と `map` の可換性 |
| `List.any_map` | `(l.map f).any p = l.any (p ∘ f)` | `any` と `map` の合成 |
| `List.flatMap_map` | `(l.map f).flatMap g = l.flatMap (g ∘ f)` | `flatMap` と `map` の合成 |
| `List.take_eq_nil_iff` | `l.take k = [] ↔ k = 0 ∨ l = []` | `take` が空になる条件 |

### Std 型クラス

| 型クラス | フィールド | 用途 |
|---------|----------|------|
| `Std.Commutative op` | `comm : ∀ a b, op a b = op b a` | 二項演算の可換性 |
| `Std.IdempotentOp op` | `idempotent : ∀ x, op x x = x` | 二項演算の冪等性 |
| `Std.LawfulLeftIdentity op e` | `left_id : ∀ a, op e a = a` | 左単位元 |
| `Std.LawfulRightIdentity op e` | `right_id : ∀ a, op a e = a` | 右単位元 |
| `Std.LeftIdentity op e` | （マーカーのみ） | `LawfulLeftIdentity` の前提 |
| `Std.RightIdentity op e` | （マーカーのみ） | `LawfulRightIdentity` の前提 |

**注意**: `LawfulLeftIdentity` / `LawfulRightIdentity` を定義するには、先に対応する `LeftIdentity` / `RightIdentity` マーカーインスタンスが必要。

```lean
-- ✅ 正しい順序
instance : Std.LeftIdentity Color.mix Color.white := ⟨⟩
instance : Std.LawfulLeftIdentity Color.mix Color.white where
    left_id := mix_white_left
```

---

## 手動定義 → Batteries 置換パターン

### 置換できたもの

| 手動定義 | Batteries 補題 | 注意点 |
|---------|--------------|--------|
| `private theorem list_map_set` | `List.map_set` | 直接置換可能 |
| `private theorem beq_symm` | `BEq.comm` | `LawfulBEq` が必要。`(a := x)` で名前付き引数指定 |
| `private theorem list_filterMap_map` | `List.filterMap_map` | 引数順が異なる場合あり。型を確認のこと |
| `private theorem take_ne_nil_of_ne_nil_pos` | `List.take_eq_nil_iff` + `omega` | iff を `intro h; rw [...] at h; rcases h with rfl \| rfl` で分解 |

### 置換できなかったもの

| 補題 | 理由 |
|------|------|
| `set_ne_nil_of_ne_nil` | `List.set_eq_nil` が現バージョン (Lean 4.29.0) で "Unknown constant" |
| 各ファイルの `list_any_map_rotate180` | `List.any_map` で一部簡素化可能だが、ドメイン固有の `beq_rotate180` との組み合わせが必要 |
| BFS 関連補題群 (`bfs_vis_subset` 等) | ドメイン固有の不変条件。汎用ライブラリに対応なし |

---

## バージョン固有の注意事項

### Lean 4.29.0 / Batteries 時点

| 事象 | 詳細 |
|------|------|
| `List.set_eq_nil` 不在 | `.mp` が "Unknown constant" → `set_ne_nil_of_ne_nil` を自前で維持 |
| `List.filterMap_map` 引数順 | `(l.map f).filterMap g = l.filterMap (g ∘ f)` — `f` と `g` の順序に注意 |
| `LawfulBEq` 自動生成 | `deriving DecidableEq, BEq` で自動的に `LawfulBEq` が生成される |

---

## 関連

- **検索ガイド**: [`mathlib-search-guide.md`](mathlib-search-guide.md)（`exact?` / `#leansearch` / `#loogle` の使い方）
- **設計知識**: [`docs/knowledge/mathlib-batteries-tips.md`](../../../../docs/knowledge/mathlib-batteries-tips.md)（`simp` 最適化・`Finset` 設計制約等）
