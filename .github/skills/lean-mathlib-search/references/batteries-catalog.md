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
| `List.map_eq_nil_iff` | `List.map f l = [] ↔ l = []` | map が空になる条件。`map_ne_nil` の代替 |
| `List.set_eq_nil_iff` | `l.set i a = [] ↔ l = []` | set が空になる条件。`set_ne_nil` の代替 |
| `List.filterMap_map` | `(l.map g).filterMap f = l.filterMap (f ∘ g)` | `filterMap` と `map` の合成 |
| `List.filter_map` | `(l.map f).filter p = (l.filter (p ∘ f)).map f` | `filter` と `map` の可換性 |
| `List.any_map` | `(l.map f).any p = l.any (p ∘ f)` | `any` と `map` の合成 |
| `List.any_cons` | `(a :: l).any f = (f a \|\| l.any f)` | `any` の cons 展開 |
| `List.any_append` | `(xs ++ ys).any f = (xs.any f \|\| ys.any f)` | `any` の append 分配 |
| `List.any_filter` | `(l.filter p).any q = l.any (fun a => p a && q a)` | filter 後の any を and で合成 |
| `List.any_flatMap` | `(l.flatMap f).any p = l.any (fun a => (f a).any p)` | flatMap 後の any 分配 |
| `List.any_eq_true` | `l.any p = true ↔ ∃ x ∈ l, p x = true` | any の Prop 判定変換 |
| `List.any_beq` | `(l.any fun x => a == x) = l.contains a` | beq 形式の any → contains |
| `List.flatMap_map` | `(l.map f).flatMap g = l.flatMap (g ∘ f)` | `flatMap` と `map` の合成 |
| `List.take_eq_nil_iff` | `l.take k = [] ↔ k = 0 ∨ l = []` | `take` が空になる条件 |
| `List.length_set` | `(as.set i a).length = as.length` | set は長さを保存 |
| `List.length_take` | `(l.take i).length = min i l.length` | take 後の長さ |
| `List.ne_nil_of_length_pos` | `0 < l.length → l ≠ []` | 正の長さ → 非空 |

### List.Perm 操作

| 補題 | シグネチャ | 用途 |
|------|----------|------|
| `List.Perm.any_eq` | `l₁.Perm l₂ → l₁.any f = l₂.any f` | 置換に対する any の不変性 |
| `List.Perm.length_eq` | `l₁.Perm l₂ → l₁.length = l₂.length` | 置換に対する長さの不変性 |
| `List.Perm.map` | `l₁.Perm l₂ → (l₁.map f).Perm (l₂.map f)` | map は置換を保存 |
| `List.Perm.mem_iff` | `l₁.Perm l₂ → (a ∈ l₁ ↔ a ∈ l₂)` | 置換に対するメンバーシップ不変 |
| `List.Perm.subset` | `l₁.Perm l₂ → l₁ ⊆ l₂` | 置換は部分集合を含意 |
| `List.mergeSort_perm` | `(l.mergeSort le).Perm l` | mergeSort の結果は入力の置換 |

### Bool 操作

| 補題 | シグネチャ | 用途 |
|------|----------|------|
| `Bool.or_left_comm` | `(x \|\| (y \|\| z)) = (y \|\| (x \|\| z))` | or の左可換性（Perm.swap 証明で使用） |
| `Bool.and_comm` | `(x && y) = (y && x)` | and の可換性 |

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
| `private theorem set_ne_nil_of_ne_nil` | `List.set_eq_nil_iff` | `simp only [ne_eq, List.set_eq_nil_iff]; omega` または `exact h` で置換可 |
| `private theorem map_ne_nil_of_ne_nil` | `List.map_eq_nil_iff` | `simp only [ne_eq, List.map_eq_nil_iff]; exact h` で置換可 |
| `theorem perm_any_eq` | `List.Perm.any_eq` | `h.any_eq` に直接置換可。呼び出し側も `h.any_eq` に書き換え |

### 置換できないもの

| 補題 | 理由 |
|------|------|
| `filter_any_eq` (Stacker, Shatter) | `List.any_filter` で証明が簡素化できるが、結論が異なる（`BEq`/`LawfulBEq` に依存する `any_beq_and` ロジックが必要） |
| `any_beq_and` / `any_and_beq` (Shatter) | `BEq`/`LawfulBEq` 固有の簡約ロジック。汎用ライブラリに直接の対応なし |
| `any_beq_iff_mem` (CrystalBond) | `List.any_eq_true` + `beq_iff_eq` で簡素化可だが、結合の手順がドメイン固有 |
| 各ファイルの `list_any_map_rotate180` | `List.any_map` で一部簡素化可能だが、ドメイン固有の `beq_rotate180` との組み合わせが必要 |
| `foldMinOption_*` (SettleFoldlEq) | カスタム foldl 変種。汎用ライブラリに対応なし |

---

## バージョン固有の注意事項

### Lean 4.29.0 / Batteries 時点

| 事象 | 詳細 |
|------|------|
| `List.set_eq_nil_iff` 利用可 | v4.29.0 で `List.set_eq_nil_iff` が利用可能になった。`set_ne_nil_of_ne_nil` の自前定義を置換可 |
| `List.map_eq_nil_iff` 利用可 | v4.29.0 で `List.map_eq_nil_iff` が利用可能。`map_ne_nil` 系の自前定義を置換可 |
| `List.filterMap_map` 引数順 | `(l.map f).filterMap g = l.filterMap (g ∘ f)` — `f` と `g` の順序に注意 |
| `LawfulBEq` 自動生成 | `deriving DecidableEq, BEq` で自動的に `LawfulBEq` が生成される |

---

## 部分 import パターン

S2IL 本体のコードでは `import Mathlib.Tactic` 経由で Batteries が自動的に利用可能。
軽量な Scratch ファイルやテスト用途では、必要なモジュールのみをインポートすることでビルド時間を短縮できる。

| 目的 | import パターン | 内容 |
|------|----------------|------|
| List 基本補題 | `import Batteries.Data.List.Lemmas` | `map_set`, `any_map`, `any_cons`, `any_append`, `any_filter` 等 |
| List.Perm 補題 | `import Batteries.Data.List.Perm` | `Perm.any_eq`, `Perm.length_eq`, `Perm.map`, `Perm.mem_iff` |
| Array 補題 | `import Batteries.Data.Array.Lemmas` | `Array.size_set`, `Array.getElem_push` 等 |
| HashMap | `import Batteries.Data.HashMap` | `HashMap.insert`, `HashMap.find?`, `HashMap.mem_keys` |
| BEq / LawfulBEq | `import Batteries.Classes.BEq` | `BEq.comm`, その他の BEq 補題 |
| 全部入り | `import Batteries` | Batteries 全体（Mathlib よりは軽量） |

> **注意**: S2IL REPL では `import S2IL + Mathlib.Tactic + Plausible + Duper` が自動挿入されるため、部分 import は不要。上記は Scratch ファイルや外部ツールでの利用時の参考。

---

## 既存証明の Batteries 置換候補一覧

以下は S2IL コードを Batteries/Mathlib 補題で置換・簡素化できる候補。
証明セッションの合間に段階的に実施することを推奨。

### ✅ 直接置換可能（優先度: 高）

| ファイル | 手書き補題 | Batteries 代替 | 置換方法 |
|--------|---------|--------------|----------|
| `Gravity/Equivariance.lean` | `perm_any_eq` | `List.Perm.any_eq` | 定義削除 → 呼び出し側を `h.any_eq` に書き換え |
| `Shape/Shape.lean` | `map_ne_nil_of_ne_nil` | `List.map_eq_nil_iff` | `simp only [ne_eq, List.map_eq_nil_iff]` で置換可 |
| `Rotate180Lemmas.lean` | `set_ne_nil_of_ne_nil` | `List.set_eq_nil_iff` | `simp only [ne_eq, List.set_eq_nil_iff]` で置換可 |

### ⚠️ 証明簡素化可能（優先度: 中）

| ファイル | 手書き補題 | 活用できる Batteries 補題 | 備考 |
|--------|---------|---------------------|------|
| `Stacker.lean` | `filter_any_eq` | `List.any_filter` + BEq ロジック | 証明本体を `rw [List.any_filter]` で短縮できる可能性 |
| `Shatter.lean` | `filter_any_eq` | 同上 | Stacker.lean と同一の補題 |
| `CrystalBond.lean` | `any_beq_iff_mem` | `List.any_eq_true` + `beq_iff_eq` | 証明が 2 行に短縮できる可能性 |

### ❌ 置換不可（ドメイン固有）

| ファイル | 補題 | 理由 |
|--------|--------|------|
| `Shatter.lean` | `any_beq_and` / `any_and_beq` | `BEq`/`LawfulBEq` 固有の簡約。Batteries に直接の対応なし |
| `Gravity/Defs.lean` | `listNatLe_*` | カスタム全順序。汎用補題では表現不可 |
| `Gravity/SettleFoldlEq/` | `foldMinOption_*` | カスタム foldl 変種。対応なし |

---

## 関連

- **検索ガイド**: [`mathlib-search-guide.md`](mathlib-search-guide.md)（`exact?` / `#leansearch` / `#loogle` の使い方）
- **関連ドキュメント**: [`../../../../docs/lean/README.md`](../../../../docs/lean/README.md)（Lean 関連ガイドの入口）
- **Aesop 活用**: [`docs/lean/aesop-guide.md`](../../../../docs/lean/aesop-guide.md)（等変性補題の自動証明）
- **Plausible 活用**: [`docs/lean/plausible-guide.md`](../../../../docs/lean/plausible-guide.md)（ランダムテストによる仮説検証）
