# Mathlib / Batteries 補題検索ガイド

証明中に「使える補題があるはずだが名前が分からない」場面で参照する実践ガイド。
発見済みの補題カタログ・置換パターンは [`batteries-catalog.md`](batteries-catalog.md) を参照。

---

## 検索ツール一覧

| ツール | 入力 | 強み | 制約 |
|---|---|---|---|
| `exact?` | ゴール状態（tactic mode） | ゴールを**完全に閉じる**補題を探す | 時間がかかる（数十秒）・型が複雑だとタイムアウト |
| `apply?` | ゴール状態（tactic mode） | ゴールに**適用可能**な補題を探す（引数は残る） | `exact?` より広いが精度は落ちる |
| `#leansearch` | 英語自然言語 | 概念的な検索。名前見当がつかない場合に有効 | クエリの末尾に `.` または `?` が必要 |
| `#loogle` | 型パターン | 型シグネチャの構造で検索 | 構文にクセあり・ REPL では定数名直接指定が有効 |
| `#check` | 宣言名 | 候補の型シグネチャを確認 | 名前が分かっていないと使えない |

---

## ゴール形状 → 検索戦略マップ

### List 操作

> **`#loogle` の注意**: REPL 経由では `_` プレースホルダーを含む型パターン（`List.map _ _` 等）が結果なしになることが多い。**定数名直接指定**（例: `#loogle "List.map_map"`）か `exact?` / `#leansearch` を優先する。

| ゴールパターン | 第1候補 | `#loogle` 定数名クエリ例 |
|---|---|---|
| `(l.map f).map g = l.map (g ∘ f)` | `exact?` → `List.map_map` | `#loogle "List.map_map"` |
| `(l.map f).filter p = ...` | `exact?` → `List.filter_map` | `#loogle "List.filter_map"` |
| `(l.map f).any p = l.any (p ∘ f)` | `exact?` → `List.any_map` | `#loogle "List.any_map"` |
| `(l.map f).length = l.length` | `exact?` → `List.length_map` | `#loogle "List.length_map"` |
| `(l.set i a).map f = ...` | `exact?` → `List.map_set` | `#loogle "List.map_set"` |
| `List.Perm l1 l2 → l1.length = l2.length` | `exact?` → `List.Perm.length_eq` | `#loogle "List.Perm.length_eq"` |
| `l.foldl f init = ...`（Perm 不変） | `#leansearch` | `#leansearch "foldl of permutation with commutative associative."` |
| `l.filterMap (f ∘ g) = ...` | `exact?` → `List.filterMap_map` | `#loogle "List.filterMap_map"` |

### Nat / Int 算術

| ゴールパターン | 第1候補 | 補足 |
|---|---|---|
| `a < b` / `a ≤ b` | `omega` | 補題検索の前にまず `omega` を試す |
| `a + 0 = a` | `exact?` → `Nat.add_zero` | 基本的な恒等式 |
| `Nat.succ n ≠ 0` | `exact?` → `Nat.succ_ne_zero` | |
| 非線形（`a * b ≤ ...`） | `#leansearch` | `#leansearch "product less equal natural number."` |

### Option / Bool

| ゴールパターン | 第1候補 | `#loogle` クエリ例 |
|---|---|---|
| `(some a).map f = some (f a)` | `exact?` | `#loogle "Option.map _ (some _)"` |
| `Option.bind (some a) f = f a` | `exact?` | `#loogle "Option.bind (some _) _"` |
| `(a == b) = (b == a)` | `exact?` → `BEq.comm` | `LawfulBEq` 前提が必要 |

### Finset / Multiset

| ゴールパターン | 第1候補 | `#loogle` クエリ例 |
|---|---|---|
| `s.card = ...` | `exact?` | `#loogle "Finset.card _"` |
| `a ∈ s.map f` | `apply?` | `#loogle "_ ∈ Finset.map _ _"` |

### Fin n / インデックス

| ゴールパターン | 第1候補 | `#loogle` クエリ例 |
|---|---|---|
| `(i : Fin n).val < n` | `exact?` → `Fin.isLt` | — |
| `Fin.val i = Fin.val j → i = j` | `exact?` → `Fin.val_inj` | `#loogle "Fin.val _ = Fin.val _"` |
| `i.val % n = i.val` | `exact?` → `Fin.val_fin_lt` / `omega` | `#loogle "Fin.val _, Nat.mod"` |
| `Fin.last n` の性質 | `exact?` | `#loogle "Fin.last"` |

### 関数等式 / Iff

| ゴールパターン | 第1候補 | 補足 |
|---|---|---|
| `⊢ f = g`（関数） | `funext x` でサブゴール化 → `exact?` | `Function.funext_iff` で `↔` 変換も可 |
| `⊢ A ↔ B` | `constructor` / `apply Iff.intro` で2方向に分割 | `exact?` → `Iff.comm`, `and_comm` 等が見つかることも |
| `⊢ (A ∧ B) ↔ (B ∧ A)` | `exact?` → `And.comm` | — |
| `⊢ (A ∨ B) ↔ (B ∨ A)` | `exact?` → `Or.comm` | — |
| `h : A ↔ B ⊢ A → B` | `exact h.mp` | `h.mpr` で逆方向 |

---

## `#loogle` 構文リファレンス

`#loogle` は型パターンで Mathlib 定理を検索する。

> ⚠️ **REPL での制約**: `_` プレースホルダー付きのサブ式パターン（`List.map _ _` 等）や `|-` 結論パターンは REPL 上では結果が返らないことが多い。**定数名直接指定**が最も信頼性が高い。

### REPL で有効なクエリ形式

| 形式 | 例 | 結果 |
|---|---|---|
| 定数名直接 | `#loogle "List.length_filter_le"` | ✅ 安定して動作 |
| 名前部分文字列 | `#loogle "\"length_filter\""` | ✅ ダブルクォートをエスケープ |
| 複数定数 AND | `#loogle "List.filter, List.map"` | ⚠️ 結果なしになることがある |
| `_` パターン | `#loogle "List.map _ _"` | ❌ REPL では多くの場合無効 |
| `\|-` 結論パターン | `#loogle "\|- List.length _ ≤ _"` | ❌ REPL では多くの場合無効 |

### 基本構文（Loogle ウェブ UI 向け）

| 構文 | 意味 | 例 |
|---|---|---|
| `Foo` | 名前に `Foo` を含む | `List.map` |
| `_ → _` | 関数型のパターン | `List α → List α` |
| `\|- P` | 結論が `P` の形 | `\|- List.foldl _ _ _ = _` |
| `Foo, Bar` | `Foo` と `Bar` 両方を含む | `List.Perm, List.foldl` |
| `?α` | 型変数（任意の型） | `?α → ?α → Bool` |

---

## `#leansearch` クエリ設計

`#leansearch` は英語自然言語で Mathlib 定理を検索する。末尾は `.` または `?` で終わらせる。

### ゴール → クエリ変換の例

| ゴール | クエリ |
|---|---|
| `l1.Perm l2 → l1.foldl f init = l2.foldl f init` | `"foldl of permutation with commutative associative."` |
| `(l.map f).length = l.length` | `"length of mapped list equals original length."` |
| `l.filter p ++ l.filter (¬ p ·) ~ l` | `"filter and complement partition a list."` |
| `a ∈ l.insertNth n a` | `"element belongs to list after insertion."` |
| `List.Nodup (l1 ++ l2)` | `"nodup append iff nodup and disjoint."` |

### 効果的なクエリのコツ

1. **Lean/Mathlib の用語を使う**: `List.Perm`、`foldl`、`Nodup` など
2. **性質を明示する**: `"commutative"`, `"associative"`, `"injective"` など
3. **短く具体的に**: 長文より 5-10 語のフレーズが精度が高い
4. **末尾の句読点を忘れない**: `.` または `?` で終わらせないとエラー

---

## `exact?` / `apply?` を効かせるコツ

### 型を整理してから実行

```lean
-- ❌ キャストが混在していると候補が見つからない
exact?  -- ゴール: ↑n < ↑m

-- ✅ norm_cast で正規化してから再試行
norm_cast
exact?  -- ゴール: n < m → Nat.lt_of_succ_le 等が見つかる
```

### 引数を部分適用してから実行

```lean
-- ❌ 変数が多すぎると遅い
apply?  -- ゴール: ∀ (a b c : Nat), a + b + c = a + (b + c)

-- ✅ intro で束縛してからゴールを単純化
intro a b c
exact?  -- Nat.add_assoc が見つかる
```

### simp 補題を探す

```lean
-- ✅ simp? で使われた補題リストを取得し、exact? の代替とする
simp?  -- → "simp only [List.map_map, Function.comp]"
```

---

## REPL 実行パターン

詳細は [`repl-guide.md`](repl-guide.md) の UC-8 を参照。

REPL スクリプトが `import S2IL + Mathlib.Tactic + Plausible + Duper` を先頭に自動挿入するため、JSONL 内では `"env": 0` を直接使える。

### exact? / apply?

```jsonl
{"cmd": "theorem search (l : List Nat) (h : l.length > 0) : l ≠ [] := by sorry", "env": 0}

{"tactic": "exact?", "proofState": 0}

{"tactic": "apply?", "proofState": 0}
```

```powershell
.github/skills/lean-repl/scripts/repl.ps1 -Send -SessionId <id> -CmdFile Scratch/commands-<sessionId>.jsonl
```

### #leansearch / #loogle

```jsonl
{"cmd": "#leansearch \"list reverse reverse equals identity.\"", "env": 0}

{"cmd": "#loogle \"List.reverse (List.reverse _)\"", "env": 0}
```

```powershell
.github/skills/lean-repl/scripts/repl.ps1 -Send -SessionId <id> -CmdFile Scratch/commands-<sessionId>.jsonl
```

### 候補を #check で確認

```jsonl
{"cmd": "#check List.reverse_reverse", "env": 0}

{"cmd": "#check @List.map_map", "env": 0}
```

---

## S2IL 固有型の検索パターン

S2IL のドメイン型（`Shape`、`Layer`、`Quarter` 等）は Mathlib に存在しないため、
`exact?` / `apply?` のみが有効な検索手段となる。

| 型 | 検索アプローチ |
|---|---|
| `Shape` / `Layer` | `exact?` / `apply?`。S2IL 内で `@[simp]` 付きの補題を探す |
| `QuarterPos` / `Direction` | `decide`（有限型）。`exact?` は遅い |
| `List Layer` / `List Quarter` | `List` 汎用補題を `exact?` で探す。S2IL 固有補題は `simp?` で発見 |

---

## 命名規則から補題名を推測する

`exact?` でタイムアウトしそうな複雑なゴールでも、Lean / Mathlib の命名規則を知っていれば補題名を直接当てられることがある。

### 基本パターン

| パターン | 意味 | 例 |
|---|---|---|
| `Ns.X_Y` | 型 `Ns` の操作 `X` と `Y` の組み合わせ | `List.map_map`, `List.length_map`, `List.filter_map` |
| `X_of_Y` | `Y` という前提から `X` を導く | `Nat.lt_of_succ_le`, `List.ne_nil_of_length_pos` |
| `X_comm` | 演算 `X` の可換性 | `add_comm`, `mul_comm`, `And.comm` |
| `X_assoc` | 演算 `X` の結合性 | `add_assoc`, `List.append_assoc` |
| `X_left` / `X_right` | 左右の対称操作 | `add_zero` ↔ `zero_add`, `mul_one` ↔ `one_mul` |
| `X_zero` / `zero_X` | ゼロとの組み合わせ | `Nat.add_zero`, `Nat.zero_add` |
| `X_nil` / `nil_X` | 空リストとの組み合わせ | `List.append_nil`, `List.nil_append` |
| `X_congr` | 引数を変えた等式 | `List.map_congr`, `congrArg` |
| `X_inj` / `X_injective` | 単射性 | `Fin.val_inj`, `List.map_injective` |
| `X_iff` | 同値への変換 | `List.mem_map`, `List.mem_filter` |

### 推測フロー

```
ゴール: (l.map f).map g = l.map (g ∘ f)
       ↓
操作の組み合わせ: List.map ∘ List.map
       ↓
パターン: List.map_X → List.map_map を試す
       ↓
#check List.map_map  →  型確認 → 合えば exact!/rw で適用
```

---

## よくある発見パターン

### 手動定義を Batteries 補題で置換

1. `exact?` で sorry を閉じてみる
2. 見つかった補題が `Batteries.Data.List.*` 等なら、手動定義を削除して直接利用
3. [`batteries-catalog.md`](batteries-catalog.md) に追記して再利用可能に

### simp 補題の未知のリスト要素を発見

1. `simp?` でゴールを閉じる
2. 出力される `simp only [...]` のリストから知らない補題を確認
3. `#check` で型シグネチャを確認
4. 必要に応じて `@[simp]` 属性を自作定理にも付与

---

## 関連リソース

- **スキル**: `lean-mathlib-search`（検索パイプラインの自動化）
- **エージェント**: `lean-lemma-finder`（ゴールから補題を自動検索）
- **補題カタログ**: [`batteries-catalog.md`](batteries-catalog.md)（発見済み補題・置換パターン）
- **関連ドキュメント**: [`../../../../docs/lean/README.md`](../../../../docs/lean/README.md)（Lean 関連ガイドの入口）
- **REPL ガイド**: [`repl-guide.md`](repl-guide.md) UC-8
