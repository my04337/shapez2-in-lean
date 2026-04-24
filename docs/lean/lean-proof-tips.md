# Lean 4 証明 Tips

本プロジェクトの開発で得られた Lean 4 の証明に関する一般的なノウハウ。

---

## String 型の証明における注意点

Lean 4 の `String` 型は内部が UTF-8 バイト列であり、多くの関数がカーネルレベルで最適化されている。定理証明では以下の制約がある。

### 展開不可能な関数一覧

| 関数 | 理由 | 代替手段 |
|---|---|---|
| `String.splitOn` | 内部で `@[irreducible] String.splitOnAux` を使用 | 自前の `List Char` ベース split 関数 |
| `String.intercalate` | 内部ヘルパー `go✝`（ハイジェニック名）が展開不可 | `List Char` で結合 → `String.ofList` |

### `String` ↔ `List Char` ブリッジの活用

証明が必要な場合は `List Char` レベルに落として操作し、以下の stdlib 補題でブリッジする:

```lean
-- String → List Char → String のラウンドトリップ
String.ofList_toList : String.ofList s.toList = s
-- List Char → String → List Char のラウンドトリップ
String.toList_ofList : (String.ofList l).toList = l
```

詳細は [`string-roundtrip-proof.md`](string-roundtrip-proof.md) を参照。

---

## タクティクの使い分け

### `simp only` 原則 — 裸 `simp` を使わない

最終証明では**裸 `simp` を禁止**し、`simp only [...]` を使う。Mathlib の `@[simp]` DB は更新のたびに変わるため、裸 `simp` に依存する証明は将来壊れうる。

**安定化ワークフロー**:
1. 探索時に `simp` / `simp_all` で閉じることを確認
2. `simp?` / `simp_all?` に置き換えて `Try this:` から補題リストを取得
3. `simp only [lemma1, lemma2, ...]` に置換

**REPL での確認**:
```jsonl
{"cmd": "theorem foo : ... := by simp?", "env": 0}
```
→ 出力の `Try this: simp only [...]` をそのまま使用

**`simp_all` の扱い**: `simp_all only [...]` に置換するか、仮定を明示した手動証明に書き換える。Mathlib 補題が不足して `simp_all only` に変換できない場合は据え置き可（実例: QuarterPos.lean の 1 箇所）。

**`lean-simp-stabilizer` サブエージェント**: ファイル単位の自動安定化が可能。ファイルパスと行番号を渡すと REPL で `simp?` を実行し、`simp only [...]` への書き換えを生成する。

### `decide` — 有限型の全パターン網羅

有限の列挙型に関する命題は `decide` で自動証明できる。`cases` で分解した後の個別ケースにも有効。

```lean
-- 各色の具体的な文字が ':' でないことの証明
private theorem Quarter.toString_noColon (q : Quarter) :
        ':' ∉ q.toString.toList := by
    cases q with
    | empty => decide
    | pin => decide
    | crystal c => cases c <;> decide          -- 全色を展開して decide
    | colored p c => cases p <;> cases c <;> decide  -- 全パーツ×全色を展開
```

### `aesop` — 構造的ゴールの自動証明

`simp only` で閉じない構造的ゴール（コンストラクタの一致・論理結合子・補題の連鎖適用）に試みる。
S2IL では rotate180/rotateCW 等変性の基本等式が `@[aesop norm simp]` で登録済みのため、等変性ゴールは `aesop` で閉じる場合が多い。
成功時は `aesop?` で安定版スクリプトを取得して置換する。詳細: [`aesop-guide.md`](aesop-guide.md)

```lean
-- 帰納型の全ケースを aesop に委ねる
induction s <;> aesop

-- 等変性ゴールを aesop で閉じる（@[aesop norm simp] 補題を活用）
example (l : Layer) : l.eastHalf.rotate180 = l.rotate180.westHalf := by aesop
```

### `rw` vs `simp only` — 適材適所

| タクティク | 適するケース | 不向きなケース |
|---|---|---|
| `rw` | 適用順序を厳密に制御したい場合。左辺が一意にマッチする場合 | match 式内部の複数箇所に散在するパターン |
| `simp only` | 複数の同種パターンを一括で解決したい場合 | 適用順序が重要な場合（意図しないリライトが起きうる） |

**組み合わせパターン**: `rw` で構造を段階整理 → `simp only` で残りを一括解決

```lean
-- rw でリスト構造を整理し、simp only で Layer.ofString? を一括解決
rw [toCharList, splitOnColon_append_colon _ _ h1, splitOnColon_noColon _ h2]
simp only [Layer.ofString_ofList_toString]
```

### `<;>` — 複数ゴールへの一括適用

`cases` で分岐した後、全ケースに同じタクティクを適用する場合に便利。

```lean
-- 全コンストラクタが rfl で閉じる場合
cases s <;> rfl

-- 全コンストラクタを simp で閉じる場合
cases s <;> simp [layers]
```

### 非推奨・改名されたタクティク

Lean 4 / Mathlib の更新でリネームされたタクティクを使うとビルド警告が出る。常に新名称を使うこと。

| 非推奨（旧名） | 代替（新名） | 備考 |
|---|---|---|
| `push_neg` | `push Not` | Mathlib でリネーム済み。使用すると警告が出る |

---

## `List.mapM` を証明で避けるべき理由

`List.mapM` は内部で `List.mapM.loop`（アキュムレータ + `List.reverse` パターン）を使用する。
`simp` で展開すると `do` / `pure` / `.reverse` の形になり、元のパターンマッチと整合しない。

**回避策**: `mapM` を使わず、元データ構造のパターンマッチで直接処理する。

```lean
-- ❌ mapM を使う（証明困難）
match parts.mapM (fun cs => Layer.ofString? (String.ofList cs)) with
| some [l1, l2] => ...

-- ✅ 直接パターンマッチ（証明容易）
match parts with
| [c1, c2] =>
    match Layer.ofString? (String.ofList c1),
          Layer.ofString? (String.ofList c2) with
    | some l1, some l2 => ...
```

---

## 帰納法による `List` の証明パターン

`List` に関する定理は `induction` + `cons` ケースでの `have` による前提整理が基本。

```lean
private theorem splitOnColon_noColon (cs : List Char) (h : ':' ∉ cs) :
        splitOnColon cs = [cs] := by
    induction cs with
    | nil => rfl
    | cons c rest ih =>
        -- ① 先頭要素が ':' でないことを抽出
        have hc : c ≠ ':' := by intro heq; exact h (heq ▸ .head _)
        -- ② 残りのリストに ':' が含まれないことを抽出
        have hrest : ':' ∉ rest := by intro hmem; exact h (.tail _ hmem)
        -- ③ 定義を展開し、帰納法の仮定を適用
        simp only [splitOnColon, beq_iff_eq, hc, ite_false, ih hrest]
```

ポイント:
- `List.Mem.head` と `List.Mem.tail` で `∉` を分解
- `beq_iff_eq` で `BEq` を `Eq` に変換（`if c == ':'` → `if c = ':'`）
- `ite_false` で `if False then ... else ...` を簡約

---

## `rcases` による析取（`∨`）の分解

`List.mem_append`（`x ∈ l₁ ++ l₂ ↔ x ∈ l₁ ∨ x ∈ l₂`）の結果を分解する際に `rcases` が便利。

```lean
-- 4つの Quarter の toString を結合した Layer.toString に ':' が含まれないことの証明
private theorem Layer.toString_noColon (l : Layer) :
        ':' ∉ l.toString.toList := by
    simp only [Layer.toString, String.toList_append, List.mem_append]
    intro h
    -- h : ... ∨ ... ∨ ... ∨ ... を4分岐に分解
    rcases h with ((h | h) | h) | h
    · exact Quarter.toString_noColon l.ne h
    · exact Quarter.toString_noColon l.se h
    · exact Quarter.toString_noColon l.sw h
    · exact Quarter.toString_noColon l.nw h
```

---

## `private def` への `unfold` 制限

`private def` として定義された関数は、同一モジュール内でも `unfold` が失敗することがある。
`simp only [関数名]` に切り替えることで回避できる。

```lean
-- ❌ unfold が失敗する場合がある
unfold foldMinOption

-- ✅ simp only で展開可能
simp only [foldMinOption]
```

---

## Bool の `by_cases` の代替

Bool 値の場合分けに `by_cases h : f x = true` を使おうとすると、
`Decidable` インスタンスが解決できずに型エラーになることがある。
代わりに `cases` でパターンマッチする。

```lean
-- ✅ Mathlib 導入済みのため by_cases も利用可能
by_cases h : f x = true

-- ✅ cases でパターンマッチ（より明示的で Mathlib 非依存）
cases hd : f x with
| true  => ...
| false => ...
```

---

## Bool 矛盾ゴールのクローザー

`h : false = true ⊢ False` や `h : b = true` が `false = true` になった場合の閉じ方。

```lean
-- ✅ 方法 1: simp で自動消去（最も簡潔）
simp at h

-- ✅ 方法 2: decide を使った absurd
exact absurd h (by decide)

-- ✅ 方法 3: Bool 専用コンストラクタ
exact Bool.noConfusion h

-- ✅ 方法 4: Bool.false_ne_true に渡す
exact (Bool.false_ne_true h)
```

**発生場面**: `any (· == q) = false` を得た後、同じ式が `true` になることを示した場合
（例: `simp only [h_disj] at h_mem` で `false = true` に帰着するケース）。

---

## `List.not_mem_nil` は引数を取らない

`List.not_mem_nil` は `∀ a, a ∉ ([] : List α)` という型で、
引数に要素を渡す `exact List.not_mem_nil m` の形ではコンパイルエラーになる。
`nomatch` で空リストへのメンバーシップが不可能であることを示す。

```lean
-- ❌ コンパイルエラー
exact List.not_mem_nil m

-- ✅ nomatch でパターンマッチ不可能を示す
exact nomatch hm    -- hm : x ∈ []
```

---

## `List.filterMap` の展開

`List.filterMap_cons` は標準では存在しない。
代わりに `simp only [List.filterMap]` で 1 ステップ展開し、
`split` で内部の `match` / `if` を分岐して処理する。

```lean
-- ❌ List.filterMap_cons は見つからない
rw [List.filterMap_cons]

-- ✅ simp + split で展開
simp only [List.filterMap]
split
· ...   -- some ケース
· ...   -- none ケース
```

---

## `cases` による `List.Mem` の分解と変数置換

`cases hm : x ∈ (a :: rest)` で `| head _ =>` を展開すると、
`x` が `a` に**置換される**。後続の仮定中の `x` も変わるため注意。

```lean
-- h : x.layer == n = true を持つ状態で...
cases hm with
| head _ =>
    -- ここで h の中の x が a に置き換わっている
    -- h : a.layer == n = true
```

---

## `Finset.any` の不在と `decide (∃ ...)` パターン

Lean 4 v4.29.0 / Mathlib に `Finset.any` は存在しない。
`List.any` を Finset 上の操作に置き換える場合は `decide (∃ q ∈ cc, P q)` を使う。

```lean
-- ❌ Finset.any は存在しない
cc.any (fun q => q.dir.isEast)

-- ✅ decide (∃ ...) で代替
decide (∃ q ∈ cc, q.dir.isEast = true)
```

### 注意点

| 問題 | 解決策 |
|---|---|
| Bool 述語を Prop で使う | `= true` を付ける: `q.dir.isEast = true` |
| lambda 内のドット記法が失敗 | パラメータに型注釈: `(rr : QuarterPos)` |
| `decide P = decide Q` の証明 | `congr 1` → `propext` で `Iff` から導出 |
| lambda 本体で `rw` がマッチしない | `simp only` で beta 簡約してから `rw` |
| `BEq.rfl` が `(· == q)` と不一致 | 型注釈付き `have` で `.any` の形を固定 |

### `List.any ↔ Finset.mem` 変換パターン

```lean
-- List の any-membership と Finset のメンバーシップの変換
private theorem any_beq_iff_mem (l : List QuarterPos) (p : QuarterPos) :
    l.any (· == p) = true ↔ p ∈ l

-- Bool 等式への変換: Iff から Bool.eq_iff_iff.mpr で導出
Bool.eq_iff_iff.mpr ((any_beq_iff_mem _ _).trans (h.trans (any_beq_iff_mem _ _).symm))
```

### `Finset ∈` は computably 使える

`Finset α` に対して `p ∈ s` は `DecidableEq α` があれば `Decidable` である。
`if p ∈ s then ...` や `p ∉ s` を `Bool` コンテキスト（`List.filter` 等）に渡す際も、
Lean 4 は `DecidablePred` を自動解決するため `decide` の明示は不要。

```lean
-- ✅ decide 不要（DecidableEq があれば直接使える）
let floatingClusters := clusters.filter fun cluster =>
    cluster.all fun p => p ∉ grounded   -- grounded : Finset QuarterPos

-- ❌ decide を明示しなくてよい（冗長）
cluster.all fun p => decide (p ∉ grounded) == true
```

---

## `omega` — 線形算術の自動証明

### 概要

`omega` は Lean 4 / Mathlib に組み込まれた自動証明タクティクで、
**`Nat` および `Int` の線形算術**（変数の一次式による等式・不等式）を完全に自動証明する。
`Init.Tactics` に含まれており、`import Mathlib` なしでも利用可能。

### 守備範囲（使える）

```lean
-- 等式・不等式の線形組み合わせ
example (n m : Nat) (h : n ≤ m) : n ≤ m + 1 := by omega
example (n : Nat) (h1 : n < 5) (h2 : 3 ≤ n) : n = 3 ∨ n = 4 := by omega

-- List.length の計算（length は Nat）
example (l : List α) (h : l.length > 0) : l.length - 1 + 1 = l.length := by omega

-- Nat の引き算（自然数なのでアンダーフロー込み）
example (a b : Nat) (h : b ≤ a) : a - b + b = a := by omega

-- max / min を含む不等式
example (a b : Nat) : a ≤ max a b := by omega
```

### 守備範囲外（使えない）

```lean
-- 乗算・除算を含む命題（非線形）
example (n : Nat) : n * n ≥ n := by omega  -- ❌ 失敗

-- 全称量化を含む命題（量化子なしの線形算術のみ）
example : ∀ n : Nat, n + 1 > n := by omega  -- ❌ 失敗（intro n; omega で解決）

-- Bool / Option 等 Nat/Int 以外の型
example (b : Bool) : b = true ∨ b = false := by omega  -- ❌ 失敗（decide で解決）
```

### `simp` との組み合わせパターン

`List.length_*` や `Nat.min_*` などの補題では、
まず `simp only` で長さ式を数値式に変換してから `omega` を呼ぶと効果的。

```lean
-- List.length_map / List.length_append を先に適用
example (l1 l2 : List α) :
        (l1 ++ l2).length = l1.length + l2.length := by
    simp only [List.length_append]  -- 長さ式を展開
    -- または直接 omega（List.length_append を知っている場合）
    omega

-- concat した長さ不等式
example (l : List α) (h : l ≠ []) : 1 ≤ l.length := by
    cases l with
    | nil => contradiction
    | cons _ _ => simp [List.length]; omega
```

### 本プロジェクトでの活用箇所と置換パターン

本プロジェクト（Gravity.lean 等）では既に 50+ 箇所で使用されているが、
以下のような手動証明を `omega` で置き換えられる場面がある。

| 置換前（手動） | 置換後（omega） |
|---|---|
| `exact Nat.le_refl n` | `omega` |
| `exact Nat.le_trans h1 h2` | `omega`（h1, h2 が線形不等式のとき） |
| `exact Nat.min_le_left a b` | `omega` |
| `exact Nat.min_le_right a b` | `omega` |
| `have : k ≤ n := Nat.le_of_succ_le_succ h; exact this` | `omega` |
| `Nat.pos_of_ne_zero (by omega)` | `by omega` |
| `Nat.pos_of_ne_zero h_zero` | `by omega`（h_zero : x ≠ 0 がコンテキストにあるとき） |
| `Nat.le_of_lt h` | `by omega`（h がコンテキストにあるとき） |
| `Nat.zero_le _` | `by omega` |
| `Nat.le_antisymm (by omega) h` | `by omega`（両方の不等式がコンテキストにあるとき） |
| `Nat.mul_pos h1 (by omega)` | `by omega`（h1 がコンテキストにあり乗数がリテラルのとき） |
| `omega` 前の `push_neg` + `intro` の組み合わせ一部 | そのまま `omega` |

特に `placeQuarter_length`、`landingDistance_le_minLayer`、`allValid_length'` 等の
自然数算術補題では `omega` による大幅な簡略化が見込める。

### 使用方針（推奨）

自然数・整数の等式・不等式を証明する際は **`omega` を第一選択** とする。

1. まず `omega` を試す
2. `omega` が失敗した場合のみ `Nat.*` / `Int.*` の明示的補題を使う
3. `List.foldl` 等の関数結果が絡む場合は `simp` で正規化後に `omega`

`omega` が失敗する典型パターン:
- 変数同士の乗算（`n * m`）→ `Nat.mul_pos`, `Nat.mul_le_mul` 等を使う
- 関数の定義展開が必要（`List.foldl`）→ `simp [List.foldl]` の後に `omega`
- 再帰補題の結果に依存 → 明示的に `have` で補題を呼ぶ

### `intro` との組み合わせ

全称命題の先頭に量化子がある場合は `intro` で変数を導入してから `omega` を呼ぶ。

```lean
-- ∀ を含む線形算術命題
example : ∀ n : Nat, n ≤ n + 1 := by
    intro n; omega   -- ✅

-- 帰納法のケースで自然数式を閉じる
induction n with
| zero => simp
| succ k ih => omega  -- succ k の形で線形式が閉じる場合
```

---

## v4.29.0 での注目変更点（補足）

### `lean4checker` が Lean 4 本体に統合

v4.29.0 より、これまで独立リポジトリだった `lean4checker` が Lean 4 本体に統合された。
`lean4checker` は import されたモジュールの証明が `sorry` に依存していないことを
カーネルレベルで再確認するツール。

```
# lake を使ったビルド実行例
lake exe lean4checker Mathlib
```

本プロジェクトでは大きな変更なし。今後 `lean4checker` を別途インストールする必要はない。

### Lake: Git 依存パッケージ更新後の `.hash` ファイル自動クリーン

`lake update` でパッケージの revision を変更すると、以前は古い `.hash` ファイルが残留し、
ビルドトレースが不正になることがあった（[関連 Zulip スレッド](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/ProofWidgets.20not.20up-to-date)）。

v4.29.0 では `updateGitPkg` が `git clean -xf` をチェックアウト後に実行するようになり修正された。
**`lake update` 後にビルドが正常に通らない場合は `.lake` ディレクトリを手動で削除する必要は原則なくなった。**

### `inferInstanceAs` のドキュメント改善

`inferInstanceAs` の内部実装が `InstanceNormalForm` → `WrapInstance` にリネームされた（内部変更のみ）。
ユーザー向けには、ドキュメントの表現が
「instance normal form に正規化する」→「expected type に合わせてインスタンスをラップする」
と改善された。動作は実質的に変わらない。

---

## Gravity 証明で判明した偽定理カタログ

`Gravity.lean` の `process_rotate180` 証明過程で、以下の仮定が全て偽と判明した。
これらに依拠するアプローチを取ってはならない。

| 偽の仮定 | なぜ偽か |
|---|---|
| `shouldProcessBefore_no_chain` | 4L+ で 3 pin 連鎖反例。2-3L 限定検証の不備 |
| `sortFallingUnits_spb_order_on_floatingUnits` | 4 要素反例。insertSorted のグリーディ停止が順序を壊す |
| `sortFallingUnits_shouldProcessBefore_one_way_order` | spb 非推移性。3 要素反例 |
| `sortFallingUnits_later_not_spb_earlier` | 同根原因（非推移的 spb サイクル） |
| `sortFallingUnits_inversion_is_tied` (一般 Perm) | 3L 3色 8628 violations。r180 固有 Perm でのみ真 |
| sortFallingUnits が正しい topological sort を生成する | insertSorted はグリーディで後方不整合を生む |
| spb が floatingUnits 上で全順序 | tied ペアが存在する |
| BFS 列挙結果がリスト等号で r180 等変 | 探索順序が方角で変わる |
| `floatingUnits_rotate180` (list equality) | BFS order changes (.any メンバーシップのみ等変) |
| `sortFallingUnits_preserves_spb_order` | 3-cycle 下で insertSorted の順序保存が偽 |
| `spb_antisymm_of_disjoint` | 位置素のみでは反対称律不成立 |
| `foldl_sorted_disjoint_flatMap_eq` | flatMap .any 等価 + 位置素では unit 分割不一致 |
| sortFallingUnits 出力が pointwise .any 等価 | 2L: 800 不一致, 3L: 9072 不一致 |

### 共通教訓

- **ペアワイズ非循環 ≠ DAG**: 全ペアの 2-cycle がなくても 3-cycle 以上が存在しうる
- **計算検証は十分な規模で**: 2-3L のみの計算検証は 4L+ 反例を見逃す
- **リスト等号は探索順序依存**: BFS 出力はリスト等号ではなく `.any` メンバーシップで述べる
- **偽定理に依拠する証明チェーンは直ちに不健全**: sorry 1 個でも上流全体が汚染される

---

## 証明作業の効率化ルール（エージェント向け）

このセクションはエージェントの作業効率を向上させるために実績から抽出したルールをまとめる。

### 提案 1: lean-proof-planning Phase 0 を最初に読む

`lean-proof-planning` スキルが適用される場面（新規証明開始・方針転換）では、実装着手の前に必ず読む。

```
❌ 禁止: スキル読み → 即実装
✅ 正解: スキル読み → Phase 0（真偽チェック）→ ゲート 1（反例チェック）→ 実装
```

Phase 0 を省略して実装に入ると、偽定理に長時間費やすリスクが高い（本プロジェクト実績: 複数回発生）。

### 提案 2: 関連シンボル群は 1 回の alternation regex で取得する

Lean ソースを `grep_search` するとき、関連する複数シンボルをバラバラに検索しない。

```
❌ 非効率: grep "foldl_placeFU_cluster" → grep "foldl_placeFU_pin" → grep "isOccupied_placeFallingUnit"
✅ 効率的: grep "foldl_placeFU|isOccupied_placeFallingUnit" (1 クエリで全件取得)
```

**実装**: `grep_search` の `query` フィールドに正規表現の alternation `|` を使う。  
`isRegexp: true` を忘れずに設定する。

### 提案 3: 補題の前提条件は最も一般的な形で書く

複数の具象バージョン（cluster-only / pin-only / mixed など）に発展する補題は、
最初から最も一般的な前提式で設計する。

```lean
-- ❌ pin-only 版（後で mixed を作るとき再設計が必要）
(h_layer_ge : ∀ p, FallingUnit.pin p ∈ group → d ≤ p.layer)
(h_layer_lt : ∀ p, FallingUnit.pin p ∈ group → p.layer < obs.length)

-- ✅ 最初から全 FU 統一形（cluster も pin も同じ形で扱える）
(h_layer_ge : ∀ u ∈ group, ∀ q ∈ u.positions, d ≤ q.layer)
(h_layer_lt : ∀ u ∈ group, ∀ q ∈ u.positions, q.layer < obs.length)
```

`FallingUnit.positions` は `cluster ps → ps` / `pin p → [p]` なので、後者は前者の縮退形として機能する。

### 提案 4: 自プロジェクト補題・Mathlib API の使用前に REPL `#check` で型確認する

補題を使おうとする前に、その型シグネチャを REPL で確認する。
特に `List.nodup_append` / `List.nodup_cons` 等の分解結果の型は直感と外れやすい。

```jsonl
{"cmd": "#check @List.nodup_append", "env": 0}
```

これにより、実装中のエラー修正サイクル（REPL → 修正 → REPL → 修正）を排除できる。

| よく誤解される API | 実際の型（要 `#check` 確認） |
|---|---|
| `List.nodup_append.mp` | `→ l₁.Nodup ∧ l₂.Nodup ∧ (∀ a ∈ l₁, ∀ b ∈ l₂, a ≠ b)` （`Disjoint` ではない） |
| `List.nodup_cons.mp` | `→ a ∉ l ∧ l.Nodup` |
| `List.flatMap_cons` | `→ (f a ++ l.flatMap f)` ← `simp` で展開する補題 |
