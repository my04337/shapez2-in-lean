# process_rotate180 証明チェーン再設計

> 作成日: 2026-04-05
> 対象ファイル: `S2IL/Behavior/Gravity.lean`（~6,500 行）
> 前提: `docs/plans/proof-cleanup-plan.md` の SS-1〜SS-6 完了後に着手

---

## 0. エグゼクティブサマリー

### 目標定理

```lean
theorem process_rotate180 (s : Shape) :
    (process s).map Shape.rotate180 = process s.rotate180
```

落下処理 `Gravity.process` と 180° 回転 `Shape.rotate180` の可換性。

### 現状

- **命題自体は TRUE**: 20+ テストケースで計算検証済み。全反例形状を含む
- **現行証明チェーンは不健全**: 偽補題 `shouldProcessBefore_no_chain` (S-5) に依存
- **不健全な補題群**: S-5 に依存する 5 補題の証明が成立しない
- **健全な部分**: ~6,000 行の大部分（Phase 1、BFS、等変性基盤）は健全
- **sorry 数**: 1 件（`shouldProcessBefore_no_chain`、偽定理）

### 結論

- **推奨**: 提案 B「直接 direction-disjoint 証明」を SettledState 完了後に実施
- **代替**: 提案 D「定義変更 + 決定性ソート」は将来の保守性に優れるが工数大
- **現行チェーンの修正**（提案 A）は技術的に複雑で推奨しない
- **完全書き換え**（提案 C, E）はリスクが高く、既存資産を活かせない

---

## 1. 前提条件: SettledState 証明の完了

process_rotate180 の証明チェーン再設計に着手する前に、以下の SettledState 課題を完了する必要がある。

### 1.1 SettledState 残課題

| # | 内容 | 状態 | process_rotate180 への影響 |
|---|---|---|---|
| SS-1 | `IsSettled_paint` | ✅ 完了 | なし（直接無関係） |
| SS-2 | `IsSettled_crystallize` | 🔲 sorry | **低**: 直接使用しないが、IsSettled 体系の健全性に必要 |
| SS-3 | `IsSettled_rotateCW` | 🔲 sorry | **中**: rotateCW 分解アプローチ（提案 E）の前提 |
| SS-4 | `gravity_IsSettled` | 🔲 sorry | **高**: 提案 C/D で活用可能。process 出力の構造制約 |
| SS-5 | ファイル分離 | ✅ 完了 | — |
| SS-6 | `SettledShape` サブタイプ | 🔲 将来 | SS-4 完了後に検討 |

### 1.2 先に SettledState を完了すべき理由

1. **`IsSettled` は process_rotate180 の前提条件ではないが、証明戦略の選択に影響する**
   - SS-4 (`gravity_IsSettled`) が完了すれば「process 出力は安定状態」という強い制約が使える
   - 提案 C/D ではこの制約を直接活用する
2. **@[simp] 設計基準の反映が証明構造に影響する**
   - 新規 `@[simp]` 属性（`mix_self`, `truncate_idempotent` 等）が settle 系証明に波及する可能性
3. **SettledState 完了により、process のセマンティクスが明確化される**
   - 「落下処理 = 全ユニットの着地 + 正規化」という理解が形式化される
   - process_rotate180 の証明で「全ユニットが着地済みの状態で比較する」アプローチが可能になる

### 1.3 SettledState 完了の推奨順序

```
SS-4 (gravity_IsSettled)        ★★★ — process の基盤定理
  ↓
SS-2 (IsSettled_crystallize)    ★★ — floatingUnits_crystallize_eq の証明
  ↓
SS-3 (IsSettled_rotateCW)       ★★ — floatingUnits_isEmpty_rotateCW の証明
  ↓
SS-6 (SettledShape サブタイプ)  ★ — SS-1〜4 完了後
```

SS-4 を最優先とする理由: process のメインループ（foldl）が全ユニットを着地させることの証明が
他の SS 項目や process_rotate180 の新証明チェーンで活用される。

---

## 2. 現行証明チェーンの解剖

### 2.1 全体構造

```
process_rotate180 (L6413)
   ├─ [健全] floatingUnits_isEmpty_rotate180        ✅
   ├─ [健全] normalize_map_layers                    ✅
   ├─ [健全] ofLayers_rotate180                      ✅
   ├─ [健全] foldl_place_rotate180                   ✅
   ├─ [健全] sortFallingUnits_rotate180              ✅
   ├─ [健全] clearPositions_rotate180                ✅
   ├─ [健全] clearPositions_ext                      ✅
   ├─ [健全] any_map_rotate180_beq                   ✅
   ├─ [健全] falling_positions_any_rotate180          ✅
   └─ [★核心] settle_foldl_eq (L6307)
        ├─ [健全] Phase 1: sorted_foldl_pointwise_eq
        └─ [不健全] Phase 2: sortFallingUnits_foldl_perm_input_eq (L6279)
             ├─ [健全] foldl_eq_of_perm_tied_adj_comm（コールバック前提）
             ├─ [不健全] sortFallingUnits_inversion_dir_disjoint (L6234)
             │    ├─ [不健全] sortFallingUnits_inversion_is_tied (L6194)
             │    │    └─ [不健全] sortFallingUnits_spb_order_preserving (L6155)
             │    │         └─ [不健全] foldl_insertSorted_preserves_spb_order (L5932)
             │    │              └─ [❌ FALSE] shouldProcessBefore_no_chain (L5605)
             │    ├─ [健全] tied_no_shared_dir
             │    └─ [健全] floatingUnits_elem_positions_disjoint
             ├─ [健全] shouldProcessBefore_no_mutual
             └─ [健全] insertSorted_preserves_relative_order
```

### 2.2 健全/不健全の分類

| カテゴリ | 補題数 | 行数概算 | 再利用可否 |
|---|---|---|---|
| **健全（再利用可）** | ~50+ | ~5,500 | ✅ 全提案で再利用 |
| **不健全（S-5 依存）** | 6 | ~600 | ⚠️ 命題は真だが証明を修正必要 |
| **偽定理** | 1 | ~20 | ❌ 削除必須 |

### 2.3 不健全補題の詳細

| 補題 | 命題の真偽 | 修正の方向性 |
|---|---|---|
| `shouldProcessBefore_no_chain` | **FALSE** (一般) | 削除 |
| `foldl_insertSorted_preserves_spb_order` | 一般 FALSE | r180 固有制約で真になるか要検証 |
| `sortFallingUnits_spb_order_preserving` | 一般 FALSE | r180 固有制約で真になるか要検証 |
| `sortFallingUnits_inversion_is_tied` | **一般 FALSE** / r180 固有 TRUE | 証明ルート変更で救済可能 |
| `sortFallingUnits_inversion_dir_disjoint` | r180 固有 TRUE | 証明ルート変更で救済可能 |
| `sortFallingUnits_foldl_perm_input_eq` | r180 固有 TRUE | 上記 2 つの修正で自動修復 |

### 2.4 現行チェーンの問題の本質

**問題**: `sortFallingUnits` は挿入ソートベースのグリーディアルゴリズムであり、
入力の順序に対して出力が決定的でない（tied ペアの相対順序が入力順序に依存する）。

現行チェーンは「一般の置換に対して sortFU 出力間の反転は tied のみ」を主張するが、
これは **FALSE**（3L で 8,628 violations）。
r180 由来の特定の置換でのみ TRUE であり、r180 の構造（レイヤ不変性）を形式化する必要がある。

**根本原因**: 証明構築時に r180 固有の構造を一般化しすぎた。一般化された命題が偽だったため、
偽の中間補題（`shouldProcessBefore_no_chain`）で穴埋めする不健全な構造になった。

### 2.5 sortFallingUnits をより決定的にモデル化できるか

#### Q: sortFallingUnits を決定的なソートに置き換えることは原理上可能か？

**回答: はい、原理上は可能だが、2 段階の問題がある。**

**段階 1: FallingUnit 上の全順序の構築**

現行の `shouldProcessBefore` は前順序（preorder）ですらなく、以下の性質を持つ:

| 性質 | 成否 | 説明 |
|---|---|---|
| 反射性 | ❌ | `spb(a,a)` は実装が `la < lb` なので false |
| 反対称性 | ❌ | mutual pair は floatingUnits 上で不在だが、一般には存在しうる |
| 推移性 | ❌ | **`shouldProcessBefore_no_chain` (S-5) が FALSE であることが直接的証拠** |
| 全関係性 | ❌ | tied pair が存在する |

全順序を構築するには **tiebreaker** が必要。選択肢:

| Tiebreaker | 原理的可能性 | 自然さ | r180 等変 |
|---|---|---|---|
| 辞書式 positions 比較 | ✅ 可能 | 中 | **❌ 不可** |
| minLayer 比較 | ✅ 可能（ties 残る） | 高 | ✅ レイヤ不変 |
| ハッシュ値比較 | ✅ 可能 | 低 | ❌ |
| canonical 象限エンコード | ✅ 可能 | 中 | ❌（方角辞書順に依存） |

**核心的制約**: `r180 等変な FallingUnit 上の全順序は存在しない` (既知の事実)。
これは `u ≠ u.r180` なるユニットが存在し、全順序が `u < u.r180` または `u.r180 < u` を
定めねばならないが、r180 の対合性 (`r180 ∘ r180 = id`) と矛盾するためである。

したがって、決定性ソートを導入しても `sortFU'(l1) = sortFU'(l2)` (リスト等号) は
r180 由来の置換に対しては自明に成立する（Perm 不変性）が、
**`sortFU'(l).foldl f obs = sortFU(l).foldl f obs` の等価性証明が別途必要**。

**段階 2: 旧定義との foldl 等価性**

決定性ソート `sortFU'` を導入した場合、`process` 関数の定義を変更するか、
または旧 `sortFU` との foldl 等価性を証明する必要がある:

```lean
-- 定義変更パス: process の sortFallingUnits を sortFallingUnits' に差し替え
-- 等価性パス: 以下を証明
theorem sortFU_foldl_eq_sortFU'_foldl (s : Shape) (units obs) :
    (sortFU units).foldl f obs = (sortFU' units).foldl f obs
```

この等価性証明は、tied ペア（方角素）が foldl で可換であること
（`settleStep_comm_ne_dir` で証明済み）から導出可能。
ただし sortFU と sortFU' の出力差が tied ペアの順序入れ替えのみであることの形式化が必要。

#### Q: 自然な形として定式化できるか？

**定義変更パス（提案 D の発展）であれば、比較的自然**:

```lean
-- shouldProcessBefore を基盤とし、tied な場合に canonical tiebreaker で解決
instance : Ord FallingUnit where
  compare a b :=
    if shouldProcessBefore a b then .lt
    else if shouldProcessBefore b a then .gt
    else compare (a.canonicalKey) (b.canonicalKey)

def sortFallingUnits' (units : List FallingUnit) : List FallingUnit :=
    units.mergeSort (· ≤ ·)
```

ただし以下の不自然さが残る:
1. `canonicalKey` の設計が ad-hoc（ゲームロジックとの自然な対応がない）
2. `Ord` の推移性証明に spb の非推移性を tiebreaker で補正する必要がある
3. ゲーム実装（insertSorted）との乖離が生じ、「実装の正しさ」の別証明が必要

**等価性パス（定義を変えない）であれば、より自然**:

sortFU の非決定性を受け入れた上で「tied ペアは可換なので結果は同じ」と示す。
これは提案 B の核心であり、ソートの数学的性質（tied ペア = 無関係ペア）
を直接活用する。ゲームロジックとの整合性が高い。

#### 結論

| 方針 | 原理的可能性 | 自然さ | 推奨度 |
|---|---|---|---|
| 決定性ソートへの**定義変更** | ✅ 可能 | 中（tiebreaker が ad-hoc） | ★★★ |
| 決定性ソートとの**等価性証明** | ✅ 可能 | 低（2 重定義） | ★★ |
| **tied ペア可換性で直接証明**（提案 B） | ✅ 可能 | **高**（ゲームロジックと整合） | ★★★★ |

**最も自然なアプローチは「非決定性を受け入れ、可換性で吸収する」こと（提案 B）。**
決定性ソートは保守性向上のオプショナルな追加改善として位置付けるのが適切。

---

## 3. process 関数のセマンティクス（証明設計の基礎）

### 3.1 process のアルゴリズム

```
process(s) :=
  1. units := floatingUnits(s)           -- BFS で浮遊ユニット列挙
  2. if units.isEmpty then normalize(s)   -- 安定状態: 正規化のみ
  3. sorted := sortFallingUnits(units)    -- 下位優先ソート
  4. allPos := sorted.flatMap positions   -- 全浮遊象限
  5. obstacle := clearPositions(s, allPos) -- 障害物初期化
  6. result := sorted.foldl (fun obs u =>
       placeFallingUnit(s, obs, u, landingDistance(u, obs))
     ) obstacle.layers                    -- 逐次配置
  7. ofLayers(result) |>.bind normalize   -- Shape 構築 + 正規化
```

### 3.2 r180 等変性の成立条件

process_rotate180 が成立するためには、以下の各ステップが r180 等変であれば十分:

| ステップ | 等変性 | 現状 |
|---|---|---|
| floatingUnits | ✅ `.isEmpty` は等変 | `floatingUnits_isEmpty_rotate180` |
| floatingUnits | ⚠️ リスト等号は**偽** | BFS 探索順序が異なる |
| sortFallingUnits | ✅ shouldProcessBefore が等変 | `sortFallingUnits_rotate180` |
| clearPositions | ✅ .any メンバーシップで等変 | `clearPositions_rotate180` + `clearPositions_ext` |
| foldl (逐次配置) | ✅ 個別ステップは等変 | `foldl_place_rotate180` |
| **foldl (入力の並びの差異)** | **★ 核心の難所** | `settle_foldl_eq` — 不健全 |
| normalize | ✅ 等変 | `normalize_map_layers` |

### 3.3 核心の難所: foldl 入力の並びの差異

**左辺**: `sortFU((fU s).map r180).foldl f obs`
**右辺**: `sortFU(fU(s.r180)).foldl f obs`

2 つのリストの関係:
- `(fU s).map r180` と `fU(s.r180)` は **同じ要素集合の異なる順列**（BFS 順序差）
- sortFU 適用後も リスト等号にはならない（tied ペアの入力順序依存性）
- しかし **foldl 結果は等しい**（計算検証済み）

この等価性を証明するのが process_rotate180 の証明全体の核心であり、
全 6,500 行のうち ~1,500 行がこの 1 ステップに費やされている。

### 3.4 r180 変換の数学的性質（証明に利用可能な構造）

| 性質 | 説明 | 形式化状態 |
|---|---|---|
| **レイヤ不変性** | `QuarterPos.rotate180` は `.layer` を保存 | 定義から自明 |
| **方角回転** | NE↔SW, SE↔NW | 定義から自明 |
| **shouldProcessBefore 等変** | `spb(a,b) = spb(a.r180, b.r180)` | `shouldProcessBefore_rotate180` ✅ |
| **位置素性保存** | 位置素なペアは r180 後も位置素 | `map_rotate180_pairwise_disjoint` ✅ |
| **tied ↔ direction-disjoint** | floatingUnits 上で tied ペアは方角素 | `tied_no_shared_dir` ✅ |
| **l_mid/l2 の入力反転は常に tied** | r180 が層を保存するため、同方角ペアの上下関係は不変 | 計算検証済み、未形式化 |

---

## 4. 新証明チェーン提案

### 提案 A: 現行チェーンの最小修正（r180 制約の追加）

**概要**: 現行のバブルソート帰納法を維持し、`shouldProcessBefore_no_chain` への依存を
r180 固有の制約で置換する。

**核心の変更**:
- `sortFallingUnits_inversion_is_tied` の仮定に「h_ow: one-way ペアが両入力で同順」を追加
- `foldl_insertSorted_preserves_spb_order` の Case 3 を次のように修正:
  - chain a→b→w が存在する場合、same-direction chain なら spb transitivity で処理
  - different-direction chain なら direction-disjoint 可換性で処理
- `settle_foldl_eq` から r180 固有制約を供給

```
process_rotate180
  └─ settle_foldl_eq
       ├─ Phase 1: sorted_foldl_pointwise_eq                 [変更なし]
       └─ Phase 2: sortFallingUnits_foldl_perm_input_eq'     [仮定追加]
            ├─ foldl_eq_of_perm_tied_adj_comm                [変更なし]
            └─ sortFallingUnits_inversion_dir_disjoint'       [仮定追加]
                 ├─ sortFallingUnits_inversion_is_tied'       [仮定追加, 証明修正]
                 │    └─ sortFallingUnits_spb_order_preserving' [Case 3 修正]
                 │         ├─ foldl_insertSorted_preserves_spb_order' [Case 3 修正]
                 │         │    ├─ heuristic: same-dir chain → spb transitivity
                 │         │    └─ heuristic: diff-dir chain → direction-disjoint
                 │         └─ [shouldProcessBefore_no_chain 削除]
                 ├─ tied_no_shared_dir                       [変更なし]
                 └─ floatingUnits_elem_positions_disjoint    [変更なし]
```

**利点**:
- 既存コードの変更量が最小（~200 行修正）
- 既存の補題構造を維持
- テスト済みの命題はそのまま

**欠点**:
- `foldl_insertSorted_preserves_spb_order` の Case 3 修正が**非常に複雑**
  - same-dir chain の spb transitivity は自明でない（cluster 構造解析が必要）
  - diff-dir chain の方角素性証明にも insertSorted の内部構造解析が必要
- 不健全な補題群の命題を「強い仮定付きで再証明」するため、証明が冗長
- shouldProcessBefore の非推移性に起因する case 爆発のリスク

**工数**: ★★★★☆ (4/5)
**リスク**: **高** — Case 3 で新たな偽仮説に陥る可能性

---

### 提案 B: 直接 direction-disjoint 証明（推奨）

**概要**: バブルソート帰納法 (`foldl_eq_of_perm_tied_adj_comm`) は維持し、
そのコールバック（反転ペアが direction-disjoint であること）を
r180 の構造から直接証明する。S-5 依存の中間補題群を全てバイパス。

**核心のアイデア**:
1. sortFU 入力 l_mid と l2 の「入力反転」（l_mid[i] が l2 では後方にある）は常に tied
2. tied 入力反転から、sortFU 出力反転も tied であることを 2 段階で示す:
   - Step 1: 入力反転が tied → insertSorted が tied ペアの相対順序を変えない条件を形式化
   - Step 2: insertSorted が tied ペア以外の順序を保存すること（既存の `insertSorted_preserves_relative_order`）
3. tied → direction-disjoint は既存の `tied_no_shared_dir` で閉じる

```
process_rotate180
  └─ settle_foldl_eq
       ├─ Phase 1: sorted_foldl_pointwise_eq                 [変更なし]
       └─ Phase 2: sortFallingUnits_foldl_perm_input_eq_r180 [新規]
            ├─ foldl_eq_of_perm_tied_adj_comm                [変更なし]
            └─ sortFU_output_inversion_dir_disjoint_r180      [新規, 核心]
                 ├─ input_inversion_is_tied_r180              [新規, 核心]
                 │    └─ r180_preserves_layer_order           [新規, 小]
                 ├─ sortFU_tied_input_implies_tied_output     [新規, 中]
                 │    └─ insertSorted_preserves_relative_order [既存, 健全]
                 ├─ tied_no_shared_dir                        [既存, 健全]
                 └─ floatingUnits_elem_positions_disjoint     [既存, 健全]
```

**新規補題の詳細**:

```lean
-- 核心 1: r180 由来の入力反転は常に tied
-- r180 はレイヤ不変のため、同方角で minLayer が異なるペア（one-way）は
-- 両入力で同じ相対順序を持つ → 反転するのは tied ペアのみ
private theorem input_inversion_is_tied_r180 (s : Shape)
    (l_mid l2 : List FallingUnit)
    (h_mid_def : l_mid = (floatingUnits s).map g)  -- g は floatingUnit_any_in_rotate180 から
    (h_l2_def : l2 = floatingUnits s.rotate180)
    (a b : FallingUnit) (ha : a ∈ l_mid) (hb : b ∈ l_mid)
    (h_a_before_b : posIn a l_mid < posIn b l_mid)
    (h_b_before_a : posIn a l2 > posIn b l2) :
    shouldProcessBefore a b = false ∧ shouldProcessBefore b a = false

-- 核心 2: tied 入力反転は sortFU 出力でも tied 反転のまま
private theorem sortFU_tied_input_implies_tied_output
    (l1 l2 : List FallingUnit)
    (h_perm : l1.Perm l2)
    (h_nodup : l1.Nodup)
    (h_tied_input : ∀ a b, a ∈ l1 → b ∈ l1 →
        posIn a l1 < posIn b l1 → posIn a l2 > posIn b l2 →
        shouldProcessBefore a b = false ∧ shouldProcessBefore b a = false)
    (a b : FallingUnit)
    (h_order : posIn a (sortFU l1) < posIn b (sortFU l1))
    (h_inv : posIn a (sortFU l2) > posIn b (sortFU l2)) :
    shouldProcessBefore a b = false ∧ shouldProcessBefore b a = false
```

**利点**:
- 不健全な中間補題群（5 個）を完全にバイパス
- r180 の構造を直接活用するため、偽仮説のリスクが低い
- `foldl_eq_of_perm_tied_adj_comm` と健全な既存補題を全て再利用
- 「入力反転 → 出力反転」の帰納法は insertSorted の性質から自然に導出される
- 削除対象の不健全コード: ~600 行

**欠点**:
- `input_inversion_is_tied_r180` の証明に BFS 列挙順序の解析が必要
  - `floatingUnits` が `allValid` を基にクラスタ/ピンを列挙する順序の形式化
- `sortFU_tied_input_implies_tied_output` は insertSorted の構造帰納法が必要
  - ただし `insertSorted_preserves_relative_order` (S-2, 完了) が核心部分をカバー

**工数**: ★★★☆☆ (3/5)
**リスク**: **中** — BFS 列挙順序の形式化が最大の技術的課題

---

### 提案 C: Canonical Settling（着地位置の一意性から証明）

**概要**: sortFU の比較を完全に回避し、「各 FU の最終着地位置は入力順序に依存しない」ことを
直接示す。process のセマンティクスに基づくトップダウンアプローチ。

**核心のアイデア**:
1. 各 FU u の「正準着地位置」を定義: DAG の位相的順序に従って処理した場合の着地位置
2. direction-disjoint なペアは処理順序に関係なく同じ着地位置
3. direction-sharing なペアは shouldProcessBefore が一方向に決まるため、順序は一意
4. したがって process の出力は floatingUnits の集合のみに依存し、列挙順序に依存しない
5. r180 は集合を保存する → process 出力は r180 等変

```
process_rotate180
  └─ settle_canonical_eq [新規, 大]
       ├─ canonical_landing_well_defined [新規]
       │    ├─ shouldProcessBefore_no_mutual        [既存, 健全]
       │    └─ shouldProcessBefore_dag_on_shared_dir [新規]
       ├─ foldl_agrees_with_canonical [新規]
       │    ├─ settleStep_comm_ne_dir               [既存, 健全]
       │    └─ sortFU_respects_shouldProcessBefore   [新規]
       ├─ canonical_landing_r180_equivariant [新規]
       │    └─ shouldProcessBefore_rotate180         [既存, 健全]
       └─ floatingUnits_set_equal_r180 [新規]
            ├─ floatingUnit_any_in_rotate180          [既存, 健全]
            └─ floatingUnits_pairwise_disjoint        [既存, 健全]
```

**新規補題の詳細**:

```lean
-- 着地位置はユニット集合のみに依存し、処理順序に依存しない
-- （direction-sharing ペアは shouldProcessBefore で一意順序、
--   direction-disjoint ペアは可換）
private theorem settle_canonical_eq (s : Shape)
    (l1 l2 : List FallingUnit) (obs : List Layer)
    (h_perm : l1.Perm l2) (h_nodup : l1.Nodup)
    (h_sub : ∀ u, u ∈ l1 → u ∈ floatingUnits s)
    (h_sorted1 : ∀ a b, a ∈ l1 → b ∈ l1 →
        shouldProcessBefore a b = true → posIn a l1 < posIn b l1)
    (h_sorted2 : ∀ a b, a ∈ l2 → b ∈ l2 →
        shouldProcessBefore a b = true → posIn a l2 < posIn b l2) :
    l1.foldl (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs =
    l2.foldl (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs
```

**利点**:
- **最もクリーンな証明構造**: sortFU の内部に立ち入らない
- process のセマンティクスに直結するトップダウン設計
- shouldProcessBefore の非推移性を完全に回避
- SS-4 (`gravity_IsSettled`) の証明と相乗効果
- "正準着地位置" の概念は他の証明（冪等性等）にも再利用可能

**欠点**:
- 「sortFU が shouldProcessBefore を尊重する」ことの証明が必要
  - sortFU(l) において spb(a,b)=true → a が b より前
  - 現行の `sortFallingUnits_spb_order_preserving` は S-5 に依存して不健全
  - 新たに r180 に依存しない形で証明が必要（shouldProcessBefore_no_mutual で十分かは要検証）
- 「正準着地位置」の形式化が概念的に新しく、定義の設計が必要
- 既存の foldl_eq_of_perm_tied_adj_comm (バブルソート帰納法) を使わないため大量の既存コード不使用
- **settle_canonical_eq** の h_sorted1, h_sorted2 仮定を sortFU 出力に対して供給する必要
  - sortFU が spb を尊重することの証明が核心的に難しい
  - 提案 A の Case 3 問題と同根

**工数**: ★★★★★ (5/5)
**リスク**: **高** — 正準着地位置の形式化に想定外の困難が潜む可能性

**重要な懸念**: `sortFU_respects_shouldProcessBefore` の証明は、結局
`shouldProcessBefore_no_chain` 問題と同根の困難に直面する可能性がある。
insertSorted がグリーディに停止するため、3 要素以上の chain があると
spb(a,b)=true でも a が b の後方に配置されうる（S-3 の反例と同じ現象）。
ただし floatingUnits 由来の入力では 2L/3L で violations=0（計算検証済み）。

---

### 提案 D: 定義変更 — 決定性ソートへの移行

**概要**: `sortFallingUnits` の定義を変更し、入力順序に依存しない決定性ソートに置き換える。
これにより `sortFU(l1) = sortFU(l2)` が l1 ~ l2 で自動成立し、Phase 2 が自明になる。

**核心のアイデア**:
1. `DecidableLinearOrder FallingUnit` を定義（shouldProcessBefore + canonical tiebreaker）
2. `sortFallingUnits` を Mathlib の `List.mergeSort` に置き換え
3. `mergeSort` の decidable linear order に基づく決定性から `sortFU(l1) = sortFU(l2)` が成立
4. settle_foldl_eq の Phase 2 が `congr` で閉じる

```
process_rotate180
  └─ settle_foldl_eq
       ├─ Phase 1: sorted_foldl_pointwise_eq            [変更なし]
       └─ Phase 2: congr (mergeSort は Perm 不変)        [自明]

+ 追加で必要:
  process_eq_process' [新旧 process の等価性]
       └─ sortFU_eq_mergeSort [旧 sortFU と mergeSort の foldl 結果が同一]
            ├─ mergeSort_respects_shouldProcessBefore
            └─ tied_pairs_commute (settleStep_comm_ne_dir)
```

**具体的な設計**:

```lean
-- FallingUnit の全順序を定義（shouldProcessBefore を拡張）
private def fuCompare (a b : FallingUnit) : Ordering :=
    if shouldProcessBefore a b then .lt
    else if shouldProcessBefore b a then .gt
    else compare (a.positions.map hashPos) (b.positions.map hashPos)  -- canonical tiebreaker

-- 決定性ソート
def sortFallingUnits' (units : List FallingUnit) : List FallingUnit :=
    units.mergeSort (fun a b => fuCompare a b != .gt)

-- 旧定義との互換性
theorem sortFU_foldl_eq_sortFU'_foldl (s : Shape) (units : List FallingUnit) (obs : List Layer)
    (h_sub : ∀ u, u ∈ units → u ∈ floatingUnits s)
    (h_nodup : units.Nodup) :
    (sortFallingUnits units).foldl f obs = (sortFallingUnits' units).foldl f obs
```

**利点**:
- **Phase 2 が完全に自明化**: `mergeSort` の Perm 不変性は Mathlib で証明済み
- 将来の保守性が非常に高い（決定性ソートは理解しやすい）
- shouldProcessBefore の非推移性問題を完全に回避（tiebreaker が全順序を保証）
- `sortFU_foldl_eq_sortFU'_foldl` の証明も tied ペア可換で自然に導出

**欠点**:
- **定義の変更**が必要（`sortFallingUnits` の差し替え、またはラッパー追加）
- 旧定義との互換性証明が必要
- `fuCompare` の全順序性（反射・反対称・推移・全順序）の証明が必要
  - shouldProcessBefore が DAG でない場合、tiebreaker の推移性証明が意外に複雑
- mergeSort の Mathlib API 習熟が必要
- 既存テストの一部が影響を受ける可能性

**工数**: ★★★★☆ (4/5)
**リスク**: **中** — API 移行コスト。tiebreaker 全順序の形式化

**注意**: `r180 等変な全順序は存在しない` ことが既知だが、ここでは r180 等変性は不要。
全順序が存在すれば `mergeSort(l1) = mergeSort(l2)` が自動成立するため、
tiebreaker は任意の canonical な全順序で良い。

---

### 提案 E: rotateCW 分解アプローチ

**概要**: `Shape.rotate180 = mapLayers (Layer.rotateCW ∘ Layer.rotateCW)` であることを利用し、
`process_rotateCW` を先に証明してから合成で `process_rotate180` を得る。

**核心のアイデア**:
1. `process_rotateCW` を証明: `(process s).map rotateCW = process s.rotateCW`
2. `process_rotate180` は `process_rotateCW` の 2 回適用で得る

```
process_rotate180
  └─ process_rotateCW ∘ process_rotateCW
       └─ process_rotateCW [新規の主定理]
            ├─ floatingUnits_isEmpty_rotateCW     (SS-3 が前提)
            ├─ sortFallingUnits_rotateCW
            ├─ clearPositions_rotateCW
            ├─ settle_foldl_eq_rotateCW           [新規, 核心]
            └─ ...
```

**利点**:
- `process_rotateCW` が得られれば、CCW と 180° が自動的に導出される
- SS-3 の証明と組み合わせて一貫した理論体系
- rotateCW もレイヤ不変なので settle_foldl_eq の核心的困難は同じ構造

**欠点**:
- **settle_foldl_eq_rotateCW の証明は settle_foldl_eq と同等以上に困難**
  - rotateCW の方角マッピング (NE→SE→SW→NW) は r180 (NE↔SW, SE↔NW) と異なる
  - `shouldProcessBefore_rotateCW` の等変性証明が必要（r180 はペアの入れ替え、CW は巡回）
  - 既存の r180 等変性補題が直接使えない
- 既存の r180 固有インフラ（~5,000 行）がほぼ不使用
- 完全な書き直しに近い工数

**工数**: ★★★★★ (5/5)
**リスク**: **非常に高** — settle_foldl_eq の核心的困難を回避できない上に、既存資産を活かせない

---

## 5. 比較表

### 5.1 提案間の総合比較

| 指標 | A: 最小修正 | B: 直接 dir-disjoint | C: Canonical | D: 決定性ソート | E: rotateCW |
|---|---|---|---|---|---|
| **workload** | ★★★★ | ★★★ | ★★★★★ | ★★★★ | ★★★★★ |
| **リスク** | 高 | **中** | 高 | 中 | 非常に高 |
| **既存コード再利用** | 90% | **80%** | 40% | 60% | 10% |
| **削除行数** | ~100 | ~600 | ~1,500 | ~800 | ~5,000 |
| **新規行数** | ~300 | ~500 | ~2,000 | ~800 | ~5,000+ |
| **偽仮説リスク** | 高 | **低** | 中 | 低 | 中 |
| **証明の美しさ** | 低 | **中** | **高** | 中 | 中 |
| **保守性** | 低 | 中 | 高 | **高** | 高 |
| **SS-4 活用** | なし | なし | **あり** | なし | なし |
| **SS-3 前提** | 不要 | 不要 | 不要 | 不要 | **必須** |
| **bonus 定理** | なし | なし | 冪等性等 | なし | CW/CCW 等変 |

### 5.2 核心技術の比較

| 核心タスク | A | B | C | D | E |
|---|---|---|---|---|---|
| insertSorted Case 3 修正 | **必須** | 不要 | 不要 | 不要 | 不要 |
| BFS 列挙順序の形式化 | 部分的 | **必須** | 不要 | 不要 | 必須 |
| sortFU spb 尊重の証明 | あり | 不要 | **必須** | 不要 | 必須 |
| 正準着地位置の定義 | 不要 | 不要 | **必須** | 不要 | 不要 |
| DecidableLinearOrder | 不要 | 不要 | 不要 | **必須** | 不要 |
| tied 入力→出力伝播 | 不要 | **必須** | 不要 | 不要 | 不要 |
| rotateCW 等変性基盤 | 不要 | 不要 | 不要 | 不要 | **必須** |

### 5.3 リスク要因の詳細比較

| リスク要因 | A | B | C | D | E |
|---|---|---|---|---|---|
| 新たな偽補題に陥る確率 | **高** | 低 | 中 | 低 | 中 |
| 過大な一般化による失敗 | 中 | **低** | 高 | 低 | 高 |
| insertSorted 内部の複雑性 | **高** | 中 | 高 | 低 | 高 |
| Mathlib API 依存 | 低 | 低 | 低 | **中** | 低 |
| 証明途中の手戻り規模 | 中 | **小** | 大 | 中 | 大 |

### 5.4 MaM 最終目標を見据えた長期評価

#### 5.4.1 プロジェクト最終目標の確認

S2IL プロジェクトの最終目標は **MaM（Make Anything Machine: 全自動工場）の表現能力証明**:

```lean
-- フェーズ 3 の最終定理群
theorem mam_produces_any_uncolored_1layer : ...  -- T-13
theorem mam_produces_any_colored_1layer : ...    -- T-14
theorem mam_produces_any_multilayer : ...        -- T-15
```

これらの証明には以下の**全操作の r180 等変性**が前提となる:

```
process_rotate180               ← 本丸（唯一の sorry）
  ↓
gravity_rotate180_comm          ← 公開ラッパー
  ↓ 
cut_rotate180_comm              ← 証明済み（process_rotate180 に依存）
  ↓
settleAfterCut_rotate180        ← 証明済み（gravity_rotate180_comm 経由）
  
stack_rotate180_comm            ← 未証明（T-11, gravity_rotate180_comm 依存）
pinPush_rotate180_comm          ← 未証明（T-12, gravity_rotate180_comm 依存）
```

#### 5.4.2 MaM に至るまでに必要な証明チェーン

```
Phase 1（現在）: Shape Processing の等変性
  ├─ process_rotate180           ★ 本丸
  ├─ cut_rotate180_comm          ✅（process_rotate180 に依存）
  ├─ stack_rotate180_comm        ⬜（gravity_rotate180_comm 依存）
  ├─ paint_rotate180_comm        ⬜（構造的に簡単、着色は BFS 無関係）
  ├─ crystallize_rotate180_comm  ⬜
  └─ pinPush_rotate180_comm      ⬜

Phase 1.5（将来）: Wires & Logic の形式化
  ├─ LogicalSignal 型             ⬜
  ├─ Gate 操作（AND/OR/NOT/XOR） ⬜
  └─ Belt Filter / Pipe Gate     ⬜

Phase 2: 加工フローの表現
  ├─ ShapeProcessingFlow グラフ   ⬜
  ├─ フロー合成の健全性           ⬜
  └─ rotateCW/CCW の等変性        ⬜（提案 E が先行すれば有利）

Phase 3: MaM の完全性証明
  ├─ MaM 設計の Lean 記述         ⬜
  ├─ 象限分解 (T-1〜T-4)          ⬜
  ├─ 生成可能シェイプ集合の特徴付け ⬜
  └─ T-13〜T-15 の証明            ⬜
```

#### 5.4.3 各提案が将来の証明に与える影響

**提案 B: 直接 direction-disjoint（process_rotate180 特化）**

| 将来の証明への影響 | 評価 |
|---|---|
| stack_rotate180_comm | ✅ 直接有効（gravity_rotate180_comm 供給） |
| process_rotateCW | ❌ 別途類似の証明が必要（r180 固有補題は流用不可） |
| gravity 冪等性 | ❌ 直接支援なし |
| gravity_IsSettled (SS-4) | ❌ sortFU 順序保存の知見が流用困難 |
| MaM 完全性 | ✅ ブロッキング解消に十分 |

**提案 C: Canonical Settling（着地位置の一意性）**

| 将来の証明への影響 | 評価 |
|---|---|
| stack_rotate180_comm | ✅ 有効 |
| process_rotateCW | ✅ **「着地位置は集合のみに依存」は rotaCW でも成立** |
| gravity 冪等性 | ✅ **正準着地位置が定義されれば冪等性は自然に導出** |
| gravity_IsSettled (SS-4) | ✅ process セマンティクスの明確化が寄与 |
| MaM 完全性 | ✅ ブロッキング解消 + 加工フローの健全性に寄与 |

**提案 D: 決定性ソートへの移行**

| 将来の証明への影響 | 評価 |
|---|---|
| stack_rotate180_comm | ✅ 有効 |
| process_rotateCW | ✅ **mergeSort は任意の等変変換に対して Perm 不変** |
| gravity 冪等性 | ⚠️ sortFU' の冪等性は全順序から直接導出可能だが、旧互換性証明が必要 |
| gravity_IsSettled (SS-4) | ❌ 直接支援なし |
| MaM 完全性 | ✅ ブロッキング解消 |

**提案 E: rotateCW 分解**

| 将来の証明への影響 | 評価 |
|---|---|
| stack_rotate180_comm | ✅ 有効 |
| process_rotateCW | ✅ **直接得られる（主定理）** |
| gravity 冪等性 | ❌ 直接支援なし |
| gravity_IsSettled (SS-4) | ❌ 直接支援なし |
| MaM 完全性 | ✅ ブロッキング解消 + CW/CCW 等変が Phase 2 加工フローに直結 |

#### 5.4.4 MaM 最終目標からの逆算: 本当に必要な等変性

MaM の象限抽出ロジック（フェーズ A: シミュレーション処理）で必要な操作:

1. **切断 + CCW 回転 + 再切断** → 各象限の分離
2. 分離された象限の **着色・識別**
3. **積層** で多レイヤ構成
4. **落下** で安定化

これらの操作は `rotateCCW = (rotateCW)^3` で表現されるため:
- **rotateCW の等変性が得られれば、CCW と r180 は自動的に導出される**
- **ただし Phase 2 では「フローの合成」として扱うため、個別の等変性で十分**

MaM 完全性証明で真に必要なのは、**各操作が任意のシェイプに対して正しく動作すること**であり、
等変性はその**一部**にすぎない（完全性の主要部分は「全シェイプが生成可能」の構成的証明）。

#### 5.4.5 将来性を加味した総合比較（更新版）

| 指標 | A: 最小修正 | B: 直接 dir-disjoint | C: Canonical | D: 決定性ソート | E: rotateCW |
|---|---|---|---|---|---|
| **workload** | ★★★★ | ★★★ | ★★★★★ | ★★★★ | ★★★★★ |
| **リスク** | 高 | **中** | 高 | 中 | 非常に高 |
| **既存コード再利用** | 90% | **80%** | 40% | 60% | 10% |
| **process_rotate180 解決** | ✅ | ✅ | ✅ | ✅ | ✅ |
| **process_rotateCW 再利用** | ❌ | ❌ | **✅ 高** | **✅ 高** | **✅ 直接** |
| **gravity 冪等性への寄与** | ❌ | ❌ | **✅ 高** | ⚠️ 部分的 | ❌ |
| **gravity_IsSettled 寄与** | ❌ | ❌ | **✅** | ❌ | ❌ |
| **MaM Phase 2 寄与** | ❌ | ❌ | ⚠️ 間接的 | ⚠️ 間接的 | **✅ 直接** |
| **保守性** | 低 | 中 | 高 | **高** | 高 |
| **偽仮説リスク** | 高 | **低** | 中 | 低 | 中 |
| **証明の美しさ** | 低 | 中 | **高** | 中 | 中 |

#### 5.4.6 推奨戦略（MaM 最終目標を加味）

**短期（Phase 1 完了）: 提案 B を推奨（変更なし）**

理由:
- process_rotate180 のブロッキング解消が最優先
- 工数最小・リスク中で確実に完了見込み
- stack_rotate180_comm, pinPush_rotate180_comm を即座に unblock

**中期（Phase 1.5〜2）: 提案 D への段階的移行を推奨**

理由:
- 提案 B 完了後、sortFallingUnits を決定性ソートに差し替え
- 移行証明 (`sortFU_foldl_eq_sortFU'_foldl`) は tied ペア可換で自然に導出
- process_rotateCW は mergeSort の Perm 不変性で自動的に得られる
- 将来の操作追加時にも sortFU 関連の証明が自動で成立

**長期（Phase 3）: 提案 C のアイデアをオプショナルに追加**

理由:
- 「正準着地位置」の概念は MaM ソルバーの健全性証明に直接活用可能
- gravity 冪等性の証明にも寄与
- ただし工数が大きいため、Phase 3 進行中に必要性が明確化してから着手

**推奨ロードマップ（更新版）**:
```
Phase 0: SettledState (SS-1〜SS-6)
  ↓
Phase 1a: 提案 B による process_rotate180 解消
  ↓
Phase 1b: stack/pinPush/paint_rotate180_comm の証明（gravity_rotate180_comm 利用）
  ↓
Phase 1c: [オプショナル] sortFallingUnits → mergeSort 移行（提案 D）
  ↓
Phase 1.5: Wires & Logic 形式化
  ↓
Phase 2: 加工フロー表現 + rotateCW 等変性（提案 D 完了時は自明）
  ↓
Phase 3: MaM 完全性証明（必要に応じて提案 C の正準着地位置を導入）
```

---

## 6. process_rotate180 の真理値再検証ロードマップ

### 6.1 現行の検証根拠

| 根拠 | 手法 | 範囲 | 信頼度 |
|---|---|---|---|
| `Test/Behavior/GravityRotate180.lean` | `#eval` 計算検証 | 20+ 手選テストケース | 中 |
| `Test/Behavior/SortFUPermInvariant.lean` | 全順列 foldl 一致 | 2L 全形状 | 高 |
| 反例形状での個別確認 | `#eval` | S-5 反例 2 件 | 高 |
| `Test/Behavior/SortFUInvariants.lean` | 構造不変量 | 2L/3L 全形状 | 高 |
| `Test/Behavior/MutualSpbCheck.lean` | mutual spb 不在 | 2L/3L 全形状 | 高 |

### 6.2 検証の不十分な領域

| 領域 | 問題 | リスク |
|---|---|---|
| 4L+ 形状の網羅検証 | S-5 反例は 4L で発見。2L/3L 検証のみでは不十分 | **高** |
| 大規模クラスタ | 4+ 象限のクラスタは 3L 以上でのみ出現 | 中 |
| 色・パーツの多様性 | 結晶・ピンの組み合わせパターンの網羅 | 中 |
| normalize の等変性 | 末尾空レイヤ除去が r180 と可換なことの確認 | 低（証明済み） |

### 6.3 再検証計画

**Phase V-1: 4 層全形状の穷举検証（推奨）**

```lean
-- Scratch/ProcessRotate180Check4L.lean
-- 4 層 × 4 方角 × 各象限 {empty, pin, crystal} = 3^16 ≈ 43M
-- ただし empty-only layer の除去で大幅に削減。
-- 実際は non-trivial shape に限定して ~100K オーダー
#eval do
  let mut failures := 0
  for s in generateAll4LayerShapes do
    let lhs := (Gravity.process s).map Shape.rotate180
    let rhs := Gravity.process s.rotate180
    if lhs != rhs then failures := failures + 1
  return failures  -- should be 0
```

**Phase V-2: ランダムサンプリング（5L+）**

```lean
-- Scratch/ProcessRotate180Random.lean
-- 5-8 層のランダム形状を 10,000 件生成して検証
-- クラスタ・ピン・結晶の多様な組み合わせを含む
#eval do
  let mut failures := 0
  for seed in List.range 10000 do
    let s := generateRandomShape seed (numLayers := 5 + seed % 4)
    let lhs := (Gravity.process s).map Shape.rotate180
    let rhs := Gravity.process s.rotate180
    if lhs != rhs then failures := failures + 1
  return failures  -- should be 0
```

**Phase V-3: 構造的カバレッジ確認**

| テストカテゴリ | 対象 | 確認項目 |
|---|---|---|
| 空レイヤ混在 | 中間・末尾に空レイヤ | normalize + r180 の相互作用 |
| 大規模クラスタ | 4+ 象限クラスタ | BFS 順序差の影響 |
| 複数独立チェーン | spb チェーン (a→b→c→…) | sortFU の入力順序依存性 |
| ピン集中 | 同方角に 3+ ピン | shouldProcessBefore chain |
| 混合方角 | クラスタ + ピンの方角交差 | 挿入ソートの分岐パターン |

**Phase V-4: 定理の部分的 decide 検証**

```lean
-- 小さな GameConfig で decide 可能か確認
-- GameConfig.mk 2 (by omega) での全形状に対する process_rotate180
-- 2L × 4dir × {empty, pin, crystal, colored} は有限だが巨大
-- native_decide の適用可能性を調査
```

### 6.4 検証の優先度

```
Phase V-1 (4L 穷举)         ★★★★★ — S-5 反例が 4L で発見された教訓
Phase V-3 (構造的カバレッジ)  ★★★★ — 未検査パターンの洗い出し
Phase V-2 (5L+ ランダム)     ★★★ — 大規模形状の確率的検証
Phase V-4 (decide)           ★★ — 技術調査（実行可能性不明）
```

---

## 7. 推奨実行計画

### Phase 0: SettledState 完了（前提条件）

| ステップ | 内容 | 見積 |
|---|---|---|
| 0-1 | SS-4 `gravity_IsSettled` の証明 | ★★★ |
| 0-2 | SS-2 `IsSettled_crystallize` の証明 | ★★ |
| 0-3 | SS-3 `IsSettled_rotateCW` の証明 | ★★ |
| 0-4 | SS-6 `SettledShape` サブタイプの検討 | ★ |

### Phase 1: process_rotate180 の真理値再検証

| ステップ | 内容 | 見積 |
|---|---|---|
| 1-1 | Phase V-1: 4L 全形状の穷举検証スクリプト作成 + 実行 | ★★ |
| 1-2 | Phase V-3: 構造的カバレッジ確認（テストケース追加） | ★★ |
| 1-3 | Phase V-2: 5L+ ランダムサンプリング | ★ |

### Phase 2: 証明チェーン再構築（提案 B を推奨）

| ステップ | 内容 | 見積 |
|---|---|---|
| 2-1 | 不健全コードの特定・マーキング | ★ |
| 2-2 | `input_inversion_is_tied_r180` の証明 | ★★★ |
| 2-3 | `sortFU_tied_input_implies_tied_output` の証明 | ★★ |
| 2-4 | `sortFU_output_inversion_dir_disjoint_r180` の組み立て | ★ |
| 2-5 | `settle_foldl_eq` Phase 2 の書き換え | ★ |
| 2-6 | 不健全コードの削除 + sorry 除去 | ★ |
| 2-7 | 全体ビルド確認 + テスト実行 | ★ |

### Phase 3: クリーンアップ

| ステップ | 内容 | 見積 |
|---|---|---|
| 3-1 | Gravity.lean の裸 simp 安定化（残存分） | ★★ |
| 3-2 | ドキュメント更新（チートシート、この文書） | ★ |
| 3-3 | 証明依存グラフの再生成 | ★ |

---

## 8. 提案 B の詳細ロードマップ

### 8.1 核心補題 1: input_inversion_is_tied_r180

**目標**: l_mid と l2 の間で入力反転が生じるペアは常に tied であることを証明する。

**証明戦略**:

```
l_mid = (fU s).map g      （g は floatingUnit_any_in_rotate180 から）
l2   = fU(s.r180)

r180 の性質:
  ∀ u ∈ fU(s), ∀ dir: u.minLayerAtDir(dir) = (g u).minLayerAtDir(dir.r180)
  （r180 はレイヤ不変、方角のみ回転）

shouldProcessBefore(a, b) = true の必要条件:
  ∃ dir: a.minLayerAtDir(dir) = some la ∧ b.minLayerAtDir(dir) = some lb ∧ la < lb

one-way pair (a, b) で入力反転を考える:
  spb(a,b)=true → ∃ dir: minLayer(a, dir) < minLayer(b, dir)
  r180 後: minLayer(g a, dir.r180) < minLayer(g b, dir.r180) → spb(g a, g b) = true
  fU(s) と fU(s.r180) の列挙は allValid 走査順（layer 昇順）に基づく
  → one-way pair は両リストで同じ相対順序
  → 入力反転が生じない

対偶: 入力反転が生じる → one-way ではない → tied
```

**形式化の課題**:
- `floatingUnits` の列挙順序の形式化が最大の課題
  - `allValid` が layer 昇順に走査
  - `allStructuralClustersList` が `allValid.foldl` で構築
  - ピンは `allIsolatedPins` で layer 昇順
- one-way pair のレイヤ比較が列挙順序を保存することの帰納的証明

**代替アプローチ（列挙順序の形式化を回避）**:
- `floatingUnit_any_in_rotate180` の選択関数 `g` の性質のみ使用
- g が shouldProcessBefore を保存すること (`spb(a,b) = spb(g a, g b)`) を示す
- l_mid 内の位置関係を直接 l2 へ反映
- **ただし**: l_mid と l2 の対応関係は g の性質だけでは不十分かもしれない
  （g は .any ベースの選択で、位置の列挙順序は別問題）

### 8.2 核心補題 2: sortFU_tied_input_implies_tied_output

**目標**: 入力反転が全て tied なら、sortFU 出力の反転も全て tied であることを証明する。

**証明戦略**:

```
sortFU は insertSorted の foldl。

insertSorted の性質:
  1. spb(u, v)=true → u は v の前に挿入される
  2. spb(v, u)=true → u は v の後に進む
  3. tied → tiebreaker（現行は先着順で停止）

insertSorted_preserves_relative_order (S-2, 完了):
  既にソート済みリスト中の a, b (a が b の前) に対し、
  新要素 u を挿入しても a, b の相対順序は保存される

帰納的主張:
  foldl insertSorted [] l1 の出力で posIn(a) < posIn(b) のとき
  foldl insertSorted [] l2 で posIn(a) > posIn(b) となるなら、
  a, b は tied

帰納法:
  l1 = [u1, u2, ..., un], l2 は l1 の置換
  foldl の各ステップで、新要素 ui が挿入される
  - ui が one-way pair (a, b) の一方なら:
    spb が決まっているため、両方の sortFU で同じ相対位置に挿入される
  - ui が tied pair の一方なら:
    入力順序に依存するが、tied なので反転しても問題ない

  具体的には:
  sortFU(l1) と sortFU(l2) の反転ペア (a, b) について:
  - spb(a,b)=true ならば、insertSorted は l1 でも l2 でも a を b の前に置く
    → 反転しない → 矛盾
  - spb(b,a)=true ならば、同様に b を a の前に置く
    → 反転しない → 矛盾
  - tied → 成立
```

**形式化の課題**:
- insertSorted の停止規則が複雑：fuel + shouldProcessBefore の分岐
- 「one-way pair は常に同じ相対位置」の帰納法が
  `insertSorted_preserves_relative_order` で足りるかの確認
- chain (a→b→c) 存在時の挙動:
  - sortFU(l1) で a が c の前に来るとき、sortFU(l2) でも同様か？
  - spb(a,b)=true ∧ spb(b,c)=true でも spb(a,c)≠true の可能性
  - **ただし**: floatingUnits 由来の入力では 2-way 計算検証で violations=0

### 8.3 削除対象

```
shouldProcessBefore_no_chain          (~20 行)    — FALSE、削除
foldl_insertSorted_preserves_spb_order (~200 行)  — 不健全、削除
sortFallingUnits_spb_order_preserving  (~40 行)   — 不健全、削除
sortFallingUnits_inversion_is_tied     (~40 行)   — 不健全、新版で置換
sortFallingUnits_inversion_dir_disjoint (~50 行)  — 不健全、新版で置換
sortFallingUnits_foldl_perm_input_eq   (~30 行)   — 不健全、新版で置換
---
合計: ~380 行の削除
```

### 8.4 保持対象（健全な既存コード）

```
foldl_eq_of_perm_tied_adj_comm       (~300 行) — バブルソート帰納法の本体
shouldProcessBefore_no_mutual         (~200 行) — S-1、独立健全
insertSorted_preserves_relative_order (~150 行) — S-2、独立健全
tied_no_shared_dir / _rev             (~100 行) — tied → direction-disjoint
floatingUnits_elem_positions_disjoint (~100 行) — 位置素性
settleStep_comm_ne_dir               (~200 行) — 方角素 → foldl 可換
sorted_foldl_pointwise_eq            (~100 行) — Phase 1
floatingUnit_any_in_rotate180         (~50 行) — .any メンバーシップ等変
...他の基盤補題群                      (~4,000 行)
```

---

## 9. 過去の教訓と設計方針

### 9.1 偽定理の教訓 (gravity-proof-cheatsheet.md Section 9 より)

| 偽の仮定 | 教訓 |
|---|---|
| `sortFU_spb_order_on_fU` | 4要素以上で反例。≤3 要素の検証は不十分 |
| `sortFU_shouldProcessBefore_one_way_order` | spb 非推移性を過小評価 |
| `shouldProcessBefore_no_chain` | 2-3L 限定の検証は 4L+ で崩壊 |
| `sortFU_inversion_is_tied` (一般 Perm) | 一般化しすぎで偽に |
| 全順序 tiebreaker | r180 等変な全順序は存在しない |

### 9.2 設計方針

1. **段階的検証**: 新補題は必ず 4L 以上で反例チェック（lean-counterexample スキル活用）
2. **一般化の抑制**: r180 固有の構造に限定し、一般の Perm に拡張しない
3. **計算検証先行**: 形式証明着手前に `#eval` / `decide` で真偽を確認
4. **小さな補題**: 1 補題 = 1 性質。大きな補題は分割してから着手
5. **撤退基準**: 3 時間以上進展なし / 2 回以上の偽仮説発見 → 提案の見直し

---

## 10. 用語集

| 用語 | 定義 |
|---|---|
| **floatingUnit (fU)** | 浮遊する構造クラスタまたは孤立ピン |
| **shouldProcessBefore (spb)** | 共有方角で u が v より低レイヤ → u を先に処理 |
| **tied** | spb(a,b) = false ∧ spb(b,a) = false |
| **one-way** | spb(a,b) = true ∧ spb(b,a) = false（または逆） |
| **mutual** | spb(a,b) = true ∧ spb(b,a) = true（floatingUnits 上で不在） |
| **direction-disjoint** | 共有方角なし（positions の方角集合が素） |
| **入力反転** | l1 では a が b の前、l2 では b が a の前 |
| **出力反転** | sortFU(l1) では a が b の前、sortFU(l2) では b が a の前 |
| **健全** | sorry に依存しない、かつ偽補題に依存しない |
| **不健全** | 偽補題 (shouldProcessBefore_no_chain) に依存する |
