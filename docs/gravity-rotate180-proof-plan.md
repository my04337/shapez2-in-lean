# Gravity rotate180 等変性の証明計画

> 最終更新: 2026-06（3 回目の改定 — `sortFU_foldl_perm_input_eq` 偽定理修正後）

## 1. 目標

`process_rotate180`: 落下処理 (`Gravity.process`) と 180° 回転 (`Shape.rotate180`) の可換性を示す。

```lean
theorem process_rotate180 (s : Shape) :
        (process s).map Shape.rotate180 = process s.rotate180
```

この定理は `Shape.gravity_rotate180_comm` の直接の根拠であり、
Shapez2 のシェイプ操作の回転等変性を保証する中心定理の一つ。

---

## 2. 現状

### 2-1. sorry 残数: 2 件

| # | 定理名 | 行 | 概要 | 状態 |
|---|---|---|---|---|
| S-1 | `floatingUnits_spb_rank` | L5556 | floatingUnits 上で spb が DAG（ランク関数の存在） | sorry（TRUE） |
| S-2 | `sortFU_foldl_perm_input_eq` | L5585 | floatingUnits の Perm 入力に対する sortFU 後 foldl 不変性 | sorry（TRUE, floatingUnits 限定） |

### 2-2. ファイルサイズ

- `Gravity.lean`: ~5,710 行（settle_foldl_eq の大幅簡略化後）
- sorry: 2 件
- ビルド: 0 errors, 2 sorry warnings

### 2-3. 偽定理の発見と修正

#### sortFU_preserves_spb_order（2026-06 第1セッション）

2-cycle 禁止仮定では **偽**。第三者との 3-cycle が insertSorted を破壊する。

```
a = cluster [⟨0, .ne⟩, ⟨5, .se⟩]
b = cluster [⟨3, .ne⟩, ⟨0, .sw⟩]
w = cluster [⟨3, .sw⟩, ⟨0, .se⟩]

spb: a→b→w→a (3-cycle)
l = [w, a, b] → sortFU = [b, w, a] → a は b の後
```

**修正**: 削除済み。DAG ランク関数方式の `floatingUnits_spb_rank` に置換。

#### sortFU_foldl_perm_input_eq 旧版（2026-06 第2セッション）

一般の h_disj + h_rank 仮定では **偽**（新発見）。

```
x = pin(NE, 7), u = cluster[(NE,8),(SW,1)], w = pin(SW, 3)
DAG: rank(x) < rank(u) < rank(w)
spb(x,u)=true, spb(u,w)=true, x と w は tied (方角素)

l1 = [w, x, u] → sortFU = [u, w, x]
l2 = [x, u, w] → sortFU = [w, x, u]
→ u が w,x 両方と方角共有 → foldl 不可換 → 結果が異なる
```

**根本原因**: DAG 条件下でも insertSorted のグリーディ停止が非 tied ペアの
相対順序を壊す。tied な x と w の間に、両者と方角共有する u が挟まると、
u の挿入位置が入力順に依存し、non-commutative ペアの順序が変わる。

**修正**: 定理文を floatingUnits 限定に変更（`h_sub : ∀ x ∈ l1, x ∈ floatingUnits s`）。
floatingUnits の幾何制約により上記の反例パターンは実際には発生しない（後述）。

### 2-4. リファクタリング履歴

- **2026-03-29**: 半シェイプ関連コードの全削除（~160行削減, sorry 2→1）
- **2026-04**: `invCount_adj_swap_lt` 完全証明、基盤補題群 (nodup, disjoint, etc.) 完成
- **2026-06 第1セッション**: `sortFU_preserves_spb_order` 偽定理を発見・削除。
  DAG ランク関数方式に移行。
- **2026-06 第2セッション**: `sortFU_foldl_perm_input_eq` 旧版が一般入力で偽と判明。
  floatingUnits 限定に修正。settle_foldl_eq Step 3 を大幅簡略化（~60行削減）。

---

## 3. 証明パイプライン

`process_rotate180` は以下のステップの連鎖で構成されている。
`settle_foldl_eq` を除く全ステップが完全証明済み:

```
process_rotate180
  ├─ floatingUnits_isEmpty_rotate180       ✅ 落下単位の有無が r180 不変
  ├─ option_bind_normalize_rotate180       ✅ normalize と r180 の交換
  ├─ ofLayers_rotate180                    ✅ ofLayers と r180 の交換
  ├─ foldl_place_rotate180                 ✅ foldl 内の map Layer.rotate180 を除去
  ├─ sortFallingUnits_rotate180            ✅ ソートの r180 等変性
  ├─ clearPositions_rotate180              ✅ obstacle 等変性
  ├─ clearPositions_ext                    ✅ obstacle の .any メンバーシップ同値
  ├─ any_map_rotate180_beq                 ✅ 位置メンバーシップ等変性
  ├─ falling_positions_any_rotate180       ✅ 浮遊位置メンバーシップ等変性
  └─ settle_foldl_eq                       ❌ sorry — 最後の 1 ピース
```

---

## 4. settle_foldl_eq の定理文

```lean
private theorem settle_foldl_eq (s : Shape) (obs : List Layer) :
        Shape.ofLayers
          ((sortFallingUnits ((floatingUnits s).map FallingUnit.rotate180)).foldl
            (fun obs u => placeFallingUnit s.rotate180 obs u (landingDistance u obs)) obs) =
        Shape.ofLayers
          ((sortFallingUnits (floatingUnits s.rotate180)).foldl
            (fun obs u => placeFallingUnit s.rotate180 obs u (landingDistance u obs)) obs)
```

LHS は `(floatingUnits s).map FU.rotate180` をソートして foldl、
RHS は `floatingUnits s.rotate180` をソートして foldl する。
2 つの入力リストは BFS 探索順序の違いにより **リスト等号でも List.Perm でもない**。

### 4-1. settle_foldl_eq の現在の証明構造

```
settle_foldl_eq
  ├─ l_mid 構築 (Classical choice)                    ✅ 証明済
  ├─ Step 2: sortFU l1 foldl = sortFU l_mid foldl
  │   └─ sorted_foldl_pointwise_eq                    ✅ 証明済
  └─ Step 3: sortFU l_mid foldl = sortFU l2 foldl
      └─ sortFU_foldl_perm_input_eq (floatingUnits版) ← sorry
```

Step 3 は `sortFU_foldl_perm_input_eq` への単純な `apply + exact` で完了。
h_sub の提供は `h_mid_sub : l_mid ⊆ l2 = floatingUnits s.rotate180` で直接。

---

## 5. 核心問題: shouldProcessBefore の非反対称性

### 5-1. shouldProcessBefore の性質

`shouldProcessBefore a b` は各方角列での最小レイヤの大小比較であり、
**反対称律を一般には満たさない**。

```
クラスタ A: {(layer 0, NE), (layer 3, SW)}
クラスタ B: {(layer 1, NE), (layer 2, SW)}
→ spb(A,B) = true (NE列: 0 < 1)
→ spb(B,A) = true (SW列: 2 < 3)
```

### 5-2. ペアの分類

| 種類 | 条件 | 方角列共有 | foldl 交換可能 |
|---|---|---|---|
| 通常 | 片方のみ true | あり | 順序固定（ソートで解決） |
| tied | 双方 false | なし | はい (`settleStep_comm_ne_dir`) |
| cyclic | 双方 true | あり（複数列で逆方向） | 幾何的に発生不可能（推定） |

### 5-3. insertSorted のグリーディ動作と DAG の関係

**DAG 条件下でも insertSorted は非 tied ペアの順序を壊しうる**（§2-3 の反例参照）。

根本原因: insertSorted は「最初のマッチで停止」するグリーディアルゴリズム。
要素 u の挿入時、spb(u, w) = true で停止した場合、
u の手前にある tied 要素 x が u と方角共有していても、
x と u の相対順序は制御できない。

---

## 6. 正しい証明方針: floatingUnits 限定アプローチ

### 6-1. なぜ一般定理は偽か

`sortFU_foldl_perm_input_eq` に必要な仮定:
- `l1 ~ l2` (Perm) + NoDup
- 位置素性 (h_disj)
- DAG 条件 (h_rank)

これだけでは、以下のパターンを排除できない:
- 3 要素 x, u, w で x-w tied, u が x,w 両方と方角共有
- tiebreaker により w が x より先にソートされる
- u 挿入時に w で停止 → u が x より前に配置 → x-u の順序が入力順依存

### 6-2. floatingUnits の幾何制約が排除するもの

floatingUnits の幾何的制約:

1. **同レイヤ隣接方角排除**: 異なる構造クラスタは同一レイヤの隣接方角に
   位置を持てない（持てば構造結合で同一クラスタにマージ）。

2. **方角遷移層の排他性**: クラスタが水平結合で方角を変える層では、
   そのクラスタが 2 方角を占有し、残り 2 方角も隣接して封鎖される。
   → 他クラスタはその層に一切位置不可。

3. **2方角クラスタの制約**: 反例の u = cluster[(NE,8),(SW,1)] のような
   対角方角の組み合わせは、中間方角(SE or NW)の遷移層を必要とする。
   遷移層で全方角が封鎖されるため、同一領域に tied な別要素が存在不可能。

4. **孤立ピン**: 各ピンは 1 方角列のみ占有。ピン同士では反例パターン不可。

これらの制約により、反例の 3 要素パターン（x-w tied, u が両方と方角共有）は
floatingUnits から生成される FallingUnit リストでは発生しない。

### 6-3. 定理文の正しい形

```lean
private theorem sortFU_foldl_perm_input_eq (s : Shape)
        (l1 l2 : List FallingUnit) (obs : List Layer)
        (h_perm : l1.Perm l2)
        (h_nodup_l1 : l1.Nodup)
        (h_sub : ∀ x, x ∈ l1 → x ∈ floatingUnits s) :
        (sortFallingUnits l1).foldl
            (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs =
        (sortFallingUnits l2).foldl
            (fun obs u => placeFallingUnit s obs u (landingDistance u obs)) obs
```

`h_sub` により、floatingUnits_pairwise_disjoint, floatingUnits_nodup,
floatingUnits_spb_rank, 及び幾何制約を全て利用可能。

---

## 7. 推奨ロードマップ

### Phase 1: `floatingUnits_spb_rank` の証明 (~200-400 行) ← 最大の難所

floatingUnits 上で spb が DAG であることを証明する。
ランク関数 `rank : FallingUnit → Nat` を構成し、
`spb(fU[i], fU[j]) = true → rank(fU[i]) < rank(fU[j])` を示す。

**サブステップ**:
1. Pin-Pin: 同方角なら minLayer がランク、異方角なら spb=false
2. Pin-Cluster: ピンの唯一の方角列でのレイヤ比較
3. Cluster-Cluster: 幾何制約の形式化（最大の難所）
   - `reachable_visits_intermediate_layer` (BFS パスの中間値定理)
   - `clusters_no_adj_same_layer` (同レイヤ排除)
   - minLayer の per-direction 比較 → global ランクへの集約

### Phase 2: `sortFU_foldl_perm_input_eq` の証明 (~200-400 行)

**方法 A**: sortFU の反転ペアが全て direction-disjoint であることを証明

1. `sortFU_preserves_spb_order_inFU`: floatingUnits 条件下の spb 順序保存
   - insertSorted の帰納法 + `insertSorted_split`
   - DAG 条件 + floatingUnits 幾何制約の追加仮定
   - 反例パターン (§2-3) の排除

2. `foldl_eq_of_perm_tied_adj_comm` の既存証明を活用
   - s1 = sortFU l1, s2 = sortFU l2
   - 反転ペアは全て tied → 方角素 → foldl 可換

**方法 B**: sortFU の出力が入力順序非依存であることを直接証明

1. floatingUnits 幾何制約から「反例パターン排除」を形式化
2. 排除されたパターン以外では insertSorted が一貫 → sortFU l1 = sortFU l2

**方法 C**: 別のソートを定義して等価性を示す

1. ランク関数で要素をソートした `rankSort` を定義
2. `rankSort l foldl = sortFU l foldl` を tied ペア可換性で証明
3. `rankSort l1 = rankSort l2` (決定的ソート)

### Phase 3: 統合と検証 (~50 行)

- settle_foldl_eq の sorry 除去
- process_rotate180 → gravity_rotate180_comm の完全証明確認
- ビルド: 0 errors, 0 sorry warnings

---

## 8. 利用可能な基盤補題

### 等変性インフラ

| 補題 | 概要 |
|---|---|
| `isStructurallyBonded_rotate180` | 構造結合の rotate180 不変性 |
| `structuralCluster_mem_rotate180` | クラスタメンバーシップの .any レベル rotate180 保存 |
| `groundedPositions_mem_rotate180` | 接地位置の .any レベル rotate180 保存 |
| `shouldProcessBefore_rotate180` | ソート述語の rotate180 不変性 |
| `FallingUnit.positions_rotate180` | 位置リストの rotate180 等変性 |
| `FallingUnit.minLayer_rotate180` | 最小レイヤの rotate180 不変性 |
| `FallingUnit.minLayerAtDir_rotate180` | 方角別最小レイヤの rotate180 等変性 |
| `sortFallingUnits_rotate180` | ソートの rotate180 等変性 |
| `landingDistance_rotate180` | 着地距離の rotate180 不変性 |
| `placeFallingUnit_rotate180` | 配置操作の rotate180 等変性 |

### ソート・foldl インフラ

| 補題 | 概要 |
|---|---|
| `insertSorted_perm` | insertSorted は Perm を保存 |
| `insertSorted_split` | insertSorted = take k ++ [u] ++ drop k |
| `sortFallingUnits_perm` | sortFU は入力の Perm |
| `sortFallingUnits_any_positions` | sortFU は位置 .any を保存 |
| `sortFallingUnits_pointwise_ext` | pointwise .any 等価入力 → pointwise .any 等価出力 |
| `sorted_foldl_pointwise_eq` | pointwise .any 等価 → foldl 結果一致 |
| `foldl_pointwise_ext` | pointwise .any 等価 → foldl 全体一致 |
| `invCount_adj_swap_lt` | 隣接要素の反転 swap で転置数が減少 |

### 交換則インフラ

| 補題 | 概要 |
|---|---|
| `settleStep_comm_ne_dir` | 方角列非共有ペアの settleStep 可換性 |
| `foldl_settle_head_swap` | 方角素隣接要素の swap → foldl 不変 |
| `foldl_settle_swap_at` | prefix 付き方角素 swap → foldl 不変 |
| `tied_no_shared_dir` / `_rev` | tied ペア → 方角列を共有しない |
| `shouldProcessBefore_ext` | spb は .any にのみ依存 |

### 位置素性・NoDup インフラ

| 補題 | 概要 |
|---|---|
| `floatingUnits_pairwise_disjoint` | 浮遊単位は互いに位置素 |
| `map_rotate180_pairwise_disjoint` | .map rotate180 は位置素性を保存 |
| `floatingUnits_nodup` | floatingUnits は NoDup |
| `allValid_nodup` | allValid は NoDup |
| `allStructuralClusters_nodup` | クラスタリストは NoDup |
| `allStructuralClusters_disjoint` | クラスタは互いに位置素 |
| `allStructuralClusters_all_bondable` | クラスタ全位置は bondable |

### 浮遊単位構造

| 補題 | 概要 |
|---|---|
| `floatingUnits_eq_append` | floatingUnits = fc.map .cluster ++ fp.map .pin |
| `allIsolatedPins_is_pin` | ピン位置の getQuarter = some .pin |
| `floatingUnits_isEmpty_rotate180` | 浮遊単位の有無は rotate180 不変 |
| `falling_positions_any_rotate180` | flatMap positions の .any メンバーシップ等変性 |
| `floatingUnits_length_rotate180` | \|fU(s)\| = \|fU(s.r180)\| |
| `floatingUnit_any_in_rotate180` | 各 u ∈ fU(s) に .any 等価な v ∈ fU(s.r180) |

---

## 9. 過去の棄却済みアプローチ

| アプローチ | 棄却理由 |
|---|---|
| リスト等号 `fU s.r180 = (fU s).map r180` | BFS 順序差で偽 |
| `List.Perm` レベル `floatingUnits_perm_rotate180` | BFS 内部順序差で偽（cluster [p1,p2] ≠ cluster [p2,p1]） |
| flatMap .any 等価 + 位置素 → foldl 一致 | ユニット分割差で偽 |
| pointwise .any 等価 → foldl 一致 | 入力順序差で pointwise にならない |
| tiebreaker 厳密全順序 | r180 等変な厳密全順序は (u, u.r180) ペアで矛盾 |
| shouldProcessBefore の反対称化 | cyclic → tied 化で方角共有の foldl 可換性が不成立 |
| `sortFU_preserves_spb_order` (2-cycle 禁止のみ) | 偽定理: 3-cycle で insertSorted 不整合 |
| `sortFU_foldl_perm_input_eq` 一般版 (h_disj + h_rank) | 偽定理: DAG+位置素でも排除不可な 3 要素パターン |
| tiebreaker 全順序 (minLayerAtDir 辞書式) | r180 が方角を置換するため辞書式順序が r180 非等変 |

---

## 10. 偽定理の教訓

### 10-1. `sortFU_preserves_spb_order` (2026-06 第1セッション)

- **ペアワイズ 2-cycle 禁止 ≠ DAG**: 全ペアの 2-cycle がなくても 3-cycle 以上が存在
- **insertSorted のグリーディ性**: 最初のマッチで停止 → 第三者が遮ると不整合
- **修正**: 偽定理を削除。DAG ランク関数方式に移行。

### 10-2. `sortFU_foldl_perm_input_eq` 一般版 (2026-06 第2セッション)

- **DAG + 位置素 ≠ sortFU 順序一貫性**: 3 要素パターン (x-w tied, u が両者と方角共有)
  で insertSorted が入力順依存の順序を生成する
- **一般的な h_disj + h_rank ではこのパターンを排除不可能**
- **修正**: 定理文を floatingUnits 限定に変更。幾何制約が反例パターンを排除。

### 10-3. tiebreaker 全順序化 (2026-06 第2セッション)

- **r180 等変な全順序は FallingUnit 上に存在しない**: u と u.r180 が同値になるため
- **sortFallingUnits_rotate180** を保つには比較関数が r180 不変である必要
- **方角の置換により辞書式順序は r180 非等変**
- **修正**: tiebreaker 変更アプローチを棄却。一般化を諦め floatingUnits 限定に。

### 10-4. 過去の偽定理一覧

| 定理 | 発見時期 | 根本原因 |
|---|---|---|
| `spb_antisymm_of_disjoint` | 2026-03 | 位置素のみでは反対称不成立 |
| `foldl_sorted_disjoint_flatMap_eq` | 2026-03 | unit 分割差を考慮していない |
| `floatingUnits_rotate180` | 2026-03 | BFS 順序差でリスト等号が偽 |
| `floatingUnits_perm_rotate180` | 2026-03 | BFS 内部順序差（cluster 要素順） |
| `sortFU_preserves_spb_order` | 2026-06 | 3-cycle で insertSorted 不整合 |
| `sortFU_foldl_perm_input_eq` 一般版 | 2026-06 | DAG+位置素でも排除不可な 3 要素パターン |

---

## 11. リスク

| # | リスク | 深刻度 | 回避策 |
|---|---|---|---|
| R-1 | floatingUnits 幾何制約の形式化コスト | 高 | BFS パスの方角遷移層 + 同レイヤ排除の帰納法。GenericReachable 基盤は既存 |
| R-2 | 方角遷移層の封鎖証明 | 高 | Direction の 4 要素環状構造を場合分けで処理 |
| R-3 | sortFU_preserves_spb_order に floatingUnits 条件が必要 | 中 | h_sub 仮定により floatingUnits の全補題が利用可能 |
| R-4 | Phase 2 の方法選択 | 中 | 方法 A (反転ペア方角素) が既存インフラを最大活用。方法 C (rankSort) は バックアップ |
| R-5 | 経験的検証では未発見のエッジケース | 低 | テストケースで幅広くカバー済み。反例チェック手法は確立済み |
