# Gravity 証明チートシート

> 対象ファイル: `S2IL/Behavior/Gravity.lean`（~6,500 行）
> 最終更新: 2026-04-05 22:30

**証明作業を開始する前に、このチートシートを通読してください。**

---

## 0. お知らせ: レイヤ数上限制約の導入 (2026-04-02)

`Shape.stack` と `Shape.pinPush` にレイヤ数上限の前提条件が導入されました。

| 変更 | 概要 |
|---|---|
| `Shape.stack` | `_h_bottom : bottom.layerCount ≤ config.maxLayers` および `_h_top : top.layerCount ≤ config.maxLayers` を追加。工程5a (`shatterOnTruncate`) を削除（上側結晶は工程2で砕け散り済みのため不要） |
| `Shape.pinPush` | `_h_s : s.layerCount ≤ config.maxLayers` を追加 |

**本チートシートの対象である `process_rotate180` 証明パイプラインへの影響はありません。**
`Gravity.process` は `stack`/`pinPush` を使用せず、`settle_foldl_eq` も無関係です。

ただし、将来 `stack_rotate180_comm` や `pinPush_rotate180_comm` を証明する際には、
`gravity_rotate180_comm` をその内部で使用することになります（両者とも内部で `gravity` を呼ぶため）。
また、レイヤ数上限制約により `truncate` 前の `shatterOnTruncate` が stack で不要になったことで、
`stack_rotate180_comm` の証明パイプラインが簡素化されます:

```
変更前: placeAbove_r180 → shatterTopCrystals_r180 → gravity_r180 → shatterOnTruncate_r180 → truncate_r180 → gravity_r180
変更後: placeAbove_r180 → shatterTopCrystals_r180 → gravity_r180 → truncate_r180 → gravity_r180
```

前提条件 `h_bottom`/`h_top` と `layerCount_rotate180` の組み合わせでレイヤ数制約の保存が自明。

---

## 1. ビルド状態

| 項目 | 値 |
|---|---|
| errors | 0 |
| sorries | 1 |
| warnings | 0 |

---

## 2. 目標定理

```lean
theorem process_rotate180 (s : Shape) :
    (process s).map Shape.rotate180 = process s.rotate180
```

落下処理 `Gravity.process` と 180° 回転 `Shape.rotate180` の可換性。
`Shape.gravity_rotate180_comm` → `cut_rotate180_comm` の前提条件。

---

## 3. sorry 箇所

| # | 定理 | 行 | 概要 | 真理値 | 難度 | 状態 |
|---|---|---|---|---|---|---|
| S-1 | `spb_no_mutual` | ~~L5019~~ | floatingUnits 間で spb 双方向 true 不可 | TRUE | ★★★ | ✅ 完了 |
| S-2 | `insertSorted_preserves_relative_order` | ~~L5253~~ | insertSorted が既存要素の相対順序保存 | TRUE | ★★ | ✅ 完了 |
| S-3 | ~~`sortFU_spb_one_way_order`~~ | ~~L5274~~ | ~~one-way spb ペアが sortFU で順序保存~~ | **FALSE** | - | ❌ **偽と判明、削除済み** |
| S-4a | `sortFU_inversion_is_tied` | L6194 | sortFU の反転ペアは tied (spb 双方 false) | TRUE (計算検証) | ★★★ | ✅ **完了** (S-5 に依存) |
| S-4b | `sortFU_inversion_dir_disjoint` | L6234 | sortFU の反転ペアは方角素 | TRUE | ★★ | ✅ **完了** (S-4a に依存) |
| S-5 | `spb_no_chain` | L5605 | floatingUnits 間で spb 連鎖 (a→b→c) は不可 | **FALSE** | - | ❌ **偽と判明** |

### S-3 → S-4 の経緯

S-3 (`sortFU_spb_one_way_order`) は **floatingUnits の制約下でも偽** と判明。
反例: `a=pin(2,NE), b=cluster[(4,NE),(4,SE)], c=pin(6,SE)` — spb の非推移三角形により
`sortFU([c,a,b])` で spb(a,b)=true でも a が b の後に来る。

代替として S-4 を **2段階** で構成:
- **S-4a** (`sortFU_inversion_is_tied`): sortFU の反転ペアが tied (spb 双方 false) であることを主張 → **sorry**
- **S-4b** (`sortFU_inversion_dir_disjoint`): S-4a + `tied_no_shared_dir` + `fU_elem_positions_disjoint` から direction-disjoint を導出 → **✅ 完了**

#### 数学的洞察: tied ↔ direction-disjoint

`floatingUnits(s)` の要素 `a ≠ b` について:
- 方角 `d` を共有 (双方とも `minLayerAtDir d = some`) → 最小レイヤ値が異なる（等しければ同一 QuarterPos → position-disjoint に矛盾）→ `spb(a,b)=true` or `spb(b,a)=true`
- **対偶**: tied (双方 false) → 方角を共有しない → direction-disjoint

この洞察により S-4b は S-4a から自動的に導出され、残 sorry は S-4a の「反転ペアは tied」のみに集約される。

### sorry の依存関係

```
process_rotate180 ← settle_foldl_eq ← sortFU_foldl_perm_input_eq
    ├── spb_no_mutual (S-1)                               ✅ 完了
    ├── sortFU_inversion_dir_disjoint (S-4b)             ⚠️ 証明不健全 (S-5依存)
    │     ├── sortFU_inversion_is_tied (S-4a)            ⚠️ 証明不健全 (S-5依存)
    │     ├── tied_no_shared_dir                         ✅
    │     ├── tied_no_shared_dir_rev                     ✅
    │     └── fU_elem_positions_disjoint                 ✅
    └── foldl_eq_of_perm_tied_adj_comm                   ✅
```

> **S-1・S-2・S-4a・S-4b は完了**。S-3・S-5 は偽と判明。
> **S-5 (`spb_no_chain`) は FALSE** — 証明チェーンの再構築が必要。
> ⚠️ S-4a/S-4b/sortFU_foldl_perm_input_eq の証明は S-5 に依存しており不健全。

### 各 sorry の詳細

**S-1: `spb_no_mutual` — ✅ 完了**
- d1=d2 ケース: `lu < lv ∧ lv < lu → omega`
- d1≠d2 ケース: 4-horizontal-step 矛盾戦略で証明完了
  - `genReachable_diff_dir_horizontal` でクラスタ内パスの水平ステップが a.dir = p.dir を返すことを利用
  - `minLayerAtDir_le_of_mem` で最小レイヤ制約を導出

**S-2: `insertSorted_preserves_relative_order` — ✅ 完了**
- `insertSorted_split` で挿入位置 k を取得、k と a,b の位置関係で 3 case 分岐

**S-3: `sortFU_spb_one_way_order` — ❌ 偽と判明、削除済み**
- 反例: a=pin(2,NE), b=cluster[(4,NE),(4,SE)], c=pin(6,SE), l=[c,a,b]
  - spb(a,b)=T, spb(b,a)=F, spb(b,c)=T, spb(c,b)=F, spb(a,c)=F
  - sortFU([c,a,b]) = [b,c,a]: posIn a=2, posIn b=0 → S-3 fails
- spb の非推移性が根本原因
- 実 shape `"--------:--------:P-------:--------:CrCr----:--------:--P-----:--------"` でも確認

**S-4a: `sortFU_inversion_is_tied` — ✅ 完了 (L6194)**
- sortFU(l1) と sortFU(l2) の反転ペアが tied (spb 双方 false)
- `sortFallingUnits_spb_order_preserving` (L6155) を使用して証明
  - この補題は `foldl_insertSorted_preserves_spb_order` (L5932) + `posIn_lt_of_decomposition` (L6108) から構成
  - 4-case 不変条件分析: (a=u,b=u)→矛盾, (a=u,b∈acc)→insertSorted_before_spb, (a∈acc,b=u)→spb_no_chain+append, (a∈acc,b∈acc)→preserves_relative_order
- `spb_no_chain` (S-5, sorry) に依存

**S-5: `spb_no_chain` — ❌ 偽と判明 (2026-04-05)**
- floatingUnits の要素 a, b, c で spb(a,b)=true ∧ spb(b,c)=true → False は **FALSE**
- **反例 1 (3-pin same column, 6層)**: Shape `"--------:P-------:--------:P-------:--------:P-------"`
  - floatingUnits: [pin(1,NE), pin(3,NE), pin(5,NE)]
  - spb(pin1,pin3) = true (NE: 1<3), spb(pin3,pin5) = true (NE: 3<5)
  - layer 0 が全空のため全 pin が floating。pin は canFormBond=false で独立。
- **反例 2 (mixed direction, 4層)**: Shape `"--------:P-------:CrCr----:--P-----"`
  - floatingUnits: [cluster({SE@2,NE@2}), pin(1,NE), pin(3,SE)]
  - spb(pin(1,NE), cluster) = true (NE: 1<2), spb(cluster, pin(3,SE)) = true (SE: 2<3)
  - さらに sortFU(fus) ≠ sortFU(fus.reverse)（sortFU が入力順依存）
- **事前計算検証の不備**: 2L/3L のみで 4L+ 形状を未検証。4 層以上で反例が成立する。
- **process_rotate180 は全反例形状で TRUE** — 最終定理は正しいが証明チェーンが不健全

**S-4b: `sortFU_inversion_dir_disjoint` — ✅ 完了 (L6234)**
- sortFU(l1) と sortFU(l2) の反転ペアが direction-disjoint
- S-4a (`sortFU_inversion_is_tied`) + `fU_elem_positions_disjoint` + `tied_no_shared_dir` / `tied_no_shared_dir_rev` から導出
- 2026-04-05 に sorry 解消。数学的洞察「tied ↔ direction-disjoint」を活用

---

## 4. 証明パイプライン

```
process_rotate180 (L6413)
  ├─ floatingUnits_isEmpty_rotate180       ✅
  ├─ option_bind_normalize_rotate180       ✅
  ├─ ofLayers_rotate180                    ✅
  ├─ foldl_place_rotate180                 ✅
  ├─ sortFallingUnits_rotate180            ✅
  ├─ clearPositions_rotate180              ✅
  ├─ clearPositions_ext                    ✅
  ├─ any_map_rotate180_beq                 ✅
  ├─ falling_positions_any_rotate180       ✅
  └─ settle_foldl_eq (L6307)               ✅ (Phase 1 + Phase 2)
       ├─ sorted_foldl_pointwise_eq           ✅ Phase 1
       └─ sortFU_foldl_perm_input_eq (L6279)  ✅ (sorry × 1 内包)
            ├─ foldl_eq_of_perm_tied_adj_comm    ✅ バブルソート帰納法
            ├─ sortFU_inversion_dir_disjoint (L6234) ✅ (S-4b)
            │    ├─ sortFU_inversion_is_tied (L6194)  ✅ (S-4a)
            │    │    └─ sortFallingUnits_spb_order_preserving (L6155) ✅
            │    │         ├─ foldl_insertSorted_preserves_spb_order (L5932) ✅
            │    │         │    ├─ insertSorted_before_spb           ✅
            │    │         │    ├─ insertSorted_append_when_no_spb (L5902) ✅
            │    │         │    ├─ insertSorted_preserves_relative_order ✅ (S-2)
            │    │         │    └─ spb_no_chain (L5605)              ❌ sorry (S-5)
            │    │         └─ posIn_lt_of_decomposition (L6108)      ✅
            │    ├─ tied_no_shared_dir            ✅
            │    ├─ tied_no_shared_dir_rev        ✅
            │    └─ fU_elem_positions_disjoint    ✅
            ├─ spb_no_mutual                     ✅ (S-1)
            └─ insertSorted_preserves_relative_order ✅ (S-2)
```

---

## 5. settle_foldl_eq の証明構造

`settle_foldl_eq` は以下の 2 フェーズに分解済み:

### Phase 1: pointwise .any 等価による foldl 等価 ✅

`sorted_foldl_pointwise_eq` を使用: l1 = (fU s).map r180 と l_mid = (fU s).map g が
各インデックスで .any 等価であることから、sortFU(l1).foldl = sortFU(l_mid).foldl。

### Phase 2: Perm 不変性による foldl 等価 ✅ (sorry 内包)

l_mid.Perm l2 を示し、`sortFU_foldl_perm_input_eq` を適用。
`sortFU_foldl_perm_input_eq` の本体は `foldl_eq_of_perm_tied_adj_comm` (バブルソート帰納法) を呼び出し、
h_tied_comm コールバック内で `sortFU_inversion_dir_disjoint` (S-4b) を使用。

---

## 6. sortFU_foldl_perm_input_eq の内部構造

```lean
private theorem sortFU_foldl_perm_input_eq (s : Shape)
    (l1 l2 : List FallingUnit) (obs : List Layer)
    (h_perm : l1.Perm l2)
    (h_nodup : l1.Nodup)
    (h_sub : ∀ u, u ∈ l1 → u ∈ floatingUnits s) :
    (sortFallingUnits l1).foldl (...) obs = (sortFallingUnits l2).foldl (...) obs
```

### h_tied_comm コールバックの論理

`sortFU_inversion_dir_disjoint` (S-4b) を直接使用:
sl1 = sortFU(l1), sl2 = sortFU(l2) の反転ペアが direction-disjoint であることを S-4b が保証。
`foldl_eq_of_perm_tied_adj_comm` のコールバックに直接渡される。
S-4b は完全に証明済み (S-4a の sorry に依存)。

### S-4a の証明ロードマップ (今後の課題)

S-4a (`sortFU_inversion_is_tied`) は以下の 3 段階で証明可能:
1. **入力の反転は tied のみ**: `floatingUnits` の BFS 列挙順序が layer 昇順であることから、
   one-way pair の相対順序は `(fU s).map g` と `fU(s.r180)` の間で保存される
2. **sortFU は tied-only inversion を保存**: insertSorted の可換性（tied pair の処理順序入れ替えは結果に影響しない）
3. 1+2 から、sortFU 出力間の inversion は tied のみ

**注意**: `sortFU_inversion_is_tied` の型シグネチャは一般の `l1.Perm l2` に対しては偽 (3L で 516 violations)。
`floatingUnits(s)` 由来の特定の permutation (`(fU s).map g` と `fU(s.r180)`) でのみ真。
形式化には BFS 列挙順の帰納的解析が必要。

---

## 7. ファイル構造マップ

| 行範囲 | カテゴリ | 内容 | 状態 |
|---|---|---|---|
| L1-40 | ヘッダ | SPDX, import, namespace 開始 | ✅ |
| L40-370 | コア定義 | 構造結合, BFS, FallingUnit, sortFU, process | ✅ |
| L374-878 | 基本等変性 | rotate180 基盤補題 | ✅ |
| L881-1324 | BFS 健全性 | structuralClusterList の正当性 | ✅ |
| L1352-1831 | 到達可能性 | floatingUnits 非空性, クラスタ存在 | ✅ |
| L1867-2210 | 着地等変性 | foldl_place_rotate180 等 | ✅ |
| L2214-3091 | foldl 可換性 | settleStep_comm_ne_dir 等 | ✅ |
| L3115-3310 | tied 性質 | tied_no_shared_dir 等 | ✅ |
| L3312-3610 | pointwise 等価 | sortFU_pointwise_ext, sorted_foldl_pointwise_eq | ✅ |
| L3616-3900 | 位置素性 | floatingUnits_pairwise_disjoint | ✅ |
| L3900-4224 | 補助定理 | perm/length 等変性, insertSorted_split | ✅ |
| L4225-5400 | バブルソート基盤 | posIn, invCount, swap, foldl_eq_of_perm_tied_adj_comm | ✅ |
| L5400-5600 | spb_no_mutual | S-1 完了 | ✅ |
| L5600-5620 | spb_no_chain | sorry (S-5) | ❌ |
| L5620-5900 | insertSorted 補題 | insertSorted_before_spb ✅, _preserves_ (S-2) ✅ | ✅ |
| L5900-5932 | insertSorted_append_when_no_spb | no-spb 時の末尾追加 | ✅ |
| L5932-6108 | foldl_insertSorted_preserves_spb_order | 4-case 不変条件 (S-5 に依存) | ✅ |
| L6108-6155 | posIn_lt_of_decomposition | 分解からの位置比較 | ✅ |
| L6155-6194 | sortFallingUnits_spb_order_preserving | spb 順序保存 (S-4a 中核) | ✅ |
| L6194-6234 | sortFU_inversion_is_tied | S-4a ✅ (S-5 に依存) | ✅ |
| L6234-6279 | sortFU_inversion_dir_disjoint | S-4b ✅ (S-4a に依存) | ✅ |
| L6279-6307 | sortFU_foldl_perm_input_eq | 本体完成 (S-4b に依存) | ✅ |
| L6307-6413 | settle_foldl_eq | Phase 1 + Phase 2 (完成) | ✅ |
| L6413-6450 | process_rotate180 | 最終目標定理 | ✅ |
| L6450+ | Shape 拡張 | IsSettled, gravity_rotate180_comm 等 | ✅ |

---

## 8. 確立済みの事実（覆らない）

| 事実 | 根拠 |
|---|---|
| `process_rotate180` は真 | 20+ テストケースで計算検証済み |
| spb は floatingUnits 上で DAG（2-cycle 禁止） | 計算検証 + 幾何制約 |
| 方角素ペアは foldl で可換 | `settleStep_comm_ne_dir` で証明済み |
| tied + 位置素 → 方角素 | `tied_no_shared_dir` / `tied_no_shared_dir_rev` で証明済み |
| **tied ↔ direction-disjoint (floatingUnits 上)** | 共有方角 → minLayer 差 → one-way → 対偶で tied → 方角素 |
| sortFU_inversion_dir_disjoint は完全証明済み | sortFU_inversion_is_tied + tied_no_shared_dir から導出 (L6234) |
| **sortFU_inversion_is_tied は完全証明済み** | sortFallingUnits_spb_order_preserving + spb_no_chain (sorry) から導出 (L6194) |
| **spb 2 段連鎖は floatingUnits で発生し得る** | 4層以上の形状で3 pin 反例確認。事前計算検証は 2-3L のみで不十分だった |
| sortFU ソート出力は pointwise .any 等価ではない | 2L: 800 不一致, 3L: 9072 不一致 (Scratch/SortFUDeterminism.lean) |
| floatingUnits の .any メンバーシップが r180 等変 | `floatingUnit_any_in_rotate180` で証明済み |
| r180 はレイヤ不変、方角のみ NE↔SW / SE↔NW 回転 | `QuarterPos.rotate180` の定義 |
| sortFU(l1).foldl = sortFU(l2).foldl (for fU perms) | 計算検証 (23+ shapes) |
| one-way spb 順序は floatingUnits で保存 | `check_sort_invariant.lean` で violations=0 (2-layer, 3-layer) |
| mutual spb は floatingUnits で発生しない | `check_all_pairs_commute.lean` で検証済み |
| sortFU_spb_one_way_order は**一般には FALSE** | 3要素反例で確認 (check_sort_order.lean) |
| **sortFU_inversion_is_tied は一般 Perm で FALSE** | 3L 3色 8628 violations（Scratch/AllPermInvCheck.lean） |
| **h_ow 制約下では sortFU_inversion_is_tied は TRUE** | 3L 3色 全対で 0 violations。h_ow: spb(a,b)=true → a before b in both inputs |
| **l_mid/l2 の入力反転は常に tied** | 同レイヤ・別方角ペアのみスワップ。r180 はレイヤ不変 |

---

## 9. 禁止パターン（偽定理の教訓）

以下の仮定は **全て偽** と判明済み。これらに依拠するアプローチを取ってはならない。

| 偽の仮定 | なぜ偽か |
|---|---|
| `sortFU_spb_order_on_fU` | 4要素反例: [d,c,a,b] → sortFU = [b,c,d,a] (spb(a,b)=true なのに a が b の後方) |
| `sortFU_spb_one_way_order` (一般リスト版) | 3要素反例: a={(0,NE)}, b={(1,NE),(0,SE)}, x={(1,SE)} で b が a より前に来る |
| `sortFU_later_not_spb_earlier` | 同根原因（非推移的 spb サイクル） |
| sortFU が正しい topological sort を生成する | insertSorted はグリーディで後方不整合を生む |
| foldl settle が入力の置換に対して不変 | 方角列を共有するペアが結果に影響する |
| spb が floatingUnits 上で全順序 | tied ペア（双方 false）が存在する |
| BFS 列挙結果がリスト等号で r180 等変 | 探索順序が方角で変わる |
| `List.Perm.foldl_eq'` が直接適用可能 | 全ペア可換が必要だが fU は一部方角共有 |
| `floatingUnits_spb_rank` | sortFU position は入力順序依存 |
| `floatingUnits_rotate180` (list equality) | BFS order changes |
| `sortFU(fU(s).map r180)` pw `.any`-equiv `sortFU(fU(s.r180))` | 2L: 800 不一致, 3L: 9072 不一致。ソート後でも pointwise 等価にならない |
| `sortFU_inversion_is_tied` が一般 Perm で真 | 3L 3色 8628 violations（全順列）。l_mid/l2 の特定構造でのみ真。h_ow 制約下では 0 violations |
| `spb_no_chain` (spb 2段連鎖不可) | 4層 Shape `"--------:P-------:--------:P-------:--------:P-------"` で 3 pin 連鎖。pin は canFormBond=false で常に独立。計算検証が 2-3L のみで不十分だった |
| `sortFallingUnits_spb_order_preserving` | 反例2 (mixed direction) で sortFU(fus) ≠ sortFU(fus.reverse)。chain があると insertSorted の貪欲停止が順序を壊す |
| `sortFU_foldl_perm_input_eq` (一般 Perm) | 反例2 で sortFU(fus).foldl ≠ sortFU(fus.reverse).foldl。方角共有ペアの順序が影響する |

---

## 10. 次期作業計画

### Phase 0: クリーンアップ ✅ 完了（2026-04-02）
### Phase 1: settle_foldl_eq 構造構築 ✅ 完了（2026-03-25）
### Phase 2: バブルソート帰納法の本体 ✅ 完了（2026-04-01）

- foldl_eq_of_perm_tied_adj_comm (invCount 帰納法): 完成
- h_tied_comm コールバック: 完成 (S-1, S-4b に依存)
- 補助インフラ (posIn, invCount, swap系): 完成

### Phase 3: 残 sorry の解消

#### S-1: spb_no_mutual — ✅ 完了
#### S-2: insertSorted_preserves_relative_order — ✅ 完了
#### S-3: sortFU_spb_one_way_order — ❌ 偽と判明、削除済み

#### S-4b: sortFU_inversion_dir_disjoint — ✅ 完了 (2026-04-05)

`sortFU_inversion_is_tied` (S-4a) + `tied_no_shared_dir` + `fU_elem_positions_disjoint` から完全導出。
数学的洞察「tied ↔ direction-disjoint for floatingUnits」を活用。

#### S-4a: sortFU_inversion_is_tied — ✅ 完了 (2026-04-04)

S-4a の核心は `sortFallingUnits_spb_order_preserving` (L6155) に集約された:
- `foldl_insertSorted_preserves_spb_order` (L5932): foldl 中の 4-case 不変条件
- `posIn_lt_of_decomposition` (L6108): 分解 prefix ++ [a] ++ suffix からの位置比較
- `insertSorted_append_when_no_spb` (L5902): spb なし時の末尾追加
- `spb_no_chain` (L5605, S-5 sorry): 連鎖不在
証明は `spb_no_chain` (S-5) に依存する。

#### S-5: spb_no_chain — ❌ 偽と判明 (2026-04-05)

`spb_no_chain` は **FALSE** であることが判明。4層以上の形状で反例が成立。

**反例**:
- `"--------:P-------:--------:P-------:--------:P-------"` (6層, 3 floating pins at NE layers 1,3,5)
- `"--------:P-------:CrCr----:--P-----"` (4層, mixed direction chain)

**影響範囲**: S-5 に依存する以下の補題も一般 Perm に対して FALSE:
- `foldl_insertSorted_preserves_spb_order` — Case 3 が不健全
- `sortFallingUnits_spb_order_preserving` — sortFU が入力順依存
- `sortFU_inversion_is_tied` — 一般 Perm で FALSE
- `sortFU_foldl_perm_input_eq` — 一般 Perm で FALSE
- `sortFU_inversion_dir_disjoint` — 一般 Perm で FALSE (is_tied に依存)

注意: S-4a, S-4b の **証明文**は S-5 (sorry) に依存しており不健全だが、
S-4a/S-4b の**命題自体**は r180 固有の Perm では TRUE のまま。
`process_rotate180` の命題も TRUE（全反例形状で計算検証済み）。

**次セッションの修正方針**:

以下の 3 候補から選択（詳細は Section 13 参照）:

A. **r180 固有 Perm 制約で直接証明**: l_mid/l2 の入力反転が常に tied であることを直接利用。
   sortFU_inversion_is_tied を r180 特有の制約（one-way ペアが両入力で同順）で証明し直す。
   spb_no_chain と sortFallingUnits_spb_order_preserving を不要にする。

B. **bubble sort 帰納法の Case 3 修正**: spb_no_chain の代わりに
   「b 挿入時、a より後のみに spb(b,w)=true な要素がいる」ことを示す。
   同方角 chain では spb transitivity、異方角 chain では direction-disjoint 可換性を利用。

C. **全く異なる settle_foldl_eq 証明**: Phase 2 のバブルソートアプローチを廃止し、
   r180 変換の構造（同レイヤ・回転方角ペアのみスワップ）を直接利用して
   foldl 等価を証明。中間の sortFU 関連補題を全て不要にする。

---

## 11. テスト

| ファイル | 概要 |
|---|---|
| `Test/Behavior/Gravity.lean` | 落下処理の基本テスト |
| `Test/Behavior/GravityRotate180.lean` | process_rotate180 の計算検証テスト（20+ ケース） |
| `Test/Behavior/SortedPwAny.lean` | sortFU の pointwise .any 等価性チェック（21 shapes） |
| `Test/Behavior/SortFUOrder.lean` | sortFU の spb 順序保存を全排列で検証 |
| `Test/Behavior/SortFUInvariants.lean` | 2-layer/3-layer 全シェイプで構造的不変量を穷举検証 |
| `Test/Behavior/MutualSpbCheck.lean` | mutual spb 不在の穷举検証 |
| `Test/Behavior/SortFULaterNotSpb.lean` | sortFU_later_not_spb_earlier の検証 |
| `Test/Behavior/SortFUPermInvariant.lean` | sortFU(perm).foldl の全順列一致検証 |

---

## 12. 計算検証ファイル

2026-04-04 のクリーンアップにて Scratch/ 配下の全ファイル（58 件）を削除。
計算検証は全て完了しており、結果は以下の Section 8（確立済みの事実）に集約済み。

反例検証スクリプト: `Scratch/SpbNoChainCheck.lean`（2026-04-05 追加）

テストコードは `Test/Behavior/` に集約されている（Section 11 参照）。

---

## 13. 証明チェーン修正計画 (2026-04-05)

### 問題の核心

`spb_no_chain` が FALSE であるため、以下の証明チェーンが不健全:

```
process_rotate180 ← settle_foldl_eq ← sortFU_foldl_perm_input_eq (❌ 一般 Perm で FALSE)
    ├── foldl_eq_of_perm_tied_adj_comm        ✅ (コールバック前提で健全)
    ├── sortFU_inversion_dir_disjoint          ❌ (is_tied 経由で不健全)
    │     └── sortFU_inversion_is_tied         ❌ (一般 Perm で FALSE)
    │           └── sortFallingUnits_spb_order_preserving  ❌ (FALSE)
    │                 └── foldl_insertSorted_preserves_spb_order  ❌ (Case 3 不健全)
    │                       └── spb_no_chain   ❌❌ FALSE
    ├── spb_no_mutual                          ✅ (独立、健全)
    └── insertSorted_preserves_relative_order  ✅ (独立、健全)
```

ただし `process_rotate180` の **命題自体は TRUE** (全反例形状で計算検証済み)。

### 修正候補 A: r180 固有制約で sortFU_inversion_is_tied を直接証明

**アイデア**: l_mid と l2 の具体的な構造（r180 由来）を利用し、
sortFU_inversion_is_tied を一般 Perm でなく r180 固有の Perm に限定して証明。

**必要な変更**:
1. `sortFU_inversion_is_tied` の仮定に r180 固有制約を追加:
   - `h_ow`: one-way ペア (spb(a,b)=true) が両入力で同順
   - これにより入力の全反転は tied ペアのみ
2. `foldl_insertSorted_preserves_spb_order` の Case 3 を修正:
   - chain a→b→w が存在する場合でも、a が b の挿入点より前にあることを示す
   - same-direction chain: spb transitivity で spb(a,w)=true → invariant で a before w
   - different-direction chain: 要追加解析
3. `sortFU_foldl_perm_input_eq` の仮定に r180 固有制約を追加
4. `settle_foldl_eq` から上記を呼ぶ際に r180 固有制約を供給

**工数見積**: ★★★★ (Case 3 の修正が複雑)

### 修正候補 B: settle_foldl_eq の Phase 2 を部分書き換え

**アイデア**: バブルソートアプローチ (foldl_eq_of_perm_tied_adj_comm) 自体は健全。
問題は sortFU_inversion_dir_disjoint のコールバックの証明。

**必要な変更**:
1. sortFU_inversion_dir_disjoint を直接証明（is_tied 経由をスキップ）:
   - r180 由来の Perm では sortFU 出力間の全反転が direction-disjoint
   - BFS 列挙順序 + r180 変換の層不変性から直接導出
2. spb_no_chain, sortFallingUnits_spb_order_preserving, sortFU_inversion_is_tied を削除
3. settle_foldl_eq の Phase 2 は foldl_eq_of_perm_tied_adj_comm + 修正版 dir_disjoint

**工数見積**: ★★★ (dir_disjoint の直接証明が核心)

### 修正候補 C: "same-layer swap" 直接アプローチ

**アイデア**: l_mid と l2 の差分は「同レイヤ・回転方角ペアのスワップ」のみ。
これらのペアは常に direction-disjoint。sortFU を経由せず直接 foldl 等価を証明。

**必要な変更**:
1. l_mid と l2 の差分が "same-layer swap" のみであることを形式化
2. same-layer swap ペアが direction-disjoint であることを証明
3. `List.Perm` を "adjacent transposition decomposition" に分解
4. 各 transposition で foldl が不変であることを settleStep_comm_ne_dir から導出

**工数見積**: ★★★★★ (Perm の分解が技術的に複雑)

### 推奨: 候補 B

候補 B が最も有望:
- foldl_eq_of_perm_tied_adj_comm は健全で再利用可能
- spb_no_mutual, settleStep_comm_ne_dir 等の既存インフラも再利用可能
- 核心タスクは sortFU_inversion_dir_disjoint の直接証明のみ
- 既存コードの削除量が最小
- S-4a/S-4b の命題を維持しつつ証明ルートのみ変更可能