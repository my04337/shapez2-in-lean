# S2IL 補題インデックス

Lean 4 で形式化された S2IL プロジェクトの主要な定理・補題をファイル別に索引化する。

> **エージェント向けナビ**: このファイルを最初に読むことで、grep/read_file の回数を大幅に削減できる。
> - `semantic_search` はこのプロジェクトでは精度が低いため、`grep_search` を優先すること
> - ファイルの import チェーンは「依存関係マップ」セクションで確認できる

---

## 依存関係マップ（import チェーン）

```
GenericBfs.lean       (imports: なし)
ColorMixer.lean       (imports: Color)
Painter.lean          (imports: Shape)
CrystalGenerator.lean (imports: Shape)
Rotate.lean           (imports: Shape)
Rotate180Lemmas.lean  (imports: QuarterPos, Rotate, Batteries)
CrystalBond.lean      (imports: QuarterPos, Rotate, Rotate180Lemmas, Batteries, Mathlib.Finset.Image)
Gravity.lean          (imports: CrystalBond, GenericBfs, Rotate180Lemmas, Mathlib.{Perm,Nodup,TakeDrop,Finset.Image})
                      Gravity/Defs.lean                      ← 全 import
                      Gravity/Equivariance_obsolated.lean     ← imports Gravity.Defs
                      Gravity/CommExt_obsolated.lean          ← imports Equivariance_obsolated
                      Gravity/PermInvariance_obsolated.lean   ← imports CommExt_obsolated
                      Gravity/SettleFoldlEq_obsolated.lean    ← imports PermInvariance_obsolated
                      Gravity/FoldlBridge_obsolated.lean      ← imports SettleFoldlEq_obsolated
                      Gravity_obsolated.lean (facade)         ← imports SettleFoldlEq_obsolated + FoldlBridge_obsolated
                      Gravity.lean (public facade)            ← imports Gravity_obsolated
Shatter.lean          (imports: CrystalBond, Rotate, Rotate180Lemmas, Mathlib.Finset.Image)
SettledState.lean     (imports: SettledState/{Core,Paint,Crystallize,Rotate,GravityBridge})
                      SettledState/GroundedCore.lean       (imports: Gravity)
                      SettledState/GroundedInvariant.lean  (imports: Gravity)
                      SettledState/GroundedPlacement.lean  (imports: Gravity, GroundedCore, GroundedInvariant)
                      SettledState/GravityBridge.lean      (imports: Gravity, GroundedCore, GroundedInvariant, GroundedPlacement)
SettledShape.lean     (imports: SettledState, PinPusher, Stacker, Cutter, Arbitrary, Plausible)
Stacker.lean          (imports: Gravity, Shatter, SettledState, GameConfig)
Cutter.lean           (imports: Gravity, Shatter, Rotate, SettledState)
PinPusher.lean        (imports: Gravity, Shatter, Stacker, SettledState, GameConfig)
```

> **注意**: Gravity モジュールは CrystalGenerator.lean を import していない。
> crystallize 関連の証明は SettledState.lean に配置すること。

> 追記（2026-04-15）: `SettledState/GravityBridge.lean` は shallow な sibling 分割とし、
> 基盤補題を `SettledState/GroundedCore.lean` と
> `SettledState/GroundedInvariant.lean`、配置ステップ補題を
> `SettledState/GroundedPlacement.lean` に分離。

---

## Gravity モジュール（_obsolated 実体 + public facade）

> ファイル構成（旧: `S2IL/Behavior/Gravity.lean` ~7,250 行 → 分割済み）:
> - `S2IL/Behavior/Gravity/Defs.lean`（633 行）— コア定義: 構造結合, BFS, 接地, 落下単位, ソート, 着地, 配置, `process`
> - `S2IL/Behavior/Gravity/Equivariance_obsolated.lean`（~1,814 行）— rotate180/rotateCW 等変性基盤証明, FallingUnit 変換, foldl 配置等変性, ジェネリック等変性補題（structuralCluster_σ, groundedPositions_σ 等）
> - `S2IL/Behavior/Gravity/CommExt_obsolated.lean`（1,978 行）— 配置可換性・拡張性基盤: placeQuarter/settleStep 可換性, shouldProcessBefore/sortFallingUnits 拡張性
> - `S2IL/Behavior/Gravity/PermInvariance_obsolated.lean`（~2,304 行）— floatingUnits 素性, バブルソート帰納法, shouldProcessBefore_no_mutual, settle_foldl_eq
> - `S2IL/Behavior/Gravity/SettleFoldlEq_obsolated.lean`（facade）— `PermInvariance_obsolated` の再エクスポート
> - `S2IL/Behavior/Gravity/FoldlBridge_obsolated.lean`（355 行）— sort-foldl bridge と mapped-perm 可換性補題
> - `S2IL/Behavior/Gravity_obsolated.lean`（707 行, facade）— Bridge 補題, process_rotate180/rotateCW, Shape 公開 API（実体）
> - `S2IL/Behavior/Gravity.lean`（public facade）— `Gravity_obsolated` への公開 import ラッパー
>
> ビルド状態: errors = 0, sorries = 0, warnings = 0

### ファイル構造マップ（主要ファイル別）

#### Gravity/Defs.lean（633 行）— コア定義

| 行範囲 | セクション | 主要な定義・定理 | 状態 |
|---|---|---|---|
| L1–48 | ヘッダ・import | SPDX, namespace Gravity, doc comment | ✅ |
| L49–85 | 構造結合 | `isStructurallyBonded`, `isStructurallyBonded_symm` | ✅ |
| L86–147 | BFS・孤立ピン | `structuralBfs`, `structuralClusterList`, `allIsolatedPins` | ✅ |
| L148–195 | 接地接触・接地 BFS | `isGroundingContact`, `groundingBfs`, `groundedPositionsList` | ⚠️ バグ（§注記参照） |
| L198–250 | 落下単位 | `FallingUnit`, `positions`, `minLayer`, `floatingUnits` | ✅ |
| L251–285 | ソート（spb） | `shouldProcessBefore`, `insertSorted`, `sortFallingUnits` | ✅ |
| L286–557 | 決定性ソート | `fallingUnitLe`, `fallingUnitOrd`, `listNatLe`, `canonicalKey`, `sortFallingUnits'` | ✅ |
| L558–612 | 着地・配置 | `isOccupied`, `landingDistance`, `placeQuarter`, `placeFallingUnit` | ✅ |
| L614–633 | process | `process`（normalize → sort → foldl → return） | ✅ |

#### Gravity/Equivariance_obsolated.lean（~1,814 行）— 等変性基盤

| 行範囲 | セクション | 主要な定理 | 状態 |
|---|---|---|---|
| L1–19 | ヘッダ・import | imports `Gravity.Defs` | ✅ |
| L20–44 | r180 基盤 | `isStructurallyBonded_rotate180`(L21), `isGroundingContact_rotate180`(L31) | ✅ |
| L46–180 | BFS 等変性 | `structuralBfs_rotate180`(L76), `groundingBfs_rotate180`, clusterList/positionsList マップ | ✅ |
| L182–240 | Shape 構成・FU 変換 | `ofLayers_rotate180`, `FallingUnit.rotate180`, `minLayer_rotate180` | ✅ |
| L242–508 | spb/sortFallingUnits 等変性 | `shouldProcessBefore_rotate180`, `sortFallingUnits'_rotate180`, BFS ↔ Generic | ✅ |
| L510–751 | BFS 健全性・完全性 | `groundedPositionsList_sound/complete`, `any_beq_iff_mem` | ✅ |
| L791–923 | Finset 等変性 | `structuralCluster_rotate180`, `groundedPositions_rotate180` | ✅ |
| L872–1100 | σ ジェネリック等変性 | `structuralCluster_σ`(L872), `groundedPositions_σ`(L995), `floatingUnits_isEmpty_σ`(L1079)。r180/rCW は薄ラッパー | ✅ |
| L925–1155 | グラフ補題・非空性基盤 | `genericReachable_*`, `groundedPositionsList_inv` | ✅ |
| L1279–1475 | floatingUnits 等変性 | `floatingUnits_isEmpty_rotate180`(L1438) | ✅ |
| L1458–1645 | rotateCW 等変性 | `isGroundingContact_rotateCW`(L1458) → `floatingUnits_isEmpty_rotateCW`(L1628) | ✅ |
| L1646–1801 | 着地・配置 等変性 | `isOccupied_rotate180`(L1646), `landingDistance_rotate180`(L1689), `foldl_place_rotate180`(L1784) | ✅ |

#### Gravity/CommExt_obsolated.lean（1,978 行）— 配置可換性・拡張性基盤

| 行範囲 | セクション | 主要な定理 | 状態 |
|---|---|---|---|
| L1–9 | ヘッダ・import | imports `Gravity.Equivariance_obsolated` | ✅ |
| L15–277 | 浮遊位置・リスト等価ヘルパー | `falling_positions_any_rotate180`, `any_map_rotate180_beq`, `foldl_min_*` | ✅ |
| L287–799 | FU 拡張性・placeQuarter | `minLayer_ext`, `landingDistance_ext`, `placeQuarter_comm_*`, `placeFallingUnit_ext` | ✅ |
| L806–1055 | 着地距離・配置保存 | `landingDistance_ge_one`, `landingDistance_landed`, `foldl_placeQuarter_getDir_preserved` | ✅ |
| L1071–1332 | settleStep 可換性（方角素） | `settleStep_comm_ne_dir`（方角素ペアの foldl 可換） | ✅ |
| L1356–1549 | 層素性・spb 拡張性 | `landingDistance_placeFU_gap`, `placeFallingUnit_comm_of_layer_disjoint`, `settleStep_comm_dir_gap` | ✅ |
| L1600–1865 | minLayerAtDir・shouldProcessBefore_ext | `foldMinOption`, `minLayerAtDir_*`, `shouldProcessBefore_ext` | ✅ |
| L1877–1978 | sortFallingUnits 拡張性 | `sortFallingUnits_pointwise_ext` | ✅ |

#### Gravity/PermInvariance_obsolated.lean（2,304 行）— settle_foldl_eq 証明

| 行範囲 | セクション | 主要な定理 | 状態 |
|---|---|---|---|
| L1–9 | ヘッダ・import | imports `Gravity.CommExt_obsolated` | ✅ |
| L16–150 | floatingUnits 素性（NoDup） | `allValid_nodup`, `floatingUnits_nodup`, `floatingUnits_pairwise_disjoint` | ✅ |
| L280–380 | floatingUnits r180 対応 | `map_rotate180_pairwise_disjoint`, `foldl_settle_swap_at`, `floatingUnit_any_in_rotate180` | ✅ |
| L520–560 | floatingUnits 非空性・反対称性 | `floatingUnit_positions_nonempty`, `fallingUnitOrd_antisymm_of_floatingUnits_impl` | ✅ |
| L600–780 | 置換・反転数基盤 | `posIn`, `invCount`, `posIn_injective`, `foldl_cond_add_*` | ✅ |
| L795–1030 | FoldL 単調性・反転検出 | `invCount_zero_imp_eq`, `exists_inv_of_invCount_pos`, `exists_adj_inv_of_exists_inv` | ✅ |
| L1060–1450 | Swap σ 操作・invCount 減少 | `swapIndex`, `pairsList`, `invCount_adj_swap_lt`, `exists_adj_inv_swap` | ✅ |
| L1480–1870 | グラフ到達可能性・spb 相互排除 | `cluster_positions_one_side`, `shouldProcessBefore_no_mutual` | ✅ |
| L1880–1978 | insertSorted 分解表現 | `insertSorted_before_shouldProcessBefore`, `insertSorted_preserves_relative_order` | ✅ |
| L2000–2304 | settle_foldl_eq 統合 | `posIn_lt_of_decomposition`, `settle_foldl_eq`（Phase 1 + Phase 2） | ✅ |

#### Gravity_obsolated.lean facade（707 行）— Bridge + 公開 API

| 行範囲 | セクション | 主要な定理 | 状態 |
|---|---|---|---|
| L1–20 | ヘッダ・import | imports `Gravity.SettleFoldlEq_obsolated` + `Gravity.FoldlBridge_obsolated` | ✅ |
| L122–188 | **Perm Bridge（汎用）** | `sort_foldl_map_perm_bridge`（≤5L、LayerPerm-generic） | ✅ |
| L189–712 | **process_rotate180** と関連補題 | `process_rotate180`(L189), `settleStep_comm_mapped_perm`（h_comm 汎用版） | ✅ |
| ~L713–1100 | rotateCW セクション | rotateCW 方向変換補題, 着地・配置等変性 | ✅ |
| ~L1101 | process_rotateCW | `settleStep_comm_mapped_perm` 呼び出しで h_comm 統合済み | ✅ |
| ~L1321–1376 | Shape 公開 API | `gravity_rotate180_comm`(~L1332), `gravity_rotateCW_comm`(~L1337), `IsSettled_rotate180`(~L1365) | ✅ |

> ✅ Bridge 補題を汎用化 (Phase F, 2026-04-14):
> - `sort_foldl_map_perm_bridge`: LayerPerm-generic 版。r180/rCW 個別版を統合（-36行）
> - `settleStep_comm_mapped_perm`: h_comm ブロックを LayerPerm-generic 版に統合（-163行）
> - `LayerPerm.onDir_injective` (Rotate180Lemmas.lean): Direction 変換の単射性
>
> **残存 sorry 0 件（axiom 2 件に切り替え: Plan B-1, 2026-04-14）**:
> - `all_grounded_settle_foldl` (SettledState.lean): `private axiom` 化（pin NE 着地時の ImmBelow 供給。Plan B-3 で構成的証明に置換予定）
> - `gravity_IsSettled` (SettledState.lean): `axiom` 化（≤5L での 1.9M+ shapes 計算検証済み）
> - `process_rotate180_placeAbove_settled` (Stacker.lean): `axiom` 化（166,757+ shapes 計算検証済み）
>
> **重大発見 (Wave 7)**: `process_rotate180` は ≥6L で偽（6L反例確認済み）。
> 全証明チェーンに `layerCount ≤ 5` 仮説を追加済み。
> 計算検証: ≤5L で TRUE 確認済み（1.9M+ shapes, 0 failures + CW 65K shapes, 0 failures）。
>
> **Wave 7 変更点**: `sortFallingUnits_output_inversion_dir_disjoint_r180/rCW`（偽定理）を削除。
> `sort_foldl_map_perm_bridge`（汎用版）に集約。
> `layerCount ≤ 5` 仮説を bridge → process → gravity_comm → cut/pinPush/stack の全チェーンに伝播。
>
> **Wave 6 変更点**: `process` は `sortFallingUnits'`（`List.mergeSort fallingUnitOrd`）を使用するよう変更。
> `fallingUnitOrd` は `(minLayer, canonicalKey)` で全順序を定義。
> 旧 `sortFallingUnits_rotate180`, `sorted_foldl_pointwise_eq`, `settle_flatMap_any_eq` は削除済み。

### 主要定理・補題一覧（可視性付き）

> **注意**: 以下の行番号は分割前のモノリス `Gravity.lean` に基づく参照値。
> 正確な行番号は各分割ファイルの「ファイル構造マップ」を参照するか、`grep_search` で定理名を検索すること。

#### 公開 (public) 定理

| 定理 | ファイル | 状態 | 概要 |
|---|---|---|---|
| `isStructurallyBonded_symm` | Defs | ✅ | 構造結合は対称 |
| `isStructurallyBonded_rotate180` | Equivariance | ✅ | 構造結合は r180 で等変 |
| `isGroundingContact_rotate180` | Equivariance | ✅ | 接地接触は r180 で等変 |
| `structuralBfs_eq_generic` | Equivariance | ✅ | 構造 BFS = 汎用 BFS |
| `groundingBfs_eq_generic` | Equivariance | ✅ | 接地 BFS = 汎用 BFS |
| `allValid_any_iff_layer'` | Equivariance | ✅ | allValid メンバーシップ ↔ layer < layerCount |
| `isGroundingContact_valid` | Equivariance | ✅ | 接地接触 → q.layer < layerCount |
| `isGroundingContact_valid_fst` | Equivariance | ✅ | 接地接触 → p.layer < layerCount |
| `groundedPositionsList_sound` | Equivariance | ✅ | BFS 結果 → 有効 seed から到達可能 |
| `groundedPositionsList_complete` | Equivariance | ✅ | 有効 seed から到達可能 → BFS 結果に含まれる |
| `any_beq_iff_mem` | Equivariance | ✅ | `.any (· == p)` ↔ `p ∈ l` |
| `structuralCluster_rotate180` | Equivariance | ✅ | 構造クラスタは r180 で等変 |
| `groundedPositions_rotate180` | Equivariance | ✅ | 接地位置集合は r180 で等変 |
| `ungrounded_nonempty_implies_floatingUnits_nonempty` | Equivariance | ✅ | 非接地非空位置 → floatingUnits 非空 |
| `floatingUnits_nonempty_implies_exists_ungrounded` | Equivariance | ✅ | floatingUnits 非空 → 非接地非空位置が存在 |
| `floatingUnits_isEmpty_rotate180` | Equivariance | ✅ | floatingUnits.isEmpty は r180 で不変 |
| `isGroundingContact_rotateCW` | Equivariance | ✅ | 接地接触は rotateCW で等変 |
| `groundedPositions_rotateCW` | Equivariance | ✅ | 接地位置集合は rotateCW で等変 |
| `floatingUnits_isEmpty_rotateCW` | Equivariance | ✅ | floatingUnits.isEmpty は rotateCW で不変 |
| `falling_positions_any_rotate180` | CommExt | ✅ | 浮遊位置 .any は r180 で等変 |
| `fallingUnitLe_total` | Defs | ✅ | fallingUnitLe は全前順序（a ≤ b ∨ b ≤ a） |
| `fallingUnitLe_trans` | Defs | ✅ | fallingUnitLe は推移的 |
| `any_map_rotate180_beq` | CommExt | ✅ | map r180 の .any 等変 |
| `process_rotate180` | Facade | ✅ | `(process s).map r180 = process s.r180`（Wave 9 で sorry 解消） |
| `gravity_rotate180_comm` | Facade | ✅ | process_rotate180 のラッパー |
| `process_rotateCW` | Facade | ✅ | `(process s).map rCW = process s.rCW`（Wave 9 で sorry 解消） |
| `gravity_rotateCW_comm` | Facade | ✅ | process_rotateCW のラッパー |
| `IsSettled_iff_isSettled` | Facade | ✅ | Prop ↔ Bool 変換 |
| `IsSettled_rotate180` | Facade | ✅ | 安定状態は r180 で保存 |

#### 注目すべき private 定理（外部利用時は public 化が必要）

| 定理 | ファイル | 概要 |
|---|---|---|
| `shouldProcessBefore_rotate180` | Equivariance | spb は r180 で等変 |
| ~~`sortFallingUnits_rotate180`~~ | — | **Wave 6 で削除**。後継: `sortFallingUnits'_rotate180` |
| `sortFallingUnits'_rotate180` | Equivariance | sortFallingUnits' は r180 で等変（`List.map_mergeSort` + `minLayer_rotate180`） |
| `mem_groundedPositions_rotate180` | Equivariance | 接地メンバーシップの r180 保存 |
| `mem_groundedPositions_rotateCW` | Equivariance | 接地メンバーシップの rotateCW 保存 |
| `settleStep_comm_ne_dir` | CommExt | 方角素ペアの settleStep 可換性 |
| `foldl_eq_of_perm_tied_adj_comm` | PermInvariance | バブルソート帰納法の本体 |
| `shouldProcessBefore_no_mutual` | PermInvariance | S-1: spb 相互不在 |
| ~~`sortFallingUnits'_pointwise_ext`~~ | — | **削除**。`settle_foldl_eq` Phase 1 に `List.map_mergeSort` で吸収 |
| ~~`sortFallingUnits_output_inversion_dir_disjoint_r180`~~ | — | **Wave 7 で削除**（偽定理）。bridge 補題に集約 |

#### ユーティリティ補題（ヘルパー追加前に重複チェック用）

ヘルパーを追加する前に、以下の既存補題と重複しないか確認すること。

> `grep_search` で補題名を検索することを推奨。

| 補題 | ファイル | 概要 |
|---|---|---|
| `QuarterPos.rotate180_layer` | Equivariance | r180 は layer を保持 |
| `QuarterPos.rotate180_dir` | Equivariance | r180 の dir は `dir.rotate180` |
| `foldl_map_layer` | Equivariance | `(l.map r180).foldl min = l.foldl min` |
| `FallingUnit.minLayer_rotate180` | Equivariance | minLayer は r180 で不変 |
| `foldl_min_le_init` | CommExt | foldl min の結果 ≤ 初期値 |
| `foldl_min_le_elem` | CommExt | foldl min の結果 ≤ リスト要素の layer |
| `foldl_min_le_mem` | CommExt | cons リストの foldl min ≤ 任意メンバの layer |
| `foldl_min_attained` | CommExt | foldl min は初期値またはメンバの layer |
| `mem_of_any_beq_eq` | CommExt | .any BEq 等価 → メンバーシップ逆転 |
| `minLayer_ext` | CommExt | .any BEq 等価な FU は同minLayer |
| `landingDistance_ext` | CommExt | .any 等価な FU は同landingDistance |
| `setDir_setDir_comm` | CommExt | setDir は異方角で可換 |
| `placeQuarter_length` | CommExt | placeQuarter は長さ保存 |
| `placeQuarter_comm_layer_ne` | CommExt | placeQuarter は異レイヤで可換 |
| `placeQuarter_comm_dir_ne` | CommExt | placeQuarter は同レイヤ・異方角で可換 |
| `placeFallingUnit_ext` | CommExt | .any 等価な FU は同じ placeFallingUnit 結果 |
| `landingDistance_check_ge_one` | CommExt | d ≥ 1 → maxDrop ≥ 1 → check 結果 ≥ 1 |
| `landingDistance_ge_one` | CommExt | minLayer ≥ 1 → 着地距離 ≥ 1 |
| `minLayer_witness` | CommExt | FU.positions 内に minLayer と等しい layer の要素が存在 |
| `any_landed_of_le` | CommExt | p.layer ≤ d なら floor contact で landed 成立（private） |
| `landingDistance_check_landed` | CommExt | check 再帰の返り値 d で landed=true |
| `landingDistance_landed` | CommExt | landingDistance の返り値で floor/obstacle contact が成立 |
| `landingDistance_check_not_landed_before` | CommExt | result より前の全 d' で着地条件が不成立 |
| `landingDistance_not_occupied_at_landing` | CommExt | d≥2 の場合、全着地位置が obstacle で未占有（no-overwrite 基盤） |
| `foldl_placeQuarter_getDir_preserved` | CommExt | placeFallingUnit が非着地位置の getDir を保存 |
| `isOccupied_placeQuarter_ne_layer` | CommExt | 異レイヤの placeQuarter が isOccupied 保存 |
| `isOccupied_placeFU_of_ne` | CommExt | 異 FU 配置が isOccupied 保存 |
| `landed_placeFU_of_ne` | CommExt | 異 FU 配置が landed チェック保存（floor contact 含む） |
| `landingDistance_placeFU_gap` | CommExt | gap ≥ 2 での着地距離独立性（minLayer 場合分け） |
| `placeFallingUnit_comm_of_layer_disjoint` | CommExt | レイヤ素 FU の foldl 可換性 |
| `settleStep_comm_dir_gap` | CommExt | settle step 可換性（same-minLayer + gap ≥ 2） |
| `floatingUnits_pairwise_disjoint` | PermInvariance | floatingUnits の位置集合は pairwise disjoint |
| `floatingUnits_nodup` | PermInvariance | floatingUnits は重複なし |
| `shouldProcessBefore_no_mutual` | PermInvariance | spb 相互不在（DAG 性） |

#### 確立済みの事実

| 事実 | 根拠 |
|---|---|
| `process_rotate180` は真 | 1L-3L 全数検証（531,441 shapes）+ 4L 全数検証（1,392,640 shapes）+ 構造的カバレッジ（24 shapes）+ 5L-16L ランダムサンプリング（18,700 shapes）= **合計 1,949,447 shapes で 0 failures** |
| spb は floatingUnits 上で DAG（2-cycle 禁止） | 計算検証 + `shouldProcessBefore_no_mutual` 証明済み |
| 方角素ペアは foldl で可換 | `settleStep_comm_ne_dir` 証明済み |
| tied ↔ direction-disjoint (floatingUnits 上) | 共有方角 → minLayer 差 → one-way → 対偶 |
| r180 はレイヤ不変、方角のみ NE↔SW / SE↔NW | `QuarterPos.rotate180` の定義 |
| spb(a,b) = spb(a.r180, b.r180) | r180 のレイヤ不変性から直接 |
| sortFallingUnits(l1).foldl = sortFallingUnits(l2).foldl (floatingUnits perms) for r180 | 計算検証 (1.9M+ shapes, 0 failures) |
| `shouldProcessBefore_no_chain` は FALSE | 4L 反例: 3 pins in same column (削除済み。証明チェーン不使用) |
| `sortFallingUnits_spb_order_preserving` は一般 FU で FALSE | 3 要素干渉パターン: chains a→b→c (削除済み。証明チェーン不使用) |
| `sortFallingUnits_inversion_is_tied` は一般 FU で FALSE | one-way pairs can be inverted in sortFallingUnits output (削除済み。証明チェーン不使用) |

### テストファイル一覧

| ファイル | 概要 |
|---|---|
| `Test/Behavior/Gravity.lean` | 落下処理の基本テスト |
| `Test/Behavior/GravityRotate180.lean` | process_rotate180 の計算検証テスト（20+ ケース） |
| `Verification/Gravity/ProcessRotate180Check4L.lean` | 1L-4L 全数検証（1,930,747 shapes、構造的カバレッジ含む） |
| `Verification/Gravity/ProcessRotate180Random.lean` | 5L-16L ランダムサンプリング検証（18,700 shapes） |
| `Test/Behavior/SortedPwAny.lean` | sortFallingUnits の pointwise .any 等価性チェック（21 shapes） |
| `Test/Behavior/SortFUOrder.lean` | sortFallingUnits の spb 順序保存を全排列で検証 |
| `Test/Behavior/SortFUInvariants.lean` | 2-layer/3-layer 全シェイプで構造的不変量を全数検証 |
| `Test/Behavior/MutualSpbCheck.lean` | mutual spb 不在の全数検証 |
| `Test/Behavior/SortFULaterNotSpb.lean` | sortFallingUnits_later_not_spb_earlier の検証 |
| `Test/Behavior/SortFUPermInvariant.lean` | sortFallingUnits(perm).foldl の全順列一致検証 |
| `Test/Behavior/SortFUPwAnyEq.lean` | sortFallingUnits の pointwise .any 等価性チェック |

---

## SettledState.lean

> ファイル: `S2IL/Behavior/SettledState.lean`

| 補題 | 状態 | 概要 |
|---|---|---|
| `floatingUnits_paint_eq` | ✅ | Paint は floatingUnits を保存 |
| `floatingUnits_crystallize_eq` | ✅ | Crystallize 後は floatingUnits が空 |
| `IsSettled_paint` | ✅ | Paint は安定状態を保存 |
| `IsSettled_crystallize` | ✅ | Crystallize は安定状態を保存（入力に関わらず） |
| `IsSettled_rotateCW` | ✅ | RotateCW は安定状態を保存 |
| `gravity_IsSettled` | ⚙️ axiom | 落下処理出力は安定状態（**`s.layerCount ≤ 5` 仮説付き**）。≤5L: 1.9M+ shapes 計算検証済み。Plan B-1 (2026-04-14) で axiom 化。Plan B-3 で構成的証明に置換予定 |
| `floatingUnits_nil_of_normalize` | ✅（private） | normalize は floatingUnits = [] を保存。Case 1 から独立補題として抽出 |
| `groundedPositions_mono` | ✅（private） | 非空象限保存で groundedPositions は単調 |
| `obstacle_all_grounded` | ✅（private） | clearPositions 後の全非空位置が接地 |
| `perm_flatMap_of_perm` | ✅（private） | List.Perm から flatMap Perm を帰納法で導出 |
| `AllNonEmptyGrounded` | def | ofLayers 上の全非空位置が接地している述語 |
| `ImmBelow` | def（private） | 垂直チェーン完備性。∀ (l,d) 非空 → l=0 ∨ (l-1,d) 非空 |
| `vertical_grounding_contact` | ✅（private） | 同方角・垂直隣接・両非空 → isGroundingContact |
| `getDir_nonempty_implies_getQuarter` | ✅（private） | getDir 非空 → getQuarter s が some q を返す（Shape 変換） |
| `immBelow_column_filled` | ✅（private） | ImmBelow → layers 0..l が全て非空（降下帰納法） |
| `immBelow_implies_allNonEmptyGrounded` | ✅（private） | ImmBelow → AllNonEmptyGrounded（垂直チェーン→GenericReachable）|
| `foldl_grounded_induction` | ✅（private） | base + step → foldl 全体の接地不変量（リスト帰納法） |
| `foldl_grounded_induction_with_inv` | ✅（private） | foldl_grounded_induction の拡張版。追加不変量 P を foldl 全体で追跡 |
| `foldl_grounded_induction_prefix` | ✅（private） | prefix 構造付き foldl 帰納法。step 関数に done/u/rest/h_eq を提供 |
| `one_step_all_grounded` | ✅ | 1 FU 配置で接地不変量保存（h_empty_landing 仮説付き）。pin/cluster 両ケース完全証明済み (Wave 18-19) |
| `all_grounded_settle_foldl` | ⚙️ axiom | foldl_grounded_induction_prefix で構成していたが、pin 非空着地の ImmBelow 供給が未証明。Plan B-1 (2026-04-14) で `private axiom` 化。Plan B-3 で構成的証明に置換予定 |
| `placeFallingUnit_ne_mono` | ✅（private） | placeFallingUnit は非空位置の非空性を保存（FU 着地位置以外の getDir 変化なし） |
| `pin_ne_landing_dist_eq_one` | ✅（private） | pin NE 着地時に landingDistance = 1（d>1 なら d-1 で isOccupied 矛盾）|
| `placeQuarter_length_ge` | ✅（private） | placeQuarter はリストの長さを減らさない |
| `placeFallingUnit_length_ge` | ✅（private） | placeFallingUnit はリストの長さを減らさない |
| `below_grounded_implies_grounded` | ✅（private） | 非接地+非空の位置の直下は接地+非空でない |
| `floatingUnits_minLayer_ge_one` | ✅（private） | 浮遊 FU の minLayer ≥ 1（L0 非空は常に接地） |
| `h_empty_landing_case_d_eq_one` | ~~🔲 sorry~~ | ✅ Wave 19 で削除。一般 obs で偽のため廃止。`one_step_all_grounded_cluster` に統合 |
| `one_step_all_grounded_cluster` | ✅ | cluster FU 配置の接地不変量保存。d≥2 ✅、d≤1 ✅ Wave 21（edge mono + cluster connectivity） |
| `one_step_all_grounded_pin` | ✅ | pin FU 配置の全非空接地不変量保存。空着地 ✅、非空着地 ✅（ImmBelow 仮説 `h_ib_ne` 付き。内部で ImmBelow → pin 保存 → immBelow_implies_allNonEmptyGrounded で証明）|

---

## SettledShape.lean

> ファイル: `S2IL/Behavior/SettledShape.lean`（imports: SettledState, Arbitrary, Plausible）

SettledState.lean の IsSettled 保存定理を利用して `SettledShape` 上の操作を定義し、
Plausible 用の Arbitrary / SampleableExt インスタンスを提供する。

| 定義 / 補題 | 状態 | 概要 |
|---|---|---|
| `paint` | ✅ | `SettledShape → Color → SettledShape`（`IsSettled_paint` 利用） |
| `crystallize` | ✅ | `Shape → Color → SettledShape`（`IsSettled_crystallize` 利用） |
| `rotateCW` | ✅ | `SettledShape → SettledShape`（`IsSettled_rotateCW` 利用） |
| `rotateCCW` | ✅ | `SettledShape → SettledShape`（`IsSettled_rotateCCW` 利用） |
| `gravity` | ✅ | `Shape → (h_lc) → Option SettledShape`（`gravity_IsSettled` axiom 利用） |
| `pinPush` | ✅ | `SettledShape → GameConfig → (h) → Option SettledShape`（`IsSettled_pinPush` 利用） |
| `stack` | ✅ | `SettledShape → SettledShape → GameConfig → (h) → Option SettledShape`（`IsSettled_stack` 利用） |
| `cut` | ✅ | `Shape → (h_lc) → Option SettledShape × Option SettledShape`（`IsSettled_cut_*` 利用） |
| `halfDestroy` | ✅ | `Shape → (h_lc) → Option SettledShape`（`IsSettled_halfDestroy` 利用） |
| `eq_of_val_eq` | ✅ | 値が等しければ SettledShape も等しい |
| `val_eq_of_eq` | ✅ | SettledShape が等しければ値も等しい |
| `Decidable IsSettled` | ✅ | IsSettled の決定可能性インスタンス |
| `BEq SettledShape` | ✅ | 内部 Shape での等値判定 |
| `Repr SettledShape` | ✅ | 表示用インスタンス |
| `Arbitrary SettledShape` | ✅ | Plausible 用ランダム生成（gravity 適用で安定化） |
| `SampleableExt SettledShape` | ✅ | Plausible 用サンプリング |

### 未定義

| 操作 | 必要な保存定理 | 状態 |
|---|---|---|
| `swap` | `IsSettled_swap` | 未実装（`IsSettled_normalize` 依存） |

### Gravity モジュール: rotateCW 等変性チェーン（Equivariance.lean + Facade）

| 補題 | 状態 | 概要 |
|---|---|---|
| `isGroundingContact_rotateCW` | ✅ | 接地接触は rotateCW で等変 |
| `groundingBfs_rotateCW` | ✅ | BFS は rotateCW で等変 |
| `groundedPositions_rotateCW` | ✅ | 接地位置集合は rotateCW で等変 |
| `floatingUnits_isEmpty_rotateCW` | ✅ | floatingUnits.isEmpty は rotateCW で不変 |

---

## Rotate180Lemmas.lean

> ファイル: `S2IL/Behavior/Rotate180Lemmas.lean`

（Wave 5 完了後に索引化予定）

---

## CrystalBond.lean / Shatter.lean

> BFS 等変性・砕け散り等変性

### CrystalBond.lean rotateCW 等変性

| 定理 | 状態 | 概要 |
|---|---|---|
| `isBondedInLayer_rotateCW` | ✅ | isBondedInLayer は rCW で不変 |
| `isBondedCrossLayer_rotateCW` | ✅ | isBondedCrossLayer は rCW で不変 |
| `isBonded_rotateCW` | ✅ | isBonded は rCW で不変 |
| `allValid_rotateCW` | ✅ | allValid は rCW で不変 |
| `cluster_rotateCW` | ✅ | cluster の rCW 等変性（Finset.image 形式） |
| `allValid_any_rotateCW` | ✅ | allValid の any メンバーシップは rCW で不変 |
| `allValid_any_rotateCCW` | ✅ | allValid の any メンバーシップは rCCW で不変 |

### Shatter.lean rotateCW 等変性

| 定理 | 状態 | 概要 |
|---|---|---|
| `shatterOnFall_rotateCW_comm` | ✅ | 落下砕け散りと rCW は可換 |
| `shatterOnTruncate_rotateCW` | ✅ | shatterOnTruncate は rCW と可換 |

---

## Cutter.lean

> ファイル: `S2IL/Behavior/Cutter.lean`（imports: Gravity, Shatter, Rotate, SettledState）

### IsSettled 保存定理

| 定理 | 状態 | 概要 |
|---|---|---|
| `IsSettled_settleAfterCut` | ✅ | settleAfterCut の出力は安定状態（全パスが gravity 経由） |
| `IsSettled_halfDestroy` | ✅ | halfDestroy の出力は安定状態 |
| `IsSettled_cut_east` | ✅ | cut の東側出力は安定状態 |
| `IsSettled_cut_west` | ✅ | cut の西側出力は安定状態 |

> `IsSettled_swap` は `IsSettled_normalize` 追加後に実装予定（combineHalves → normalize パス）

---

## PinPusher.lean

> ファイル: `S2IL/Behavior/PinPusher.lean`（imports: Gravity, Shatter, Stacker, SettledState, GameConfig）

### IsSettled 保存定理

| 定理 | 状態 | 概要 |
|---|---|---|
| `IsSettled_liftUp_generatePins` | ⚙️ axiom（private） | settled 入力の liftUp+generatePins は settled |
| `gravity_eq_normalize_of_settled` | ✅（private） | settled なシェイプでは gravity = normalize |
| `IsSettled_pinPush` | ✅ | pinPush の出力は安定状態（`h_settled` 仮説付き） |

### rotateCW 等変性

| 定理 | 状態 | 概要 |
|---|---|---|
| `liftUp_rotateCW` | ✅ | liftUp は rCW と可換 |
| `generatePins_rotateCW` | ✅ | generatePins は rCW と可換 |
| `pinPush_rotateCW_comm` | ✅ | pinPush は rCW と可換（≤5L） |

---

## Stacker.lean

> ファイル: `S2IL/Behavior/Stacker.lean`（imports: Gravity, Shatter, SettledState, GameConfig）

### IsSettled 保存定理

| 定理 | 状態 | 概要 |
|---|---|---|
| `IsSettled_stack` | ✅ | stack の出力は安定状態（全パスが gravity 経由） |

### rotateCW 等変性

| 定理 | 状態 | 概要 |
|---|---|---|
| `truncate_rotateCW` | ✅ | truncate は rCW と可換 |

---

## Behavior 操作: 回転等変性一覧

> 各 Behavior ファイル（Painter, CrystalGenerator, Cutter, PinPusher, Stacker）の回転等変性定理を集約。
> 詳細計画: [`gravity-proof-execution-plan.md`](../plans/gravity-proof-execution-plan.md) §3

### Painter.lean

| 定理 | r180 | rCW | rCCW |
|---|---|---|---|
| `paintLayer_rotate180` / `_rotateCW` | ✅ | ✅ | （Layer 単体は CW で十分） |
| `paint_rotate180_comm` | ✅ コロラリー化済 | — | — |
| `paint_rotateCW_comm` | — | ✅ | — |
| `paint_rotateCCW_comm` | — | — | ✅ |

### CrystalGenerator.lean

| 定理 | r180 | rCW | rCCW |
|---|---|---|---|
| `fillLayer_rotate180` / `_rotateCW` | ✅ | ✅ | （Layer 単体は CW で十分） |
| `crystallize_rotate180_comm` | ✅ コロラリー化済 | — | — |
| `crystallize_rotateCW_comm` | — | ✅ | — |
| `crystallize_rotateCCW_comm` | — | — | ✅ |

### Rotate.lean（Shape レベル等式）

| 定理 | 状態 | 概要 |
|---|---|---|
| `rotateCCW_eq_rotateCW_rotateCW_rotateCW` | ✅ | s.rCCW = s.rCW³ |
| `rotate180_eq_rotateCW_rotateCW` | ✅ | s.r180 = s.rCW² |

### Machine.lean（Option ラッパー）

着色・回転・結晶化は `Option Shape.SettledShape` ベースに移行済み（2026-04-13）。
pinPush/stack/halfDestroy/cut/swap は `Option Shape` のまま（テスト互換性のため）。
swap のみ `IsSettled_normalize` 追加後に SettledShape 化予定。

| 関数 / 定理 | 入力型 | 出力型 | 等変性定理 |
|---|---|---|---|
| `Machine.paint` | `Option SettledShape` | `Option SettledShape` | `paint_*_comm` ✅ (r180/rCW/rCCW) |
| `Machine.crystallize` | `Option Shape` | `Option SettledShape` | `crystallize_*_comm` ✅ |
| `Machine.rotateCW` | `Option SettledShape` | `Option SettledShape` | — |
| `Machine.rotateCCW` | `Option SettledShape` | `Option SettledShape` | — |
| `Machine.rotate180` | `Option SettledShape` | `Option SettledShape` | — |
| `Machine.pinPush` | `Option Shape` | `Option Shape` | 🔲（未移行） |
| `Machine.stack` | `Option Shape × Option Shape` | `Option Shape` | 🔲（未移行） |
| `Machine.halfDestroy` | `Option Shape` | `Option Shape` | 🔲（未移行） |
| `Machine.cut` | `Option Shape` | `Option Shape × Option Shape` | 🔲（未移行） |
| `Machine.swap` | `Option Shape × Option Shape` | `Option Shape × Option Shape` | 🔲（未移行） |
| `Machine.mixColor` | `Option Color × Option Color` | `Option Color` | 変更予定なし |

### 非等変操作（rCW）

| 操作 | 理由 |
|---|---|
| `cut` / `halfDestroy` / `swap` | `shatterOnCut` が E-W 軸固有（`isEast`/`isWest` プレディケート）。rCW で軸回転するため非等変 |

---

## 既知の問題

### isGroundingContact 双方向性バグ（2026-04-12 発見、2026-04-13 ゲーム検証完了）

`Defs.lean` の `isGroundingContact` は垂直接触を双方向（対称）に定義しているが、接地パスとして物理的に正しいのは**上方向のみ**（`to.layer = from.layer + 1`）。BFS が下方向の垂直接触を辿ることで、本来浮遊すべきピンが接地済みと誤判定される。

- **検証済み反例**: `Rr------:RrP-----:RrRr----` (S1) → L1:SE(P) が誤って接地と判定（ゲーム実機ではピンが落下）
- **旧反例 `Rrcrcrcr:RgP-P-P-:RuRuRuRu` は誤り**: L0:SE/SW/NW = `cr`（非空）のため、正しい BFS でも L1 ピンは接地する。ゲームでピンが落下するのは砕け散り (shatter) が先行して結晶が消滅するため
- **影響範囲**: `groundedPositions` → `floatingUnits` → `gravity` の全連鎖、および SettledState.lean の多数の証明
- **詳細**: [`gravity-proof-execution-plan.md` §0](../plans/gravity-proof-execution-plan.md) を参照
