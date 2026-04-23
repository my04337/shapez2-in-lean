# S1 証明計画: waveStep_nonGroundedLayerSum_lt

> 作成日: 2026-04-20
> 最終更新: 2026-04-22 (sorry-card 再編: 証明済み `waveStep_ngs_strict_bound` から残 1 sorry `waveStep_grounding_mono` へフォーカス移行)

## 現在の状態

**残 sorry: 1 件** — `waveStep_grounding_mono` (`S2IL/Operations/Gravity/ProcessWave.lean:92`)

この 1 件が閉じれば S1 本体 (`waveStep_nonGroundedLayerSum_lt`) が完了する。
`waveStep_ngs_strict_bound` (strict-bound 形式) は 2026-04-22 に telescoping 組立で証明完了。

→ **[`sorry-plan.json`](../../S2IL/_agent/sorry-plan.json)** — 対象 sorry ・ next_actions ・依存補題
→ **[`sorry-cards/waveStep_grounding_mono.md`](../../S2IL/_agent/sorry-cards/waveStep_grounding_mono.md)** — 証明戦略・実装設計（依存補題一覧）
→ **[`sorry-goals.md`](../../S2IL/_agent/sorry-goals.md)** — ビルド状態（自動生成）

---

## 目標

```lean
theorem waveStep_nonGroundedLayerSum_lt (s : Shape)
    (h : (floatingUnits s).isEmpty = false) :
    nonGroundedLayerSum (waveStep s) < nonGroundedLayerSum s
```

現在 `axiom` で宣言されている S1 を構成的定理に置き換える。

---

## 証明概略 (Telescoping Sum)

### 記号

- $S$ = settling positions (settling FU の全位置)
- $L$ = landing positions ($\{(p.\text{layer} - d, p.\text{dir}) \mid p \in S\}$)
- $d$ = landing distance (settling group の共通 LD)
- $w(p) = p.\text{layer} + 1$
- $\text{obs} = s.\text{clearPositions}(S)$

### Core Identity

$$\text{NGS}(\text{obs}) = \text{NGS}(s) - \sum_{p \in S} w(p)$$

理由: $\text{groundedPositions}(s) = \text{groundedPositions}(\text{obs})$ が成立するため、
settling 位置の寄与を除去するだけで他位置の寄与は不変。

### Landing Bound

$$\text{NGS}(s') \leq \text{NGS}(\text{obs}) + \sum_{p \in L,\, \text{empty in obs}} w(p)$$

理由:
- 非 settling ・非 landing 位置: 内容不変 + 接地単調 → 寄与 ≤ 元の値
- B3 位置 (landing on occupied): 同一レイヤ → 寄与不変 or 改善
- Landing on empty: 新規寄与 ≤ $w(\text{landing})$

### Telescoping

$$\sum_{p \in L,\, \text{empty}} w(p) \leq \sum_{q \in S} w(\text{landing}(q)) = \sum_{q \in S} (w(q) - d) = \sum_{q \in S} w(q) - |S| \cdot d$$

### 結合

$$\text{NGS}(s') \leq \text{NGS}(s) - |S| \cdot d \leq \text{NGS}(s) - 1$$

$|S| \geq 1$ (settling 非空) かつ $d \geq 1$ (landingDistance ≥ 1) による。

---

## 重要発見

### B3 は偽 (4L+)

**B3 (landing positions empty in obs)** は ≤3L で真だが 4L で偽。
pin が存在する結晶ボンドチェーン迂回パターンで、settling cluster が非 settling pin 位置に着地する。

**証明への影響**: B3 不要。着地位置が非空でも同一レイヤ → 寄与不変。

### Pin B3 は不発生

Pin singleton FU は B3 を起こさない (4L/3-type 531K shapes, 0 failures)。
理由: pin の非接地性には同方向の垂直ギャップが必須。LD はギャップ内に着地させる。

### 接地保存

- `groundedPositions(s) = groundedPositions(obs)`: clearing の双方向保存
  - ⊆: `clearPositions_preserves_grounded` (既証明)
  - ⊇: 削除されたエッジは非接地位置のもの → 接地パスに影響なし
- `groundedPositions(obs) ⊆ groundedPositions(s')`: placing の単調性
  - Cluster settling: 配置内容 = crystal/colored (canFormBond=true) → 全エッジ保存
  - Pin settling: 空位置に配置 → エッジ追加のみ

---

## Sub-lemma 一覧

> 証明状況は [`sorry-cards/waveStep_grounding_mono.md`](../../S2IL/_agent/sorry-cards/waveStep_grounding_mono.md) の「既に証明済みの足場」セクション、および過去カードのマイルストーン表を参照。

| # | 名前 | 依存先 |
|---|------|--------|
| 1 | `clearPositions_preserves_grounded` | edge_preserve_of_reachable |
| 2 | `groundedPositions_clearNonGrounded_eq` | #1 + clearPositions_grounded_reverse |
| 2a | `clearPositions_grounded_reverse` | isGroundingContact_nonEmpty |
| 3 | `nonGroundedLayerSum_clear_add` | #2, #3a-c |
| 3a | `ngsWeight` / `ngs_foldl_eq_sum` | foldl→sum変換 |
| 3b | `nonGroundedLayerSum_eq_sum` | NGS = Σ ngsWeight |
| 3c | `ngsWeight_clearPositions_mem/not_mem` | 点別寄与の保存/消去 |
| 3d | `sum_map_ite_eq_sum_filter` / `sum_map_add` | helper: sum 分解 |
| 3e | `ngsWeight_eq_layer_succ_of_mem_floatingUnits_positions` (CommExt) | FU 位置での ngsWeight = layer+1 |
| 3e' | `map_ngsWeight_eq_map_layer_succ_of_subset_floatingUnits_positions` (CommExt) | 3e の map 版（合計書換え用） |
| - | `layer_zero_nonempty_grounded` | BFS シード条件の直接適用 |
| - | `landingDistance_check_ge_min` | check ≥ min d maxDrop |
| - | `landingDistance_ge_one` | minLayer ≥ 1 → LD ≥ 1 |
| - | `floatingUnits_positions_ne_nil` | BFS seed + allStructuralClustersList 非空 |
| - | `floatingUnits_minLayer_ge_one` | minLayer_witness + layer_zero_nonempty_grounded |
| - | `settling_minLayer_ge_one` | floatingUnits_minLayer_ge_one の filter 版 |
| - | `structuralClusterList_contains_seed` | genericBfs_contains_start |
| - | `allStructuralClustersList_ne_nil` | foldl 不変条件 |
| 4 | `pin_singleton_landing_empty` | landingDistance analysis |
| 4a | `grounded_of_edge` | BFS sound/complete の 1 ステップ合成 |
| 4b | `ungrounded_pin_layer_one_below_empty` | #4a + isUpwardGroundingContact + layer_zero シード |
| 5 | `placing_cluster_preserves_grounding` | canFormBond analysis |
| 5a | `isOccupied_placeQuarter_mono` / `isOccupied_placeFallingUnit_mono` | 非空配置 → isOccupied 単調保存 |
| 5b | `isGroundingContact/isStructurallyBonded/groundingEdge _congr_of_getQuarter_eq` | `getQuarter` 等しい 2 shape でエッジ値一致 |
| 5c | `getDir_placeFallingUnit_of_ne` (CommExt) | 非着地位置での list-level `getDir` 保存 |
| 5d | `getQuarter_eq_of_getDir_getD_eq` / `groundingEdge_congr_of_getDir_getD_eq` (CommExt) | list-level `getDir getD` → shape-level `getQuarter` / `groundingEdge` 橋渡し |
| 5e | `placeFallingUnit_length_ge` (CommExt) / `groundingEdge_placeFallingUnit_of_ne` (CommExt) | 長さ非減少 + shape-level エッジ保存 (非着地位置) |
| 5f | `foldl_placeFU_fixed_length_ge` / `getDir_foldl_placeFU_fixed_of_ne` / `groundingEdge_foldl_placeFU_fixed_of_ne` (CommExt) | 固定 d での group foldl レベル エッジ保存（#5e の group 版）|
| 5g | `placeLDGroupsLandings` / `placeLDGroups_length_ge` / `getDir_placeLDGroups_of_ne` / `groundingEdge_placeLDGroups_of_ne` (CommExt) | placeLDGroups レベルの着地位置列挙 + 非着地位置でのエッジ保存（#5f の可変 d 版）|
| 5h | `placeLDGroupsLandings_mem_exists` / `placeLDGroupsLandings_mem_exists_drop` (CommExt) | `(lay, dir) ∈ placeLDGroupsLandings → ∃ u ∈ sorted, ∃ p ∈ u.positions, lay ≤ p.layer`（弱形）/ `∃ d ≤ u.minLayer, lay = p.layer - d`（強形 telescoping 接続用）|
| 5i | `placeLDGroupsLandings_layer_lt_layerCount` / `getQuarter_placeLDGroups_of_ne` / `placeLDGroupsLandings_mem_exists_drop_ge_one` (CommExt) | 着地位置の端点妥当性 `lay < s.layerCount` / 非着地位置 shape-level `getQuarter` 保存 / 強形 drop 特徴付けの `1 ≤ d` 付き版 |
| 5j | `isGroundingContact_eq_of_getQuarter_eq` / `groundingEdge_eq_of_getQuarter_eq` / `groundedPositions_mono_of_edge` / `groundedPositions_placeLDGroups_subset` (Gravity/**GroundedMono.lean**) | Settled/GroundedCore から Gravity 層に移設。grounding 単調性パッケージ |
| 6 | `placing_pin_empty_preserves_grounding` | #4, #5a |
| 7 | `waveStep_grounding_mono` | #1, #5, #6 |
| 8 | `landing_positions_injective` | FU position distinctness |
| 8a | `landing_shift_injective_of_layer_ge` (CommExt) | layer≥d での landing 単射 |
| 8b | `landing_map_nodup_of_layer_ge` (CommExt) | Nodup 位置リスト→Nodup landing |
| 8c | `landing_shift_injective_on_fu` / `landing_map_nodup_on_fu` (CommExt) | 単一 FU 版 |
| 8d | `pin_positions_nodup` (CommExt) | Pin の positions.Nodup |
| 8e | `floatingUnits_positions_pairwise_disjoint` (CommExt) | 異 FU の位置共有なし (cluster×cluster/pin×pin/cross) |
| 8g | `floatingUnits_flatMap_positions_nodup` (CommExt) | #8f + #8e 統合 (nodup_flatMap) |
| 8f | `structuralClusterList_nodup` (CommExt) + `genericBfs_nodup` (Kernel) | BFS 出力の重複なし |
| 9 | `landing_sum_bound` (CommExt) + `sum_map_layer_landing_telescope` | 着地重み telescoping + 部分集合境界 |
| 9a | `landing_sum_bound_var_d` (CommExt/Arith) | 可変 d 対応の `+ 1 ≤` 形式 |
| 9b | `waveStep_layers_eq` (Gravity/Defs.lean) | waveStep 内部の `match Shape.ofLayers` 解消 |
| 10 | `waveStep_nonGroundedLayerSum_lt` | #waveStep_ngs_strict_bound |
| 10a | `waveStep_ngs_strict_bound` | #3, #7, #9, assembly |

---

## 計算検証サマリ

| テスト | 結果 |
|--------|------|
| Main axiom (plausible) | PASSED |
| Main axiom (2L/3L 全数, 4L/2-type) | 0 failures |
| Clearing preserves grounding (2L/3L) | 0 failures (537K shapes) |
| Chain grounding (s→s') 4L/3-type | 0 failures (531K shapes) |
| Place grounding (obs→s') 4L/3-type | 0 failures (531K shapes) |
| Pin singleton B3 (4L/3-type) | 0 failures (531K shapes) |
| B3 failures (4L/3-type) | 5+ failures (crystal clusters only) |

---

## 撤退基準

- 3 セッション or 8 アプローチ失敗 → axiom 維持、T-4b へ

---

## 進捗履歴

進捗履歴は [`sorry-cards/waveStep_grounding_mono.md`](../../S2IL/_agent/sorry-cards/waveStep_grounding_mono.md) のマイルストーン表と `git log` を参照。
本計画書には現在のスナップショットのみを記載する。

