# Gravity 証明計画（Phase D-10）

- 作成日: 2026-04-29
- 最終更新: 2026-04-29
- ステータス: **Phase D-10D-5 セッション 8 完了。§6.6.F `obs0_isGrounded_of_nonEmpty` の lift を helper `IsGroundingEdge.of_getQuarter_eq` 追加 + path 記帰 (`grounded_path_avoids_floating` を path 部分長を含めて適用) で closes。警告 4 件 → 1 件 (`push_neg` ×3 を `push Not` に置換)。残 sorry 6 → 5 (6.4.B / 6.4.C / 6.5.A / 6.5.C / 6.6.D)。ビルドグリーン、axiom 24 不変。**
- スコープ: `S2IL/Operations/Gravity.lean` の脱 axiom（残 3 axiom）
- 上位計画: [layer-ab-rewrite-plan.md §4.3](layer-ab-rewrite-plan.md)
- 構造拘束: [architecture-layer-ab.md §1.4.4](architecture-layer-ab.md)
- 仕様: [docs/shapez2/falling.md](../shapez2/falling.md)

> 過去の経緯（旧 wave モデル破綻 / 候補比較 / D-10A 反例検証 / D-10B/C 実装履歴）は git log と `_archive/pre-greenfield/` および [`/memories/repo/waveStep-grounding-mono-persistence.md`](#) を参照。本書は **現在進行中の証明と決定事項** に絞る。

---

## 1. 仕様の再確認（インテント固定）

[docs/shapez2/falling.md](../shapez2/falling.md) §6 の **1 パスアルゴリズム** を採用する:

1. 入力 `s` から構造クラスタと孤立ピンを算出（**開始時点に確定**、以降不変 = 結合凍結）
2. 接地判定で落下単位（浮遊クラスタ + 浮遊ピン）を列挙
3. 落下単位を `shouldProcessBefore`（同方角列で minLayer 小を先）で部分整列
4. 障害物シェイプ `O` を「全落下単位を除去した `s`」で初期化
5. 各落下単位 `U` を順に処理: 着地距離 `d(U)` を決め、`O` を更新
6. 最終結果を normalize

### 1.1 採用モデル (d): 落下単位ごとの最大降下距離を宣言的に定める

各落下単位 `U` に対し、降下距離 `dropOf U s : Nat` を `CanDropBy s U d` 述語の最大値で唯一に定める:

- 衝突: ① 床割れない (`d ≤ U.minLayer`) ② 元シェイプ非落下位置と衝突しない ③ 自身より小さい `dropOf` を持つ他単位の着地後と衝突しない
- 再帰: `shareDirection` 共有 ∧ `minLayer` 厳密小 を measure とした well-founded 再帰
- 結合凍結: `floatingUnits` は `s` から 1 回計算、以降再評価しない（spec §6.5 例 5 / interlock I-1〜I-3 の正解の根拠）

旧 wave モデル（`_archive/pre-greenfield/Operations/Gravity/`）の障害物シェイプ逐次更新（`placeLDGroups` 系）は採用しない。`dropOf` を 1 回計算した固定写像とし、衝突判定が同列 cross-unit の上書きを構造的に排除する。

### 1.2 公開 API（数学的契約）

| 性質 | 命題 |
|---|---|
| 全関数性 | `gravity : Shape → Shape`（0 層入力 → 0 層出力）|
| 安定性 | `IsSettled (gravity s)` |
| 不動点性 | `IsSettled s ∧ IsNormalized s → gravity s = s` |
| CW 等変性 | `(gravity s).rotateCW = gravity s.rotateCW` |
| 180° / CCW 等変性 | CW の facade 1 行系 |

派生定理: 冪等性 `gravity.idempotent`、レイヤ数不増 `gravity.layerCount_le`。

#### 1.2.1 `IsNormalized` 仮定の根拠

`IsSettled s → gravity s = s` 単独だと反例 `s = [L_grounded, L_empty]` を持つ。`IsSettled` は末尾空レイヤを禁止しないが、`gravity` 末尾の `Shape.normalize` は末尾空を除去する。spec [`falling.md §6.6`](../shapez2/falling.md) は出力正規形を要求するため、入力にも `IsNormalized s` を仮定する。

---

## 2. ファイル構成

```
S2IL/Operations/Gravity.lean              # facade（公開 API、≤ 150 行）
S2IL/Operations/Gravity/
├── Defs.lean                             # FallingUnit / floatingUnits / dropOf / gravity
├── Behavior.lean                         # IsSettled / 不動点 / 着地距離境界
├── Equivariance.lean                     # CW 等変性主証明（D-10E で新設）
└── Internal/
    ├── BFS.lean                          # 汎用 BFS 骨格（reachClosure, listDedup, horizontalAdj）
    ├── Collision.lean                    # BFS↔IsGrounded 同値、structuralCluster 不変、衝突判定
    ├── Drop.lean                         # CanDropBy 述語と Nat.find 抽出
    └── ShareDirection.lean               # 落下単位の方角共有関係と well-founded
```

`Test/Behavior/Gravity.lean` および `Scratch/PhaseD10*.lean` で `#guard` 凍結（spec §6.5 例 1〜9 + interlock I-1 / I-1' / I-2 をパス済み）。

---

## 3. 補題チェーン（MECE）

### 3.1 Layer A — `Defs.lean`（実装済み・axiom-free）

| 定義 | 内容 |
|---|---|
| `FallingUnit` | `\| cluster (ps : Finset QuarterPos) \| pin (p : QuarterPos)` |
| `FallingUnit.positions` / `.minLayer` | unit の位置集合と最下層 |
| `structuralNeighbors` / `structuralCluster` | `Quarter.canFormBond` ベースの構造結合 BFS（結晶結合 `IsBonded` とは別物） |
| `floatingClusters s` / `floatingPins s` / `floatingUnits s` | 浮遊単位列挙 |
| `groundingNeighborsUp` / `~Horiz` / `~Down` | BFS の MECE 3 ブランチ（D-10D-2 で分割） |
| `groundingNeighbors s p = Up ++ Horiz ++ Down` | 合成 |
| `isGroundedFast s p : Bool` | `reachClosure` ベースの計算可能版 |
| `shareDirection (U V : FallingUnit) : Bool` | 方角列共有判定 |
| `landingDistance obs u : Nat` | `find?` で着地距離を取得 |
| `gravity s : Shape` | 全落下単位を `dropOf` ぶん下ろして `normalize` |

**着地距離の仕様**: 「最小の `d ≥ 1` で『床到達 (`q.1 = d`)』または『直下に障害物』のいずれかが成立する d」。`find?` 失敗時は `getD m` で `m` にフォールバック。

### 3.2 Layer B — `Behavior.lean`

| 定理 | 内容 | 状態 |
|---|---|---|
| `Gravity.landingDistance_le_minLayer` | `landingDistance obs u ≤ u.minLayer` | ✅ axiom-free |
| `Shape.gravity.of_isSettled'` | `IsSettled s ∧ IsNormalized s → gravity s = s` | ✅ ブリッジ経由 |
| `Shape.gravity.idempotent` | 冪等性（系） | 派生 |
| `Shape.gravity.layerCount_le` | レイヤ数不増 | 派生 |

### 3.3 Internal — `Collision.lean`（D-10D 中核）

| § | 補題 | 状態 |
|---|---|---|
| §1 | `groundingNeighbors_subset_groundingEdge` | ✅ axiom-free |
| §1 | `groundingNeighbors_supset_groundingEdge` | ✅ axiom-free |
| §1 | `groundingNeighbors_iff_groundingEdge` | ✅ 系 |
| §2 | `isGrounded_of_isGroundedFast` | ✅ D-10D-3、`reachClosure_induction` 経由 |
| §2 | `isGroundedFast_of_isGrounded` | ✅ D-10D-4（`reachClosure_closed_of_fuel_ge` 解消で完全 axiom-free 化） |
| §3 | `isGroundedFast_iff_isGrounded` | ✅ 系 |
| §4 | `structuralCluster_canFormBond` | ✅ D-10D-3（root の `canFormBond` 仮定 `hp` を追加）|
| §4 | `structuralCluster_nonEmpty` | ✅ D-10D-3 |
| §5 | `floatingPins_eq_nil_of_isSettled` | ✅ D-10D-3 |
| §5 | `floatingClusters_eq_nil_of_isSettled` | ✅ D-10D-4（`structuralClustersPartition` を top-level 化 + `mem_structuralClustersPartition` で induction）|
| §5 | `floatingUnits_eq_nil_of_isSettled` | ✅ D-10D-4（§5 cluster + pin の合成、`Behavior.lean` ブリッジ axiom も theorem 化）|
| §6.1 | `Shape.subsumed_by` (private) / `.refl` / `.trans` | ✅ D-10D-5（反射・推移は無条件）|
| §6.1 | `IsGroundingEdge.mono` | ✅ D-10D-5a（`IsCrystal.mono_of_subsumed` / `nonEmpty_mono_of_subsumed` / `nonEmpty_nonPin_mono_of_subsumed` を介して IsContact / IsBonded ケースを機械的に処理）|
| §6.1 | `IsGrounded.mono` | ✅ D-10D-5a（root 非空は `nonEmpty_mono_of_subsumed`, path は `Relation.ReflTransGen.mono` + `IsGroundingEdge.mono`）|
| §6.2 | `IsSettled.normalize` | ✅ D-10D-5b（`subsumed_by` の逆方向は使わず、補助 `normalize_isPrefix` / `normalize_length_of_nonEmpty` / `getQuarter_normalize_eq` / `IsGroundingEdge.{left,right}_nonEmpty` / `IsGroundingEdge.of_normalize_range` を経由して path 上の各セルが t で非空 ⇒ t.normalize 範囲内 の隻不変量で直接持ち上げ）|
| §6.3 | `landingCondition_landingDistance_pos` | ✅ D-10D-5c（`Option.isSome_iff_exists` + `List.find?_some` + `landingDistance` unfold + `simp [hd]` で `getD` を `d` に簡約）|
| §6.4 | `placeUnit_subsumed_by` | ✅ D-10D-5d（条件付き、hDisjoint 下で acc 不変）— 補助 `length_setQuarter` / `getQuarter_setQuarter_of_ne` / `foldl_setQuarter_length` / `foldl_setQuarter_getQuarter_of_not_target` を §6.4 冉頭に追加。R-§6.4 は反例検証済 (23 ケース OK)、foldl 内 hDisjoint 確立は D-10D-5f の中身 |
| §6.4 | `landingCondition_witness` (6.4.A) | ✅ D-10D-5e（`List.any_eq_true` から witness 抽出、純粋簡約）|
| §6.4 | `placeUnit_witness_grounded` (6.4.B) | 🚧 sorry（D-10D-5e-2、layer 0 root or 直下障害物経由 + `IsUpwardGroundingContact` 縦分枝）|
| §6.4 | `placeUnit_unit_internal_path` (6.4.C) | 🚧 sorry（D-10D-5e-3、unit 構造結合の `placeUnit` 持ち上げ; pin は refl）|
| §6.4 | `placeUnit_grounding` (主) | ✅ D-10D-5e（A + B + C で骨組み、内部は B/C に委譲）|
| §6.5 | `stepUnit_landing_disjoint` (6.5.A) | 🚧 sorry（**R-§6.4 中核**、D-10D-5f-1）|
| §6.5 | `stepUnit_subsumed_by` (6.5.B) | ✅ D-10D-5f（5.A + `placeUnit_subsumed_by` の合成、内部は 5.A に委譲）|
| §6.5 | `stepUnit_grounded_invariant_step` (6.5.C) | 🚧 sorry（D-10D-5f-2、acc 由来 / 着地像で場合分け）|
| §6.5 | `foldl_grounded_invariant` | ✅ D-10D-5f（units 帰納、内部は 5.C に委譲）|
| §6.6 | `clearPositions_getQuarter_of_not_in` (6.6.A) | ✅ D-10D-5g（`foldl_setQuarter_getQuarter_of_not_target` 系）|
| §6.6 | `obs0_nonEmpty_imp_origS_nonEmpty` (6.6.B) | ✅ D-10D-5h（新 helper `foldl_setQuarter_const_empty_at_in_target` + `getQuarter_setQuarter_self` で in-flatMap チェーンを閉じた）|
| §6.6 | `obs0_nonEmpty_imp_not_floating` (6.6.C) | ✅ D-10D-5h（`foldl_setQuarter_const_empty_at_in_target` の対偶使用）|
| §6.6 | `not_floating_imp_grounded` (6.6.D) | 🚧 sorry（D-10D-5g-3、§5 対偶の局所版）|
| §6.6 | `grounded_path_avoids_floating` (6.6.E) | ✅ D-10D-5h（`isGroundedFast_of_isGrounded` + `floatingClusters` / `floatingPins` filter 展開）|
| §6.6 | `obs0_isGrounded_of_nonEmpty` (6.6.F) | 🚧 sorry（lift 部、D-10D-5g-5; B〜E から組立、IsGrounded.mono 逆向き lift）|
| §6.6 | `gravity_isSettled_collision` (主) | ✅ D-10D-5g（IsSettled.normalize + foldl + obs0 の合成、内部は F に委譲）|

外部 sub-lemma:

| 補題 | 場所 | 状態 |
|---|---|---|
| `reachClosure_closed_of_fuel_ge` | `Internal/BFS.lean` | ✅ D-10D-4（`init.Nodup` を仮定として追加し強化補題 `reachClosure_closed_aux` で閉包性を証明）|
| `listDedup_nodup` | `Internal/BFS.lean` | ✅ D-10D-4 |
| `mem_structuralClustersPartition` | `Internal/Collision.lean` private | ✅ D-10D-4 |
| `direction_all_nodup` / `layer0Roots_nodup` | `Internal/Collision.lean` private | ✅ D-10D-4 |

#### §1 の MECE 構造（決定済み）

`IsGroundingEdge` の 6 ケースが BFS 3 ブランチに排他的に対応する:

| `IsGroundingEdge` ケース | BFS ブランチ |
|---|---|
| `IsUpwardGroundingContact` 垂直 (p.1+1=q.1) | `Up` |
| `IsUpwardGroundingContact` 垂直 (q.1+1=p.1) | （`p.1≤q.1` と矛盾、空） |
| `IsUpwardGroundingContact` 水平 | `Horiz` |
| `IsBondedInLayer` | `Horiz`（結晶 ⇒ 非空・非ピン） |
| `IsBondedCrossLayer` (p.1+1=q.1) | `Up`（結晶 ⇒ 非空） |
| `IsBondedCrossLayer` (q.1+1=p.1) | `Down` |

`Direction.isAdjacent` 補助補題: `add_one_sub_self` / `self_sub_sub_one` / `isAdjacent_add_one` / `isAdjacent_sub_one` / `isAdjacent_cases`（`Internal/Collision.lean` private）。

### 3.4 Internal — `BFS.lean`（汎用骨格 + API）

汎用 BFS 骨格を Gravity 固有から分離: `listDedup` / `reachClosure {α} [DecidableEq α] (step) (init) (fuel)` / `horizontalAdj : QuarterPos → List QuarterPos`。

D-10D-3 で追加した API 補題（**axiom-free**、`§A` / `§B`）:

- `mem_listDedup_iff` / `listDedup_length_le`: dedup の集合保存・長さ単調
- `mem_reachClosure_of_mem_init` / `mem_init_subset_reachClosure`: init 包含
- `reachClosure_induction (step) (P) (hStep)`: BFS 帰納原理（init で成立 + step で保存 ⇒ 全体で成立）

D-10D-4 で追加（**axiom-free**）:

- `listDedup_nodup`: `(listDedup xs).Nodup`
- `reachClosure_closed_aux`: 強化版閉包補題（`fuel + init.length ≥ univ.length` で induction）
- `reachClosure_closed_of_fuel_ge (univ)`: 公開ラッパー、`init.Nodup` ∧ `univ.length ≤ fuel` で閉包性

#### 3.4.1 `reachClosure_closed_of_fuel_ge` 証明の実装結果（D-10D-4）

仮定強化: 元の plan §3.4 では `init.Nodup` を仮定していなかったが、**反例**:
`init = [a, a]`, `step init = [b]` のとき
`merged = listDedup ([a, a, b]) = [a, b]`、`merged.length = 2 ≤ init.length = 2` で
停止条件成立するが `b ∉ init`。よって `init.Nodup` 仮定が必須。

実装した強化版 `reachClosure_closed_aux`:

- 仮定: `init.Nodup` ∧ `init ⊆ univ` ∧ `step` が univ を保つ ∧ `univ.length ≤ fuel + init.length`
- `fuel` で帰納:
  - 基底 `fuel = 0`: `univ.length ≤ init.length` と `init.Subperm univ` より `init.Perm univ` → `step init ⊆ univ ⊆ init`
  - 帰納 `fuel = n+1`:
    - 停止 (`merged.length ≤ init.length`): `init.Subperm merged` + 長さ等しい → `init.Perm merged` → `step init ⊆ merged ⊆ init`
    - 進行: `merged.length ≥ init.length + 1` で IH 適用、`univ.length ≤ n + merged.length` を omega で導出

Mathlib 補題: `List.Nodup.subperm` / `List.Subperm.length_le` / `List.Subperm.perm_of_length_le` / `List.Perm.mem_iff`

### 3.5 Equivariance — `Equivariance.lean`（D-10E）

| 定理 | 主依存 |
|---|---|
| `floatingUnits.rotateCW_comm` | `clusterSet.rotateCW_comm`, `IsGrounded.rotateCW` |
| `shareDirection.rotateCW` / `CanDropBy.rotateCW` / `dropOf.rotateCW` | column / minLayer / Collision の CW 不変 |
| `gravity.rotateCW_comm` | dropOf.rotateCW |
| `gravity.rotate180_comm` / `rotateCCW_comm` | facade 1 行系 |

---

## 4. 段階的着手手順

### 完了済み

- **D-10A**: 反例検証先行。spec §6.5 9 例 + interlock I-1/I-1'/I-2 すべて整合。設計観点 7 項目を [docs/lean/plausible-guide.md](../lean/plausible-guide.md) に反映。
- **D-10B**: Layer A 部 (`Defs.lean` + `Internal/ShareDirection.lean`)。`Shape.gravity` を axiom → def 化。`#guard` 11 件パス。
- **D-10C**: 不動点・終端性 (`Behavior.lean`)。`landingDistance_le_minLayer` axiom-free、`gravity.of_isSettled'` をブリッジ axiom 経由で theorem 化。残 axiom 3 本: `isSettled` / `floatingUnits_eq_nil_of_isSettled` / `rotateCW_comm`。
- **D-10D-1**: `Internal/Collision.lean` 骨格作成（補題名と戦略コメント）。
- **D-10D-2**: §1 edge correspondence axiom-free 化 + `Internal/BFS.lean` 抽出 + `groundingNeighbors` MECE 3 分割（§3.3 §1 ブロック完了）。
- **D-10D-3**: BFS API 補題追加（`reachClosure_induction` ほか）+ §2 BFS 同値性 + §3 iff + §4 `structuralCluster` 構造不変 + §5 `floatingPins_eq_nil_of_isSettled`。残 sorry 3 本。
- **D-10D-4**: BFS 閉包補題 `reachClosure_closed_of_fuel_ge` を `init.Nodup` 強化版で証明（強化補題 `reachClosure_closed_aux` + `Mathlib.Data.List.Perm.Subperm`）。`structuralClustersPartition` を top-level `def` 化、`mem_structuralClustersPartition` で induction 可能化、§5 `floatingClusters_eq_nil_of_isSettled` 解消。Behavior.lean のブリッジ axiom (`floatingUnits_eq_nil_of_isSettled`) を `Internal.floatingUnits_eq_nil_of_isSettled` への転送 theorem に格上げ。**残 axiom 25 → 24**。残 sorry 1 本（§6）。
- **D-10D-5 着手（骨格作成）**: §6 `gravity_isSettled_collision` を MECE 5 補題に分解した骨格を `Internal/Collision.lean` §6 に展開。`Shape.subsumed_by` 関係（refl/trans 込み）を新設、`IsGroundingEdge.mono` / `IsGrounded.mono` / `IsSettled.normalize` / `landingCondition_landingDistance_pos` / `placeUnit_subsumed_by` / `placeUnit_grounding` / `foldl_grounded_invariant` / 主定理を `sorry` で配置。各補題は statement + 戦略コメント + R-§6.4 リスク（cross-unit 着地像 disjoint 性）を明記。残 sorry 1 → 8、axiom 24 不変。
- **D-10D-5a 完了**: `IsGroundingEdge.mono` / `IsGrounded.mono` を closes。補助 `IsCrystal.mono_of_subsumed` / `nonEmpty_mono_of_subsumed` / `nonEmpty_nonPin_mono_of_subsumed` を §6.1 に追加（いずれも `private theorem`）。`Relation.ReflTransGen.mono` + edge.mono で `IsGrounded.mono` を閉じ、残 sorry 8 → 6、axiom 24 不変。
- **D-10D-5b 完了**: `IsSettled.normalize` を closes。当初計画していた `Shape.subsumed_by t t.normalize` は逆方向（`length` 不等式が逆）のため使えず、代わりに補助 `normalize_isPrefix` (List 接頭辞) / `mem_takeWhile_imp` / `normalize_length_of_nonEmpty` (非空レイヤ index < normalize.length) / `getQuarter_normalize_eq` (normalize 範囲内では getQuarter 一致) / `IsGroundingEdge.{left,right}_nonEmpty` / `IsGroundingEdge.of_normalize_range` を §6.2 に集約。`IsSettled.normalize` 本体は path 帰納で v ごとに `v.1 < t.normalize.length` と `ReflTransGen (IsGroundingEdge t.normalize) p₀ v` を同時に作る `step_lift` で閉じる。補助 `nonEmpty_imp_layer_lt` / `nonEmpty_imp_layer_isEmpty_false` も追加。残 sorry 6 → 6（内部補助の混入のため、隻としては 1 本閉ねているが、`IsSettled.normalize` 自体は sorry-free）— 実質的には 7 → 6、axiom 24 不変。
  - MECE 保全: §6.1 は "subsumed_by ファミリー"（3 補助） + "edge ファミリー"（mono / IsGrounded.mono）に二分。§6.2 は "normalize 表示ファミリー"（isPrefix / length_of_nonEmpty / getQuarter_normalize_eq + mem_takeWhile_imp）と "edge 非空/normalize 提げファミリー"（left_nonEmpty / right_nonEmpty / of_normalize_range + nonEmpty_imp_layer_*）と 主補題 に三分。
- **D-10D-5（ファイル分割）**: `Internal/Collision.lean` のサイズ縮減のため §6 を新規 `Internal/Settled.lean` に分離。`crystal_isEmpty_eq_false` を `private` 解除して `Internal` 名前空間に公開（`Settled.lean` から参照）。facade に `import S2IL.Operations.Gravity.Internal.Settled` 追加。
- **D-10D-5c 完了**: `landingCondition_landingDistance_pos` を closes。`Option.isSome_iff_exists` で `find? = some d` を取り出し、`List.find?_some` で述語成立、`landingDistance` unfold + `simp [hd]` で `getD m` を `d` に簡約。残 sorry 6 → 5、axiom 24 不変。
- **D-10D-5d 完了**: `placeUnit_subsumed_by`（条件付き、hDisjoint 仮定下）を closes。§6.4 冒頭に `setQuarter` 基本性質補題を 4 本集約: `length_setQuarter` / `getQuarter_setQuarter_of_ne`（同レイヤ別方向 + 別レイヤの 2 ケース）/ `foldl_setQuarter_length` / `foldl_setQuarter_getQuarter_of_not_target`（書込先以外不変）。本体は subsumed_by を `⟨length 不変, getQuarter 不変⟩` の 2 成分に分解し、後者は hDisjoint で `q` 非空 ⇒ 全 target ≠ q を経由。残 sorry 5 → 4、axiom 24 不変。
  - **R-§6.4 反例検証完了**: `Scratch/PhaseD10D_PlaceUnit_Disjoint.lean` で §4.1 / §4.1.1 11 例 + interlock I-1 / I-1' / I-2 / I-3 + 追加 8 例 = **23 ケース**で foldl 中間 `acc'` ごとに `∀ p ∈ u.positions, (getQuarter acc' (p.1 - landingDistance acc' u, p.2)).isEmpty` を `#eval` 検査、全 OK。`landingDistance` の最小性（`landingCondition` の OR 分岐: 床到達 / 直下障害物）から target 自体が空であるべき構造的根拠が得られたため、Gravity モデルの再設計は不要と判断（pivot 棚上げ、観点はリスクレジスタに保存）。
- **D-10D-5e/f/g 着手（骨格詳細化）**: §6.4 / §6.5 / §6.6 を MECE な sub-lemma 群へ分解し、`Internal/Settled.lean` に骨格を配置。**主定理 `placeUnit_grounding` / `stepUnit_subsumed_by` / `foldl_grounded_invariant` / `gravity_isSettled_collision` の 4 本は sorry-free に組み立て、未確定要素は sub-lemma に局所化**。残 sorry 4 → 9、axiom 24 不変。
  - §6.4 分解: 6.4.A `landingCondition_witness`（**完全証明**、`List.any_eq_true` から witness 抽出）+ 6.4.B `placeUnit_witness_grounded`（sorry: layer 0 / 直下障害物 + `IsUpwardGroundingContact`）+ 6.4.C `placeUnit_unit_internal_path`（sorry: unit 構造結合の `placeUnit` 持ち上げ）。`placeUnit_grounding` 本体は A → B → C の合成 1 行系。
  - §6.5 分解: 6.5.A `stepUnit_landing_disjoint`（sorry、**R-§6.4 中核**）+ 6.5.B `stepUnit_subsumed_by`（**完全証明**、5.A → `placeUnit_subsumed_by` への 1 行委譲）+ 6.5.C `stepUnit_grounded_invariant_step`（sorry、acc 由来 / 着地像で場合分け）+ `foldl_grounded_invariant`（**完全証明**、units 帰納で 5.C を呼び出し）。`hAccBound : Shape.subsumed_by acc s ∨ acc.length = s.length` を不変量に追加し、stepUnit が length を保つ（`foldl_setQuarter_length`）/ subsumed を更新する 2 系統で連鎖。
  - §6.6 分解: 6.6.A `clearPositions_getQuarter_of_not_in`（**完全証明**）+ 6.6.B `obs0_nonEmpty_imp_origS_nonEmpty`（部分: in-flatMap → empty の帰納 1 件 sorry）+ 6.6.C `obs0_nonEmpty_imp_not_floating`（sorry）+ 6.6.D `not_floating_imp_grounded`（sorry、§5 の対偶局所版）+ 6.6.E `grounded_path_avoids_floating`（sorry、`IsGrounded` の path 上 cell も grounded ⇒ 非 floating）+ 6.6.F `obs0_isGrounded_of_nonEmpty`（部分: B〜D まで wired、最終 lift sorry）。`gravity_isSettled_collision` 本体は `IsSettled.normalize` + `foldl_grounded_invariant` + 6.6.F + sortedUnits permutation の 4 行合成（**完全 wiring**）。
  - **MECE 保全**: 各 § で「主補題（合成）」と「sub-lemma（具体内容）」を分離。主補題は sorry-free。sorry は具体的・閉じた statement を持つ末端 sub-lemma に局所化。次セッションは sub-lemma を 1〜2 本ずつ閉じれば確実に進む。
- **D-10D-5h 完了（§6.6 機械的 sub-lemma 3 件 closes）**: §6.4 凉頭の helper ブロックに `getQuarter_setQuarter_self`（setQuarter 同位置 ⇒ 書込値）と `foldl_setQuarter_const_empty_at_in_target`（`foldl_setQuarter_getQuarter_of_not_target` の双対・書込値が `Quarter.empty` 定数、書込先に q が含まれれば以後ステップで値を保って q で empty）を追加。それを使って:
  - **6.6.B internal sorry** を closes（`q ∈ flatMap` ⇒ obs0 q = empty、`hne` と矛盾）
  - **6.6.C** `obs0_nonEmpty_imp_not_floating` を closes（対偶: q が floating unit に含まれれば obs0 q = empty）
  - **6.6.E** `grounded_path_avoids_floating` を closes（`hPath` + `hRoot` で `IsGrounded s v`、`isGroundedFast_of_isGrounded` で `isGroundedFast s v = true`、`floatingClusters` / `floatingPins` の filter 定義を展開して矛盾導出）
  - 残 sorry 9 → 6、axiom 24 不変。残 6 件はすべて R-§6.4 中核 (6.5.A) / unit 内連結性 (6.4.B/C) / cluster 連結性逆向き (6.6.D) / 同値性 lift (6.6.F) に局所化。
  - **MECE 保全**: §6.6 は実質 6.4 凉頭 helper と同じ "setQuarter foldl の write/read 三補題」グループで閉じ、証明重さは §6.4-B/C と §6.5-A/C と §6.6-D/F に全集中した。「計算侧の平凡補題」と「スペック依存の本質補題」の分離が達成。

### Phase D-10D-5: `gravity.isSettled` 主証明（着手済、複数セッション想定）

§3.3 §6 `gravity_isSettled_collision` を MECE 5 補題に分解した骨格を `Internal/Collision.lean` §6 に配置済。`Shape.subsumed_by` 関係を導入し、シェイプ拡張に対する `IsGroundingEdge` / `IsGrounded` の単調性を骨組みの土台にする。foldl の不変量「全有効非空位置が grounded」を `obs0` 基底 + `stepUnit` ステップで保ち、最後に `IsSettled.normalize` を通す。完了で **axiom 24 → 23**。

#### サブセッション分割

| サブ | 補題 | 状態 | 性質 |
|---|---|---|---|
| 5a | `IsGroundingEdge.mono` / `IsGrounded.mono` | ✅ | `subsumed_by` 機械的 case + `ReflTransGen.lift` |
| 5b | `IsSettled.normalize` | ✅ | `dropTrailingEmpty` の接頭辞性 + 5a |
| 5c | `landingCondition_landingDistance_pos` | ✅ | `List.find?_eq_some` の述語回収 |
| 5d | `placeUnit_subsumed_by` (disjoint 仮定下) + disjoint 補題 | ✅ | **R-§6.4 検証**: `sortedUnits` 順序 + `landingCondition` 最小性 |
| 5e | `placeUnit_grounding` の MECE 分解 + 主補題 wiring | ✅ (主) / 🚧 (B/C) | A `landingCondition_witness`（済）/ B `placeUnit_witness_grounded` / C `placeUnit_unit_internal_path` |
| 5f | `foldl_grounded_invariant` の MECE 分解 + 主補題 wiring | ✅ (B / foldl) / 🚧 (A / C) | A `stepUnit_landing_disjoint` (R-§6.4 中核) / B `stepUnit_subsumed_by`（済）/ C `stepUnit_grounded_invariant_step` / 主 `foldl_grounded_invariant`（済） |
| 5g | `gravity_isSettled_collision` の MECE 分解 + 主補題 wiring | ✅ (主) / ✅ (F lift) / 🚧 (D) | A `clearPositions_getQuarter_of_not_in`（済）/ B `obs0_nonEmpty_imp_origS_nonEmpty`（済、D-10D-5h）/ C `obs0_nonEmpty_imp_not_floating`（済、D-10D-5h）/ D `not_floating_imp_grounded` / E `grounded_path_avoids_floating`（済、D-10D-5h）/ F `obs0_isGrounded_of_nonEmpty`（済、D-10D-5i） |
| 5h | §6.6 helper 追加完成 | ✅ | `getQuarter_setQuarter_self` / `foldl_setQuarter_const_empty_at_in_target`。B/C/E を機械的に閉じた |
| 5i | §6.6.F lift + 警告衰減 | ✅ | helper `IsGroundingEdge.of_getQuarter_eq` + path 記帰で closes。`push_neg` ×3 を `push Not` に一括置換 |

#### 次セッション以降の優先順位

骨格は確定済 (主補題 4 本は sorry-free)。次セッションは末端 sub-lemma を 1〜2 本ずつ閉じる。優先度は依存方向と R-§6.4 不確定性で決まる:

1. **5g-D `not_floating_imp_grounded`（中難度、§6.6 残最後）**: 6.6.A〜C/E/F 完了（D-10D-5h/i）。残 D は「非空 ∧ 全 floating unit に含まれない ⇒ IsGrounded」を以下 2 ルートで:
   - **pin ケース**: `getQuarter s q = Quarter.pin` ⇒ `q ∉ floatingPins s` の filter 述語が `pin && !isGroundedFast` なので、述語不成立 ⇒ `isGroundedFast s q = true` ⇒ `IsGrounded s q`。
   - **bondable ケース**: `q.canFormBond = true` ⇒ q ∈ bondablePos ⇒ ∃ cl ∈ structuralClusters s, q ∈ cl（partition 全射性、要補助 `mem_structuralClusters_of_canFormBond`）。`q ∉ FallingUnit.cluster cl` ⇒ cl ∉ floatingClusters ⇒ `clusterFloating s cl = false` ⇒ ∃ p ∈ cl, isGroundedFast s p = true。cluster 内連結性（要補助 `structuralCluster_grounded_uniform`: bond 連鎖は対称な IsGroundingEdge ⇒ BFS 到達性が cluster 内で一様）⇒ isGroundedFast s q = true。
   - 要 helper 2 本を §4 (structuralCluster の構造不変) 群に追加する余地あり。
2. **5e-B / 5e-C（中難度）**: 6.4.B `placeUnit_witness_grounded` は `placeUnit_writes_origS_value`（書込先で origS 値）の補助 1 つで閉じる見込み。6.4.C `placeUnit_unit_internal_path` は pin 自明 / cluster は `structuralCluster_canFormBond` (§4) の `placeUnit` 持ち上げで構成。
3. **5f-A / 5f-C（最大山場、R-§6.4 中核）**: 6.5.A `stepUnit_landing_disjoint` は反例検証済 (23 ケース) なので真。証明は `landingDistance` 最小性 + `acc.subsumed_by s` で「acc で grounded セルは s でも grounded ⇒ s で u を `d` 段下げる前は浮遊範囲内」の論証。6.5.C は 5.A 完成後に「acc 由来 / 着地像」の場合分けで wiring。

#### 反例検証先行（必須）

5d 着手前に `Scratch/PhaseD10D_PlaceUnit_Disjoint.lean` を新設し、§4.1 / §4.1.1 11 例 + interlock I-1 / I-1' / I-2 / **I-3** で各 unit の着地像が `acc` の非空セルと disjoint であることを `#guard` 検証する。**実施済み**（23 ケース全 OK）— pivot 不要。

#### 反例が出た場合の Gravity モデル再設計観点

R-§6.4 で disjoint 性が破れた場合に新モデルを設計するための観点:

1. **着地条件強化**: `landingCondition' obs u d := landingCondition obs u d ∧ u.positions.all (fun p => (getQuarter obs (p.1-d, p.2)).isEmpty)`。全着地像セルが acc で空である追加条件で cross-unit 重複を構造的排除。spec §6.3 の挙動と一致するか §4.1 11 例で再検証。
2. **完全宣言的モデル (b) への pivot**: `gravity s := Classical.choose (gravity_exists s)` + `gravity_spec` 一意性。fold 中の物理を取り扱わず、出力の直接的特徴付け（`IsSettled` ∧ `IsNormalized` ∧ 「`s` から有限回の単位落下で構成可能」）を満たす唯一の Shape として定義。`isGroundedFast` 等の計算側は別 def として分離、`#guard` のみで構成的検証。
3. **dropOf の静的化**: 現行 `landingDistance obs u`（acc 依存）を `dropOf u s : Nat`（s 固定）に置換。各 unit の dropOf を `s` のみから決定する well-founded 再帰で計算（同方角列で `minLayer` 厳密小の他 unit に依存）。`shouldProcessBefore` の半順序を `<` で明示（[plan §1.1]）。
4. **位置写像の純粋化**: `placeUnit` を `setQuarter` の foldl ではなく `Shape.fromMap` 風の宣言的構成に置換（`fun pos => match ... with | some u => quarterAt s (pos + dropOf u, pos.2) | none => quarterAt obs0 pos`）で書込順序を排除。
5. **MECE 性の再確認**: 反例検証で I-3 の挙動が現行モデルと spec で食い違う場合、spec [docs/shapez2/falling.md §6.4] の衝突安全性条項を改めて読み直し、cluster と pin の処理優先順位を確認する。

### Phase D-10E: 等変性

`Equivariance.lean` 新設、§3.5 の補題チェーン。`floatingUnits.rotateCW_comm` は既存の `clusterSet.rotateCW_comm` (Phase C) + `IsGrounded.rotateCW` (Phase D-1) の合成で済む見込み。完了で axiom 23 → 22（Gravity 全消滅）。

### Phase D-10F: 振り返り

[layer-ab-rewrite-plan.md §5](layer-ab-rewrite-plan.md) チェックリストを Gravity に適用、`_archive/pre-greenfield/Operations/Gravity*` の削除候補リスト作成。

---

## 5. リスクレジスタ

| # | リスク | 検知方法 | 緩和策 |
|---|---|---|---|
| R1 | BFS 完全性証明が `ReflTransGen` 帰納で爆発 | D-10D-3 で 3 セッション失敗 | ホップ数の有限性 + fuel 充足を別補題化、または「全非空象限 → layer 0 への直線パス」を `dropOf` から構成的に与える代替戦略 |
| R2 | `dropOf` の well-founded 再帰が `decreasing_by` で構築不能（再評価時） | Defs.lean のリビルドエラー | shareDirection の半順序を `<` で明示。R1 と独立 |
| R3 | normalize と等変性の相互作用で末尾レイヤの扱いがズレる | D-10E で `--------:--Cr----` 系の反例 | 等変性証明では normalize を最後に適用、`normalize.rotateCW_comm` を独立補題化 |
| R4 | interlock パターン（I-3）で採用モデル (d) が誤った `dropOf` を返す | §6 主定理証明中に発覚 | pin を独立 unit として処理（spec §6.4 衝突安全性、cluster と pin の `FallingUnit.positions` 統一処理で構造的回避） |
| R5 | `Classical.decPred` 経由の `IsSettled` で plausible 検証が遅すぎる | D-10E 反例検索が回らない | `isSettledFast : Shape → Bool` を独立 def 化（既に `isGroundedFast` が存在） |
| R-§6.4 | `placeUnit` の cross-unit 着地像重複が `landingCondition` 最小性で防がれない | `Scratch/PhaseD10D_PlaceUnit_Disjoint.lean` の disjoint `#guard` 失敗 / `placeUnit_subsumed_by` の disjoint 仮定が確立できない | (a) `landingCondition` を `landingCondition'`（全 unit セルが acc で空）に強化、(b) `dropOf` を `s` 固定写像に静的化、(c) §4 D-10D-5 末尾「Gravity モデル再設計観点」5 項目で pivot |

---

## 6. 完了条件（残項目）

- [x] §3.3 §1-§4 の sorry 解消（D-10D-2 + D-10D-3）
- [x] §3.3 §5 `floatingPins_eq_nil_of_isSettled`（D-10D-3）
- [x] §3.4 `reachClosure_closed_of_fuel_ge`（D-10D-4）
- [x] §3.3 §5 `floatingClusters_eq_nil_of_isSettled`（D-10D-4、`structuralClustersPartition` 構造化）
- [x] `floatingUnits_eq_nil_of_isSettled` を theorem 化（axiom 25 → 24、D-10D-4）
- [x] §6.1 `IsGroundingEdge.mono` / `IsGrounded.mono`（D-10D-5a）
- [x] §6.2 `IsSettled.normalize`（D-10D-5b）
- [x] §6.3 `landingCondition_landingDistance_pos`（D-10D-5c）
- [x] §6.4 `placeUnit_subsumed_by`（条件付き、D-10D-5d）
- [x] §6.4-A `landingCondition_witness`（D-10D-5e）
- [x] §6.4 `placeUnit_grounding` 主補題 wiring（D-10D-5e、内部 B/C は sorry）
- [x] §6.5-B `stepUnit_subsumed_by`（D-10D-5f、内部 5.A は sorry）
- [x] §6.5 `foldl_grounded_invariant`（D-10D-5f、内部 5.C は sorry）
- [x] §6.6-A `clearPositions_getQuarter_of_not_in`（D-10D-5g）
- [x] §6.6 `gravity_isSettled_collision` 主定理 wiring（D-10D-5g、内部 6.6.B〜F は sorry）
- [ ] §6.4-B `placeUnit_witness_grounded` を closes（5e-2）
- [ ] §6.4-C `placeUnit_unit_internal_path` を closes（5e-3）
- [ ] §6.5-A `stepUnit_landing_disjoint` を closes（5f-1、**R-§6.4 中核**）
- [ ] §6.5-C `stepUnit_grounded_invariant_step` を closes（5f-2）
- [x] §6.6-B `obs0_nonEmpty_imp_origS_nonEmpty`（D-10D-5h）
- [x] §6.6-C `obs0_nonEmpty_imp_not_floating`（D-10D-5h）
- [ ] §6.6-D `not_floating_imp_grounded` を closes（5g-3）
- [x] §6.6-E `grounded_path_avoids_floating`（D-10D-5h）
- [x] §6.6-F `obs0_isGrounded_of_nonEmpty` 最終 lift（D-10D-5i, helper `IsGroundingEdge.of_getQuarter_eq` + path 記帰）
- [ ] `gravity.isSettled` axiom 削除確認（axiom 24 → 23）
- [ ] `gravity.rotateCW_comm` を theorem 化（axiom 23 → 22、D-10E、Gravity 全消滅）
- [ ] `lake build` green、warning 0
- [ ] `S2IL/_agent/sorry-plan.json` の axioms[] から Gravity の 2 axiom が削除

### 撤退条件

- 3 セッション連続で同一補題が閉じない
- BFS 同値性証明で偽である反例が発覚（spec §6.5 / I-1〜I-3 整合性は D-10A で確認済みのため、出るとすれば実装定数のオフバイワン）
- `dropOf` の well-founded 再帰が再評価時に構築不能

撤退時は (b) 完全宣言的アプローチ（`gravity := Classical.choose ...` + `gravity_spec` 一意性証明）に pivot。

---

## 7. 関連

| 参照先 | 用途 |
|---|---|
| [architecture-layer-ab.md](architecture-layer-ab.md) §1.4.4 | 落下機構の構造的拘束 |
| [layer-ab-rewrite-plan.md](layer-ab-rewrite-plan.md) §4.3 | Phase D-10 の上位計画 |
| [docs/shapez2/falling.md](../shapez2/falling.md) | 落下仕様の正本 |
| [S2IL/Operations/Settled.lean](../../S2IL/Operations/Settled.lean) | `IsGrounded` / `IsSettled` / `IsGroundingEdge` の定義 |
| [S2IL/Kernel/Bond.lean](../../S2IL/Kernel/Bond.lean) | `IsBondedInLayer` / `IsBondedCrossLayer` / `IsBonded` の定義 |
| [S2IL/Kernel/Cluster.lean](../../S2IL/Kernel/Cluster.lean) | `ClusterRel` / `clusterSet` の定義 |
| [S2IL/Operations/Gravity.lean](../../S2IL/Operations/Gravity.lean) | facade |
| [S2IL/Operations/Gravity/Internal/Collision.lean](../../S2IL/Operations/Gravity/Internal/Collision.lean) | BFS 同値性主証明 |
| [`/memories/repo/waveStep-grounding-mono-persistence.md`](#) | 旧 wave モデル破綻ノート（採用モデル (d) の動機） |
| `_archive/pre-greenfield/Operations/Gravity/` | 過去の証明資産（参考） |
| `Scratch/PhaseD10[A-C]_*.lean` | D-10A 反例検証 / D-10B `#guard` テスト / D-10C ブリッジ axiom 検証 |
