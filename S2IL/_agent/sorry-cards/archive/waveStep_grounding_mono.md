# Sorry Card: `waveStep_grounding_mono`

> 最終更新: 2026-04-23（第44報: **標準化補題抽出** — `h_edge_landing` 枝を `Gravity.placeLDGroups_landing_groundingEdge_mono` (GroundedMono.lean:943) に抽出。`waveStep_grounding_mono` 本体は 0 sorry 化し refine/exact のみで閉じた。sorry は新 scaffold 補題に集約。**本カードは残存しているが、S1 の残 sorry は新補題カード `placeLDGroups_landing_groundingEdge_mono.md` で追跡**する。）
> 位置: `S2IL/Operations/Gravity/ProcessWave.lean:91` 付近（本体から sorry なし）
> スコープ: `private theorem`
> ステータス: 🟢 **DELEGATED** — sorry は `placeLDGroups_landing_groundingEdge_mono` へ移動
> 詳細: [`placeLDGroups_landing_groundingEdge_mono.md`](./placeLDGroups_landing_groundingEdge_mono.md)
> **Preflight**: 本カードに active sorry なし。作業先 → [`placeLDGroups_landing_groundingEdge_mono.md`](./placeLDGroups_landing_groundingEdge_mono.md)

---

## ゴール

```lean
private theorem waveStep_grounding_mono (s : Shape)
    (h : (floatingUnits s).isEmpty = false) :
    let fus := floatingUnits s
    let minML := fus.tail.foldl (fun acc u => min acc u.minLayer)
        (fus.head?.map FallingUnit.minLayer |>.getD 0)
    let settling := fus.filter fun u => u.minLayer == minML
    let settlingPos := settling.flatMap FallingUnit.positions
    groundedPositions (s.clearPositions settlingPos) ⊆ groundedPositions (waveStep s)
```

直観: `obs = s.clearPositions settlingPos` の接地位置は、その後の
`placeLDGroups` 適用（= `waveStep s` の中身）でも接地のまま保存される。

---

## 上流（この補題を使う場所）

- `waveStep_ngs_strict_bound` (`ProcessWave.lean:92` 以降、**✅ 証明済み**)
  - `h_gm := waveStep_grounding_mono s h` を step 2 の核心として利用
- `waveStep_nonGroundedLayerSum_lt` (S1 本体) — `strict_bound` 経由で依拠

この 1 sorry が閉じれば S1 全体が完了する。

---

## 証明戦略（現時点の計画）

> 🔵 **2026-04-23 第43報: 新戦略「pin/cluster FU 型別場合分け」を採用**。
> α1/α4 (「全着地 obs 非空」ワンショット vacuous) は反例確定のため撤去。代替として `placeLDGroupsLandings_mem_exists_drop_*` から landing-origin FU を取り出し、
> **pin 型: obs の空性で vacuous（要 d 補正）**／**cluster 型: canFormBond 書き込み保存**（Step B3b）で攻める。

**全体像**:

```
waveStep_grounding_mono                                    ← 🔴 本 sorry
  └── Shape.groundedPositions_placeLDGroups_subset         ← ✅ 証明済み
          requires:
            h_edge_landing  (cluster + pin 着地端点で edge 不変)
            h_seed_landing  (cluster + pin 着地位置 layer-0 で非空象限)
```

### Step B4: scaffold 反映（✅ 2026-04-22 第39報）

- `ProcessWave.lean` の `waveStep_grounding_mono` 本体を `Shape.groundedPositions_placeLDGroups_subset` 呼出形に展開済み。
- `h_seed_landing` は `placeLDGroups_landing_nonEmpty` 一本で閉じている（構成的証明）。
- 残る sorry は `h_edge_landing` 枝のみ（Step B3b の提供補題待ち）。

### Step B3b: `placeLDGroups_groundingEdge_mono`（残）

B3a mixed (`foldl_placeFU_mixed_fixed_d_groundingEdge_mono`, 2026-04-22 ✅) を足場に、
`placeLDGroups.induct` で group 単位の再帰を処理する。

- **induction**: `placeLDGroups.induct` を使って `sortedSettling` の group 分解を帰納
- **各 group step**: B3a mixed を適用して foldl 内部を閉じる → `obs'` に更新
- **remaining 側**: 帰納仮説で閉じる
- **不変量の伝播**: cluster canFormBond は `s` ベースで評価されるため `obs'` 更新で不変、pin landing-empty は別 group の着地で書き込み先が重ならないことを positions Nodup で示す

### Step B4: `waveStep_grounding_mono` 組立（残）

`Shape.groundedPositions_placeLDGroups_subset` に以下を供給して閉じる:

- **`h_edge_landing`**:
  - cluster 側: B3b から直接
  - pin 側: `pin_landing_groundingEdge_false_{left,right}` で vacuous
- **`h_seed_landing`**:
  - cluster 側: `foldl_placeQuarter_written_getQuarter_canFormBond` から canFormBond → `!isEmpty`
  - pin 側: layer-0 で pin が着地するなら pin.isEmpty = false なので直接満たす（`pin_singleton_landing_empty_d_one_at_floor` の vacuous 化も代替として利用可）

---

## 直接利用する補題（シグネチャは `symbol-map.jsonl` 参照）

### Step B4 組立

| 補題 | 役割 | ファイル |
|---|---|---|
| `Shape.groundedPositions_placeLDGroups_subset` | 最終的な package 定理 | `Gravity/GroundedMono.lean` |
| `pin_landing_groundingEdge_false_left` / `_right` | pin 側 `h_edge_landing` vacuous | `Gravity/CommExt.lean` |
| `pin_singleton_landing_empty_d_one_at_floor` | pin 側 `h_seed_landing` vacuous 化 | `Gravity/CommExt.lean` |
| `foldl_placeQuarter_written_getQuarter_canFormBond` | cluster 側 `h_seed_landing` 供給 | `Gravity/CommExt.lean` |

### Step B3b 予定補題（未実装）

| 仮称 | 役割 |
|---|---|
| `placeLDGroups_groundingEdge_mono` | 各 group で B3a mixed を適用し、最終 `obs'` が元 `obs` の edge を保存 |
| 補助不変量 | cluster FU の `canFormBond`、pin FU の landing-empty が group 横断で保存 |

---

**新補助補題群（Step B3b-α1 〜 α4）**:

### α1: `settling_position_below_empty_obs`（d=1 landing の基盤、2026-04-23 追加）

```lean
theorem settling_position_below_empty_obs
    (s : Shape) (sorted : List FallingUnit) (settlingPos : List QuarterPos)
    (h_sp : sorted.flatMap FallingUnit.positions = settlingPos)
    (h_sub : ∀ u ∈ sorted, u ∈ floatingUnits s)
    (h_min : ∀ u ∈ sorted, ∀ v ∈ floatingUnits s, u.minLayer ≤ v.minLayer)
    {u : FallingUnit} (hu : u ∈ sorted)
    {p : QuarterPos} (hp : p ∈ u.positions) (h_layer : 1 ≤ p.layer) :
    isOccupied (s.clearPositions settlingPos).layers (p.layer - 1) p.dir = false
```

**証明戦略** (2026-04-23 分析):
- by_contra: `isOccupied obs (p.layer - 1) p.dir = true` と仮定
- `clearPositions` の occupancy 反転: 当該位置が settlingPos に含まれれば empty → 矛盾
- 含まれない場合: `s.layers` 上で非空 → 非空象限 q0 抽出
- `isGroundingContact s ⟨p.layer - 1, p.dir⟩ p = true`（vertical + same dir + 両非空、**pin も OK**）
- `isUpwardGroundingContact` 化 → `groundingEdge` 成立
- q0 の所属で場合分け:
  - **q0 grounded**: `grounded_of_edge` で p grounded → `floatingUnits_positions_getQuarter.2` の非 grounded と矛盾
  - **q0 floating**: q0 を含む FU u' の minLayer ≤ p.layer - 1。`h_min` より settling FU の minLayer は全 FU の最小。
    - u' ∈ sorted ⇒ q0 ∈ settlingPos（h_sp）→ clearPositions で空 → 当初矛盾
    - u' ∉ sorted ⇒ minML ≤ u'.minLayer ≤ p.layer - 1 < p.layer かつ u'.minLayer > minML で矛盾

**前例補題**: `ungrounded_pin_layer_one_below_empty`（pin + layer=1 専用）を一般化したもの。同様の構造で証明可能。

### α2: `landingDistance_not_occupied_at_landing_d_one`（d=1 ケース拡張）

```lean
theorem landingDistance_not_occupied_at_landing_d_one
    (u : FallingUnit) (s : Shape) (sorted : List FallingUnit) (settlingPos : List QuarterPos)
    (h_sp : sorted.flatMap FallingUnit.positions = settlingPos)
    (h_sub : ∀ v ∈ sorted, v ∈ floatingUnits s)
    (h_min : ∀ v ∈ sorted, ∀ w ∈ floatingUnits s, v.minLayer ≤ w.minLayer)
    (hu : u ∈ sorted)
    (hd : landingDistance u (s.clearPositions settlingPos).layers = 1) :
    ∀ p ∈ u.positions, isOccupied (s.clearPositions settlingPos).layers (p.layer - 1) p.dir = false
```

**証明**: α1 + `floatingUnits_minLayer_ge_one` から p.layer ≥ 1。各 p に α1 を適用。

### α3: `foldl_placeFU_isOccupied_antimono`（contrapositive mono、持続性）

```lean
theorem foldl_placeFU_isOccupied_antimono (s : Shape) (group : List FallingUnit)
    (obs : List Layer) (d : Nat) (h_sub : ∀ u ∈ group, u ∈ floatingUnits s)
    (lay : Nat) (dir : Direction)
    (h : isOccupied (group.foldl (fun acc fu => placeFallingUnit s acc fu d) obs) lay dir = false) :
    isOccupied obs lay dir = false
```

**証明**: `foldl_placeFU_getDir_ne_empty_mono` の対偶 + `isOccupied_iff_getDir_ne_empty` 両向き。

### α4: `placeLDGroupsLandings_isOccupied_obs_false`（本丸）

```lean
theorem placeLDGroupsLandings_isOccupied_obs_false
    (s : Shape) (sorted : List FallingUnit) (settlingPos : List QuarterPos)
    (h_sp : sorted.flatMap FallingUnit.positions = settlingPos)
    (h_sub : ∀ u ∈ sorted, u ∈ floatingUnits s)
    (h_min : ∀ u ∈ sorted, ∀ v ∈ floatingUnits s, u.minLayer ≤ v.minLayer)
    {lay : Nat} {dir : Direction}
    (h : (lay, dir) ∈ placeLDGroupsLandings s sorted (s.clearPositions settlingPos).layers) :
    isOccupied (s.clearPositions settlingPos).layers lay dir = false
```

**証明戦略**:
- `placeLDGroups.induct` で group 単位に分解
- group case: first FU の landingDistance d で分岐
  - d ≥ 2: `landingDistance_not_occupied_at_landing`（既存）
  - d = 1: α2 (`_d_one`)
- rest case: IH で `isOccupied obs_k = false`、α3 で `isOccupied obs = false`

### B3b-β/γ: h_edge_landing 閉形（α4 完成後）
```lean
intro a b h_edge h_landing; exfalso
rcases h_landing with h_in | h_in
all_goals {
  have h_empty := placeLDGroupsLandings_isOccupied_obs_false s sorted ... h_in
  -- isOccupied_eq_getQuarter + groundingEdge_false_of_empty_quarter{_right} で h_edge と矛盾
}
```

---

## 既に証明済みの足場（主要補題のみ抜粋）

| 補題 | ファイル | 役割 |
|---|---|---|
| `foldl_placeFU_cluster_fixed_d_groundingEdge_mono` | `GroundedMono.lean` | B3a cluster-only |
| `foldl_placeFU_pin_fixed_d_groundingEdge_mono` | `GroundedMono.lean` | B3a pin-only |
| `foldl_placeFU_mixed_fixed_d_groundingEdge_mono` | `GroundedMono.lean` | **B3a mixed — B3b の足場** |
| `placeFallingUnit_cluster_groundingEdge_mono` | `GroundedMono.lean` | B1 cluster |
| `placeFallingUnit_pin_groundingEdge_mono` | `GroundedMono.lean` | B1 pin |
| `placeFallingUnit_cluster_written_getQuarter_canFormBond` | `GroundedMono.lean` | B2 cluster seed |
| `Shape.groundedPositions_placeLDGroups_subset` | `GroundedMono.lean` | Step B4 の package |
| `isGroundingContact_mono_canFormBond_left/right/both` | `GroundedMono.lean` | B1 cluster の分岐閉塞 |
| `isStructurallyBonded_of_parts` / `_canFormBond_left/right` | `GroundedMono.lean` | B1 cluster の分岐閉塞 |
| `canFormBond_implies_not_empty` / `layer_lt_of_isGroundingContact_*` | `GroundedMono.lean` | B1/B2 補助 |
| `pin_landing_groundingEdge_false_left` / `_right` | `CommExt.lean` | pin vacuous |
| `pin_singleton_landing_empty_d_one_at_floor` | `CommExt.lean` | pin seed vacuous |
| `foldl_placeQuarter_written_canFormBond` / `_getQuarter_canFormBond` | `CommExt.lean` | cluster seed |
| `isOccupied_placeFallingUnit_of_pos_ne` (private) | `GroundedMono.lean` | B3a pin 補助 |

完全な履歴は `git log --oneline S2IL/Operations/Gravity/` を参照。

---

## 反例検証（過去の記録）

- 主張相当テスト: 2L/3L 全列挙 + 4L/2-type, 4L/3-type PASSED
- B3 (landing empty): 4L で偽 → 本証明では B3 に依存しない戦略を採用
- Pin singleton B3 不発生: 4L/3-type 531K shapes で 0 failures

---

## 実装設計（remaining_steps 本体ごとの技術メモ）

> 進行管理（次に何をやるか・ステップの順序・セッション末のフォローアップ）は [`sorry-plan.json`](../sorry-plan.json) の `remaining_steps` と `next_actions` に一本化する。本カードはシグネチャ候補・依存補題・数学的不変量など **実装設計** のみを保持する。

### Step B3b: `placeLDGroups_groundingEdge_mono`

**シグネチャ候補**:
```lean
theorem placeLDGroups_groundingEdge_mono
    (s : Shape) (sortedSettling : List FallingUnit) (obs : List ...)
    (h_layers : obs = (s.clearPositions settlingPos).layers)
    (h_sorted_sub : ∀ u ∈ sortedSettling, u ∈ floatingUnits s)
    (h_all_cluster_bond : ∀ u ∈ sortedSettling, u.isCluster → ∀ quarter …, canFormBond)
    (h_all_pin_landing_empty : ∀ u ∈ sortedSettling, u.isPin → isOccupied obs _ = false)
    (h_layer_lt : ∀ u ∈ sortedSettling, ∀ p ∈ u.positions, p.layer < obs.length)
    (h_layer_ge : ∀ u ∈ sortedSettling, ∀ p ∈ u.positions, landingDistance u obs ≤ p.layer)
    (h_all_nodup : (sortedSettling.flatMap FallingUnit.positions).Nodup) :
    ∀ a b : QuarterPos, a ∉ landings → b ∉ landings →
      groundingEdge obs a b = true →
      groundingEdge (placeLDGroups s sortedSettling obs) a b = true
```

**不変量の伝播**:
- `placeLDGroups.induct` で group 単位に分解し、各 group step で B3a mixed (`foldl_placeFU_mixed_fixed_d_groundingEdge_mono`) を適用
- cluster canFormBond は `s` ベース評価 → obs' 更新で不変
- pin landing-empty は positions Nodup + 別 group 着地位置の disjoint 性で保存

### Step B4: `waveStep_grounding_mono` 本体の組立

**B4 scaffold（コンパイル確認済み 2026-04-22）**:

```lean
private theorem waveStep_grounding_mono (s : Shape)
        (h : (floatingUnits s).isEmpty = false) : ... := by
    set fus := floatingUnits s with hfus
    set minML := ...
    set settling := ...
    set settlingPos := ...
    set obs_shape := s.clearPositions settlingPos with hobs_shape
    set obs := obs_shape.layers with hobs
    set sortedSettling := settling.mergeSort ... with hsorted
    set landings := placeLDGroupsLandings s sortedSettling obs with hlandings
    have h_layers : (waveStep s).layers = placeLDGroups s sortedSettling obs :=
        waveStep_layers_eq s h
    have h_obs_layers : obs_shape.layers = obs := rfl
    exact Shape.groundedPositions_placeLDGroups_subset s sortedSettling obs
        obs_shape (waveStep s) h_obs_layers h_layers
        h_edge_landing  -- ★ B3b + pin vacuous で構築
        h_seed_landing  -- ★ Step 0.2 事前補題で構築
```

**h_edge_landing の構築方針（2026-04-23 第43報で再々設計）**:

**新戦略: pin/cluster FU 型別場合分け**

2026-04-23 第42報の "全着地 obs 非空" 戦略（α1 `settling_position_below_empty_obs` / α4 `placeLDGroupsLandings_isOccupied_obs_false`）は
反例発見により **撤去**（`Scratch/commands-s1-alpha1-counter-05.jsonl` / `-06.jsonl`）。
非 settling pin が cluster 着地位置の直下にあるシナリオで obs に非空のまま残る。

代わりに `placeLDGroupsLandings_mem_exists_drop_ge_one_of_subset_fu` で landing a を FU u まで還元し、
**u の型（pin/cluster）で場合分け**:

**ケース 1: u = pin p（vacuous 化）**

Scaffold で事前に確保する 3 仮説:

- `h_ml_eq : ∀ u ∈ sortedSettling, u.minLayer = minML`（settling filter より自明）
- `h_min_fu : ∀ v ∈ floatingUnits s, v.minLayer ≥ minML`（`foldl_min_fu_le_init/_le_mem` + `hfus.head?` 分岐）
- `h_ps_layer : ∀ q ∈ settlingPos, q.layer ≥ minML`（`minLayer_le_layer` + 上記）

これらで `pin_landing_groundingEdge_false_left/right` の前提
「∀ q ∈ settlingPos, q.layer ≥ p.layer」が満たされる（p ∈ settling ⇒ p.layer = minML）。
ただし `landingDistance (pin p) obs` を d に補正する追加補題が必要:

```lean
-- 要証明（次セッション）
lemma landingDistance_eq_of_takeWhile_drop
    (u : FallingUnit) (obs : List Layer) (d : Nat)
    (h : d = landingDistance u obs ∨ ∃ group, u ∈ group ∧ ...) :
    landingDistance u obs = d
```

もしくは pin_landing_groundingEdge_false_* 側で d を任意パラメータ化した版を作成（より汎用的）。

**ケース 2: u = cluster ps（Step B3b 本体で処理）**

cluster 着地位置には cluster 原象限が書かれ、canFormBond が保存される。
B3b `placeLDGroups_groundingEdge_mono`（未実装）を induction で構築:

- `placeLDGroups.induct` で group 単位に分解
- 各 group step で B3a mixed (`foldl_placeFU_mixed_fixed_d_groundingEdge_mono`) を適用
- cluster canFormBond は `s` ベース評価 → obs' 更新で不変
- cluster 着地位置と pin 着地位置の disjoint 性は positions Nodup で保証

**h_seed_landing の構築方針**: 既に `placeLDGroups_landing_nonEmpty` で閉じ済（Step 0.2 ✅）。

**実装ステータス**（2026-04-23 第43報）:
- ✅ scaffold の 3 補助仮説 `h_ml_eq` / `h_min_fu` / `h_ps_layer` を `ProcessWave.lean` 本体内で事前計算
- ✅ `foldl_min_fu_le_init` / `_le_mem` を `CommExt/FloatUnits.lean` に public 昇格
- ⏳ pin 側 d 補正補題（上記）
- ⏳ cluster 側 B3b 本体実装

---

## 撤退基準（継承）

- 3 セッション or 8 アプローチ失敗 → S1 は axiom 維持を検討、T-4b（S3 axiom 除去）へ pivot
- 撤退判断の前に必ず以下 3 ステップ: (1) `lean-proof-planning` SKILL 読み → (2) REPL で sorry-skeleton + ゴール確認 → (3) `lean-goal-advisor` エージェント呼び出し

---

## マイルストーン（主要補題のみ）

| 日付 | 追加補題（代表） |
|---|---|
| 2026-04-21 | `waveStep_nonGroundedLayerSum_lt` axiom→sorry、telescoping 基盤補題群 |
| 2026-04-21 | `pin_singleton_landing_empty` (#4) / `isOccupied_placeQuarter_mono` / `foldl_placeQuarter_written_canFormBond` |
| 2026-04-21 | `sum_map_layer_landing_telescope` / `landing_sum_bound_var_d` (#9) |
| 2026-04-21 | `Shape.groundedPositions_placeLDGroups_subset` / `GroundedMono.lean` 新設 |
| 2026-04-21 | `ProcessWave.lean` 新設（sorry 移設）+ `placeLDGroupsLandings_sum_succ_le` |
| 2026-04-21 | `groundingEdge_false_of_empty_quarter*` / `pin_landing_groundingEdge_false_*` (#6 Step A) |
| 2026-04-21 | `foldl_placeQuarter_written_getQuarter_canFormBond` (cluster seed bridge) |
| 2026-04-21 | `waveStep_grounding_mono` 独立補題化（sorry 1→2） |
| 2026-04-22 | `ngsWeight_placeLDGroups_of_ne_le` / `waveStep_layerCount_eq` / `landing_sum_allValid_le` |
| 2026-04-22 | Gravity 層へ canFormBond/isGroundingContact mono ヘルパー移設 |
| 2026-04-22 | Step B1/B2 cluster (`placeFallingUnit_cluster_groundingEdge_mono` / `_written_getQuarter_canFormBond`) |
| 2026-04-22 | Step B1 pin (`placeFallingUnit_pin_groundingEdge_mono`) |
| 2026-04-22 | Step B3a cluster-only / pin-only / **mixed** (`foldl_placeFU_*_fixed_d_groundingEdge_mono`) |
| 2026-04-22 | **`waveStep_ngs_strict_bound` 完了**（Step C3 telescoping 組立）— 残 sorry 1 件（本補題） |
| 2026-04-22 | **Step B4 scaffold 試作**（`Shape.groundedPositions_placeLDGroups_subset` 呼出を直接組立る形を確認）— sorry 2 分解は保留、持続性課題を Step B3b 仕様に反映 |
| 2026-04-22 | **Step B4 scaffold REPL 再検証**（第37報）— `set` 束縛 + `apply` 経由で型チェック通過を再確認。`h_edge_landing` / `h_seed_landing` のゴール state を REPL で確定。Step 0.2 `placeLDGroups_landing_nonEmpty` のシグネチャも型チェック通過 |
| 2026-04-22 | **Step 0.2 完了**（第38報）— `placeLDGroups_landing_nonEmpty` 証明、補助 7 補題 (`floatingUnits_quarter_nonEmpty`, `foldl_placeFU_isOccupied_mono`, `isOccupied_placeLDGroups_mono`, `foldl_placeQuarter_written_getDir_ne_empty`, `isOccupied_of_getDir_ne_empty`, `getDir_ne_empty_of_isOccupied`, `foldl_placeFU_written_isOccupied`) を `CommExt/PlaceGrounding.lean` 末尾に追加。ビルド成功 |
| 2026-04-23 | **R-1 / R-2-1 / R-2-2 完了** — chain 補題を `getDir ≠ empty` 形に統一 (`foldl_placeFU_getDir_ne_empty_mono`, `placeLDGroups_getDir_ne_empty_mono`, `foldl_placeFU_written_getDir_ne_empty`)。bridge (`isOccupied_iff_getDir_ne_empty` + 片側 2 本) を `Defs.lean` (isOccupied 定義直後) へ昇格。ビルド成功（sorry 件数不変）|
| 2026-04-22 | **Step B4 scaffold 反映**（第39報）— `ProcessWave.lean` の `waveStep_grounding_mono` 本体を `Shape.groundedPositions_placeLDGroups_subset` 展開形に変換。`h_seed_landing` を `placeLDGroups_landing_nonEmpty` で構成的に閉じ、残 sorry は `h_edge_landing` 枝 1 点に集約（Step B3b 完了で解消）。ビルド成功 |
| 2026-04-22 | **h_edge_landing 戦略再設計**（第40報）— Pin 着地での result 側 canFormBond=false 構造に基づき、cluster/pin 両側 vacuous 化が必要かつ可能と判明。新補助補題 `placeLDGroupsLandings_isOccupied_obs_false` を Step B3b-α として設定。詳細分析は `/memories/session/waveStep-h-edge-landing-analysis.md`。sorry 本体は未変更（戦略確定のみ） |
| 2026-04-23 | **α1/α4 反例発見・戦略再検討**（第42報）— REPL で具体 shape (pin at (2,ne) surrounded by settling cluster u1) を構築し α1・α4 共に FALSE と確定。`Scratch/commands-s1-alpha1-counter-05.jsonl` / `-06.jsonl`。新戦略は edge 型場合分けへ転換予定。**α3 `foldl_placeFU_isOccupied_antimono` のみ実装・ビルド通過** — CommExt/PlaceGrounding.lean 末尾、contrapositive of `foldl_placeFU_getDir_ne_empty_mono`。将来の rest case 持続性用。sorry 件数不変 |

> 詳細コミット履歴: `git log --oneline S2IL/Operations/Gravity/`

---

## 関連資料

- 計画: [`docs/plans/s1-proof-plan.md`](../../../docs/plans/s1-proof-plan.md)
- Gravity 全体計画: [`docs/plans/gravity-proof-execution-plan.md`](../../../docs/plans/gravity-proof-execution-plan.md)
- 構造化: [`sorry-plan.json`](../sorry-plan.json)
- 自動生成ビルド状態: [`sorry-goals.md`](../sorry-goals.md)
