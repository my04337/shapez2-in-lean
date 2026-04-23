# Sorry Card: `placeLDGroups_landing_groundingEdge_mono`

> 最終更新: 2026-04-23（**第58報: 撤退判断 — 第56/57報の戦略崩壊確認**。保存補題 `landingDistance_foldl_placeFU_preserve_on_remaining` (L1054) と aux の IH 不変量 `h_sorted'` (L1372) の両方が `lean-theorem-checker` により valid Shape 反例確定。**aux の IH 構造自体が不健全**であり、第56報で導入した `h_sorted` スレッディングも解体が必要。コード変更なし、`lake build` green 維持 (sorry 2 据置)。次セッションは 4 つの pivot 候補から選定。詳細は下記 🚨 第58報セクション。）
> 位置: `S2IL/Operations/Gravity/GroundedMono.lean:1054` (scaffold preserve, **REFUTED**)、同 `:1110` (helper d'=1, h_sorted に依存)
> スコープ: `private theorem`（`namespace Gravity` 内、aux の補助）
> ステータス: 🔴 **STEP B3b — 撤退判断 / 戦略全崩壊 / pivot 選定待ち**

## 🚨 第58報 反例サマリ（2026-04-23）

### 反例 1: 保存補題 L1054 (`landingDistance_foldl_placeFU_preserve_on_remaining`)

**判定**: FALSE (`lean-theorem-checker` 機械検証済)

**具体例** (7 layers):
- `v = w = cluster [(6,se),(5,se),(5,sw),(4,sw)]` (2x2 cluster, minLayer=4)
- `u = pin(4, se)` (minLayer=4, 孤立)
- `obs = [(0,sw)]` (床 sw のみ occupied、他は全空)
- `LD w obs = 3`, `LD u obs = 4`, sortedSettling = `[w, u]` (昇順 OK)
- `d = 3`, `group = [w]`, `remaining = [u]`
- `obs' = placeFU s obs w 3` が `(q.layer - 3, q.dir)` に書込 → `(2, se), (2, sw), (3, se), (1, sw)` 追加
- **`LD u obs' = 1 ≠ 4 = LD u obs`**（u の d=1 check `(4-1-1, se)=(2,se)` が obs' で occupied）

**反例検証**: `lean-theorem-checker` エージェントによる機械検証（`#eval` で各 LD 値確認、Shape 構築含む）。再現時は上記シェイプ・FU 構成をエージェントに渡すこと。

**原因**: `obs` が抽象 `List Layer` の場合、w の cluster 書込が u の check path に偶然衝突する可能性を排除できない。`floatingUnits_positions_pairwise_disjoint` は *生の位置の disjoint* しか保証せず、*shift 後の位置衝突*は排除しない。

### 反例 2: aux の IH 不変量 `h_sorted'` (L1372)

**判定**: FALSE（valid Shape で実現可能）

**具体例** (5 layers, `lean-theorem-checker` による機械検証済):
- Shape:
  | Layer | ne | se | sw | nw |
  |---|---|---|---|---|
  | L0 | R | R | – | – |
  | L1 | R | – | – | – |
  | L3 | pin(w) | pin(a) | R | R |
  | L4 | R | – | – | R |
- `floatingUnits s = [b, w, a]`（全員 minLayer=3）
  - `w = pin(3, ne)`（孤立）
  - `a = pin(3, se)`（孤立）
  - `b = cluster {(3,sw),(3,nw),(4,nw),(4,ne)}`（4連結）
- `LD w obs = 1`, `LD a obs = 2`, `LD b obs = 2` → sortedSettling = `[w, a, b]`（昇順）
- `d = 1`, `group = [w]`, `remaining = [a, b]`
- `obs'` で `(3-1, ne) = (2, ne)` が occupied（w pin 書込）
- `LD a obs' = 2`（se 方向、w 書込と無関係）
- `LD b obs' = 1`（b の (4, ne) が d=1 で (2, ne) に衝突）
- **`Pairwise (LD · obs' ≤ LD · obs') [a, b] = false`**（2 ≤ 1 失敗）

**原因**: 同一 minLayer の disjoint FU は「孤立 pin 複数 + cluster」パターンで 3 個以上作れる。group 配置が remaining 内の特定 FU のみに大きく影響し、順序が壊れる。

## 🧭 Pivot 候補（次セッション選定）

| # | 方針 | 利点 | 欠点 | 難易度 |
|---|---|---|---|---|
| **1** | aux の IH から `h_sorted` 完全除去。helper の d'=1 closure を h_sorted 非依存な経路（nodup + disjoint）で再構成 | 既存 scaffold 構造（`_step_generic`, `_aux`）を保持。範囲が局所 | d'=1 の厳密な disjoint 議論に新規補題が必要 | 中 |
| **2** | obs 抽象化を捨て `obs = (s.clearPositions ps).layers` 形式へ特化。ps を累積しながら再帰 | `clearPositions` の disjoint 補題群が使える | ps 累積不変量の記述量が急増、`_step_generic` の現行設計を大幅改修 | 高 |
| **3** | `placeLDGroups` 自体を「毎ステップ再ソート」定義へ改修 | 数学的にはクリーン | S2/S3 他 sorry・ProcessWave など全所に影響、range 広範 | 超高 |
| **4** | `placeLDGroups_landing_groundingEdge_mono` を axiom 化、S2 作業へ進む | 即進捗。pivot-1/2 の模索時間を確保 | 根本解決を先送り | 低 |

**推奨**: pivot-1（h_sorted 除去）を第 1 候補に、失敗時 pivot-4（axiom 化）で S2 に進める 2 段構え。

## 🛠️ 次セッション最短経路（pivot-1 選択時）

1. **lean-proof-planning SKILL.md 必読**
2. **helper `placeLDGroups_remaining_head_pin_landing_empty` の signature から `h_sorted` を除去**（L1097-1099）
3. **helper 内 `rw [hd1]; sorry` 付近の `h_v_le_v'`, `h_v'_gt_v` 導出ブロック削除**（L1222-1231）
4. **d'=1 closure を新しい経路で構築**:
   - `LD v' obs' = 1` → 定義展開で `∃ p ∈ v'.positions, isOccupied obs' (p.layer - 2, p.dir) = true` または `p.layer ≤ 1`
   - その p が group 書込位置 `(q.layer - d, q.dir)` と一致する場合と、元々 obs にあった occupation の場合で場合分け
   - `h_nodup`（全 settling 位置の Nodup） + `floatingUnits_positions_pairwise_disjoint` で `p ∉ group.flatMap positions` を確立
   - group 書込由来の occupation は p が group 側 position から取られた可能性を nodup で排除
5. **aux 側も `h_sorted_rem_obs`/`h_sorted'` ブロック削除**（L1367-1379）、`h_sorted` パラメータを除去
6. **main theorem/ProcessWave caller の `h_sorted` 供給側も削除**（L190-205）、ただし `mergeSort` 自体は残す
7. 各段階で `lake build` で sorry 数・警告を監視

---

## 過去履歴（第57報以前）


> ステータス: 🟡 **STEP B3b — 保存補題 scaffold 抽出完了 / 本体証明と d'=1 closure が次の焦点**
> **Preflight**: `.github/skills/lean-build/scripts/extract-goal-context.ps1 -File S2IL/Operations/Gravity/GroundedMono.lean -Line 1054`

## 🚀 第57報 新スコアボード（2026-04-26）

| 項目 | 第56報 | 第57報 |
|---|---|---|
| sorry 件数 | 2 | 2（scaffold へ移動） |
| `lake build` | green | green |
| deprecation 警告 | 1 (`List.sorted_mergeSort`) | 0 |
| h_sorted' 閉鎖パス | tactic-level sorry | 保存補題 scaffold 経由で完全閉鎖 |
| 保存補題 signature | なし | `landingDistance_foldl_placeFU_preserve_on_remaining` 確立 |

### 残 sorry（2 件）

1. **L1054 `landingDistance_foldl_placeFU_preserve_on_remaining` 本体**
   - ゴール: `landingDistance u obs' = landingDistance u obs` where `u ∈ dropWhile ...`
   - 意味: 第一グループ foldl 後の LD 保存（remaining 要素について）
   - 証明方針（次セッション）:
     1. `h_sorted` から `LD u obs ≥ d + 1`（dropWhile 性＋pairwise）を導出
     2. `h_min_fu` の対称性から settling 共通 minLayer = v.minLayer を導出
     3. foldl の induction で各 group step の `placeFallingUnit` が u の check path に触れないことを示す
     4. `landingDistance.check` の recursion induction で isOccupied 不変 ⇒ check 値不変を示す
   - 中核となるのは `placeFallingUnit` の書込位置 `(q.layer - d, q.dir)` と u の check 走査位置 `(p.layer - d', p.dir)` (p ∈ u.positions, d' ≤ LD u obs - 1) の layer/dir disjoint 性

2. **L1110 `placeLDGroups_remaining_head_pin_landing_empty` d'=1 closure**
   - ゴール: `isOccupied obs (p.layer - 1) p.dir = false` (hd1: LD v' obs' = 1 時)
   - **注意**: `LD (pin p) obs' = 1` だけからは landing 位置の empty は直接出ない（landingDistance の定義が「below = layer - d - 1 が occupied」を triggeringconditionとするため）。したがって
     保存補題 `landingDistance_foldl_placeFU_preserve_on_remaining` + obs 側の情報（`h_pin_inv` もしくは隣接位置 occupation の詳細議論）を組合せる必要あり
   - 利用可能: `h_v'_gt_v : LD v obs < LD v' obs`, `h_pin_inv`（第一グループ pin の obs 着地 empty）, `h_v'_ld_ne : LD v' obs ≠ LD v obs`, `h_v'_in_rest : v' ∈ rest`
   - 戦略候補:
     (a) 保存補題で `LD (pin p) obs = 1` を得て、対応する pin_singleton d_one 系補題を obs 側に適用後、obs → obs' の isOccupied 保存で持ち上げ
     (b) 保存補題で pin p の minLayer = v'.minLayer から `p.layer ≥ v.minLayer` などの boundary を導出し、書込位置 `(q.layer - d, q.dir)` (q ∈ first-group) と `(p.layer - 1, p.dir)` の disjoint 性から直接導出

### 次セッション最短経路

1. **lean-proof-planning SKILL.md 必読**（撤退判断ルール準拠）
2. **scaffold 補題 L1054 の証明**:
   - REPL で `example` として sorry-skeleton を展開、ゴール形を確認
   - `landingDistance.check` の recursion で `isOccupied` 不変性を示す補助補題を先行準備
   - `placeFallingUnit` の書込位置分布（`isOccupied_placeFallingUnit_eq_of_ne` 系の既存補題）を流用
3. **helper d'=1 closure L1110**:
   - 保存補題が閉じれば `LD (pin p) obs' = LD (pin p) obs` が使える
   - d'=1 なので `LD (pin p) obs = 1` → 対応する pin_singleton_landing_empty 系で obs 側 empty
   - `isOccupied obs → obs'` の保存（これも別途必要）で obs' 側に持ち上げ

---

## 過去履歴（第56報以前）


> 最終更新: 2026-04-26（**第56報: 方針 A scaffold 完了**。`h_sorted : Pairwise (LD a obs ≤ LD b obs)` を aux / helper / main / ProcessWave caller の 4 階層全てにスレッディング。`h_sorted` 追加により helper 内部で `d' = 1 ⇒ LD v' obs > 1` の下準備 (`h_v_le_v'`, `h_v'_gt_v`) を導出済み。`ProcessWave.lean` caller は `List.sorted_mergeSort` から `List.Pairwise` を構築。`lake build` green、sorry 2 件: (1) helper d'=1 本体 closure (GroundedMono.lean:1063, `rw [hd1]; sorry`), (2) aux 内 `h_sorted'` (= remaining.Pairwise on `obs'`; GroundedMono.lean:1213)。次セッションは write-outside 補題 `foldl_placeFU_landingDistance_preserve_of_outside` を整備して両 sorry を同時に閉じる方針。第55報: `placeLDGroups_remaining_head_pin_landing_empty` の d' ≥ 2 ケースを閉鎖（`landingDistance_not_occupied_at_landing` 一発）。

| 項目 | 第55報 | 第56報 |
|---|---|---|
| sorry 件数 | 1 | 2（scaffold 化のため一時増） |
| `lake build` | green | green |
| `h_sorted` 供給パス | 未 | ProcessWave → main → aux → helper 全通 |
| helper d'=1 下準備 | なし | `h_v'_ld_ne`, `h_v_le_v'`, `h_v'_gt_v` 導出済 |
| 反例リスク | abstract obs で FALSE | `h_sorted` により TRUE (運用系と整合) |

### 残 sorry（2 件）

1. **L1063 `placeLDGroups_remaining_head_pin_landing_empty` d'=1 closure**
   - ゴール: `isOccupied obs (p.layer - 1) p.dir = false` (hd1: d' = 1 時)
   - 利用可能: `h_v'_gt_v : LD v obs < LD v' obs`, `h_pin_inv`（第一グループ pin の obs 着地 empty）, `h_v'_ld_ne : LD v' obs ≠ LD v obs`
   - 不足: `p.layer - 1 = p.layer - LD v obs` 相当の index 対応、かつ `p.layer - LD v obs < obs.length` 等の boundary
2. **L1213 `h_sorted'` IH 保存 (aux)**
   - ゴール: `remaining.Pairwise (fun a b => LD a obs' ≤ LD b obs')`
   - `h_sorted : (v::rest).Pairwise (…on obs)` と `remaining ⊆ (v::rest)` から obs 版は自明
   - 不足: obs → obs' への LD 値保存。新規補助 `foldl_placeFU_landingDistance_preserve_of_outside (s group obs d u) (h_ps_outside : u.positions ∩ group.flatMap … = ∅) : LD u (foldl placeFU _ group obs d) = LD u obs`

### 次セッション最短経路

1. **lean-proof-planning SKILL.md 必読**（撤退判断ルール準拠）
2. **REPL sorry-skeleton 確認**: L1063 / L1213 のゴール実機確認
3. **write-outside preservation 補題** `foldl_placeFU_landingDistance_preserve_of_outside` を新規整備
   - これ 1 本で `h_sorted'` (L1213) 即閉じ
   - helper (L1063) の d'=1 closure は別途 boundary 議論が必要だが、同補題がベース
4. **helper d'=1 closure**: `h_pin_inv` の index `p.layer - d₀` (d₀ = LD v obs = 1) を利用し、`p.layer - 1 = p.layer - d₀` で obs 側 empty を取り、write-outside で obs' 側に持上げ

---

## 過去履歴（第55報以前）


> 位置: `S2IL/Operations/Gravity/GroundedMono.lean:1143`（**`placeLDGroups_remaining_head_pin_landing_empty` 内部 d' = 1 分岐の sorry**）
> スコープ: `private theorem`（`namespace Gravity` 内、aux の補助）
> ステータス: 🟡 **STEP B3b — d' ≥ 2 閉鎖 / d' = 1 残存、要 sort-by-LD hypothesis 追加**
> **Preflight**: `.github/skills/lean-build/scripts/extract-goal-context.ps1 -File S2IL/Operations/Gravity/GroundedMono.lean -Line 1143`

## ⚡ 次セッション最短経路（2026-04-23 第54報で scaffold 抽出完了）

`_step_generic` (GroundedMono.lean:902)、aux-lemma `placeLDGroups_landing_groundingEdge_mono_aux`、
および独立した補助 `placeLDGroups_remaining_head_pin_landing_empty` (L1063) の 3 補題が揃い、
本体 theorem `placeLDGroups_landing_groundingEdge_mono` (L1153 付近) は完全な term-mode 委譲チェーンになっている。
残る唯一の sorry は `placeLDGroups_remaining_head_pin_landing_empty` 内部。

**残課題**: 1 LD-グループを `obs` に foldl-place した結果 `obs'` 上で、残りリスト dropWhile の
先頭グループ pin `p` の着地位置 `(p.layer - landingDistance v' obs', p.dir)` が `obs'` 上で空であることを示す。

**証明戦略（2 ケース分け）**:

| ケース | 戦略 | 主要補題 |
|---|---|---|
| `d' := landingDistance v' obs' ≥ 2` | `landingDistance_not_occupied_at_landing` を `obs'` に直接適用 | `landingDistance_not_occupied_at_landing`, `floatingUnits_minLayer_ge_one` |
| `d' = 1` | first-group cluster 着地位置と `(p.layer - 1, p.dir)` の disjoint 性 → obs' 値 = obs 値 → `h_pin_inv` の隣接位置議論 | 新規補題 `foldl_placeFU_isOccupied_of_outside_writes`（要新設）+ minLayer 昇順 sort 性 |

**推奨手順**:
1. **lean-repl skill で sorry skeleton + ゴール表示確認**（先頭 30 行のシグネチャを実装と照合）
2. **lean-counterexample で d=1 命題真偽確認**（4-layer 系で disjoint 性反例検索）
3. **d ≥ 2 ケースを先に閉じて部分前進**: `pin p ∈ floatingUnits s` を `_h_sub` + dropWhile sublist で導出 → `landingDistance_not_occupied_at_landing` 適用
4. **d = 1 ケース**: 新規 disjoint 補題の整備が必要なら別補題として scaffold 化し再帰的に進める
5. **撤退ゲート**: d=1 ケースで disjoint 補助補題が 3 アプローチ失敗したら撤退判断（lean-proof-planning skill 読み → REPL ゴール確認 → lean-goal-advisor の 3 ステップ後）

**完了済（第54報まで）**:
1. ✅ `_step_generic` (obs 抽象、I1/I2 hypothesis 化) — 0-sorry
2. ✅ aux-lemma `_aux` — case1 vacuous + case2 で `_step_generic` 適用 + IH 三分岐
3. ✅ I1' (`obs'.length ≥ s.layerCount`) を `foldl_placeFU_fixed_length_ge` で再確立
4. ✅ main theorem を aux 委譲版へリファクタ（I2 は `pin_singleton_landing_empty` で供給）
5. ✅ `ProcessWave.lean` caller の `h_nodup` 供給（`mergeSort_perm` + `Perm.flatMap`）
6. ✅ **第54報**: I2' 再確立を独立 private theorem `placeLDGroups_remaining_head_pin_landing_empty` (L1063) に抽出。aux は同補題に term-mode で委譲。残 sorry は新補題内部の証明のみ

**撤退ゲート**: 内部証明が 3 アプローチ失敗したら axiom 維持に切替、T-4b へ pivot。

---

## クイックスタート（必読 / 30-50 行）

### ゴール（要約）

```lean
theorem placeLDGroups_landing_groundingEdge_mono
    (s : Shape) (sortedSettling : List FallingUnit) ...
    (a b : QuarterPos) (h_edge : groundingEdge s_obs a b = true)
    (h_landing : (a.layer, a.dir) ∈ placeLDGroupsLandings ... ∨ ...) :
    groundingEdge s_result a b = true
```

宣言全体: `GroundedMono.lean:976`（symbol-map.jsonl で `endLine` 確認可）

### 🚨 第49報で発見した scaffold の構造的障害

現 scaffold の冒頭:
```lean
revert h_obs h_result h_landing h_edge s_obs s_result a b
generalize (s.clearPositions settlingPos).layers = obs0
induction sortedSettling, obs0 using placeLDGroups.induct s generalizing s_obs s_result
```

この `generalize` で obs0 は任意の `List Layer` になる。case2 の induction 変数 `obs` に対し
B3a mixed (`foldl_placeFU_mixed_fixed_d_groundingEdge_mono`) の 6 前提のうち **3 つが証明不能**:

| 前提 | 障害 |
|---|---|
| **h_layer_lt** `q.layer < obs.length` | `q ∈ u.positions, u ∈ floatingUnits s` から得られるのは `q.layer < s.layerCount`。`obs.length = s.layerCount` は clearPositions 起源の情報なので generalize 後は消失 |
| **h_pin_landing_empty** `isOccupied obs (p.layer - d) p.dir = false` | `pin_singleton_landing_empty` (d=1 ケースは `isOccupied_clearPositions_of_not_mem` 依存) は obs = `(s.clearPositions ps).layers` を要求。任意 obs では d=1 反例あり |
| (関連) `obs.length = s.layerCount` 維持 | placeFallingUnit_length_ge により length は増加し得るため foldl 後の obs' でも等号は不成立 |

→ **Plan A (placeLDGroups.induct 直接版) は motive 固定のため obs 情報を保持できない。抜本的再設計が必要**。

### 次アクション（sorry-plan.json `next_actions` も参照）

**推奨: 案 3 pivot — step lemma + 長さ帰納（step lemma は 2026-04-23 第50報で完了）**

1. ✅ **Step lemma `placeLDGroups_landing_groundingEdge_mono_step` を 0-sorry で証明済**
   （GroundedMono.lean:934-1075、2026-04-23 第50報）。
   シグネチャ: `(s group settlingPos d) (h_sub h_min_fu h_ps_layer h_fixed_d h_group_nodup)
   (s_obs s_mid) (h_obs : ... = clearPositions ...) (h_mid : ... = foldl placeFU ...) (a b h_edge)
   → groundingEdge s_mid a b = true`。
2. **本補題再実装（残作業）**: `sortedSettling.length` の well-founded induction で step lemma を再帰適用。
   - 現 scaffold (generalize + placeLDGroups.induct) を丸ごと置き換える。
   - 各ステップで step lemma を `(s, group = takeWhile, settlingPos, d)` に適用して `s_obs → s_mid` を処理。
   - IH 呼び出し時、`s_mid.layers = foldl placeFU ... (clearPositions settlingPos).layers` のままでは
     clearPositions 形式が保たれないため、IH には **obs = foldl ... clearPositions 形式の一般化版** か、
     または **step lemma を main theorem 内で inline 再帰的に適用** する設計が必要。
   - ⚠️ 単純な settlingPos 拡張（settlingPos ++ landings）では obs が clearPositions 形式を保てない
     （placeFU は quarter を**書き込む**、clearPositions は**除去**する）。
     → 案 4'（invariant 強化）を採用: IH に `obs` の具体形を一般化して受け取る。詳細は [`sorry-plan.json`](../sorry-plan.json) の B3b-case2-pivot を参照。

3. **(fallback) 案 4: 周到 invariant**: placeLDGroups.induct の motive に `∃ ps, obs = foldl placeFU (clearPositions ps) ps' ∧ ...` を折り込む。

既に解消済み（参考）:
- ✅ s_mid 構築 (`⟨obs', h_obs'_ne⟩`)
- ✅ IH a 枝 (`Or.inl ha_rem`)
- ✅ IH b 枝 (`Or.inr hb_rem`)
- ✅ neither 枝 (`groundingEdge_placeLDGroups_of_ne`)
- ✅ **step lemma** `placeLDGroups_landing_groundingEdge_mono_step` (2026-04-23 第50報)

## 候補補題（extract-goal-context 事前抽出、2026-04-23）

| 補題 | シグネチャ（先頭 80 文字） | ファイル:行 |
|---|---|---|
| `Layer` | `where` | `S2IL/Shape/Layer.lean:32` |
| `placeLDGroupsLandings` | `(s : Shape) : List FallingUnit → List Layer → List (Nat × Direction) | [], _ ...` | `S2IL/Operations/Gravity/CommExt/PlaceGrounding.lean:400` |
| `groundingEdge` | `(s : Shape) (a b : QuarterPos) : Bool` | `S2IL/Operations/Gravity/Defs.lean:242` |
| `landingDistance` | `(u : FallingUnit) (obstacle : List Layer) : Nat` | `S2IL/Operations/Gravity/Defs.lean:845` |
| `placeFallingUnit` | `(origShape : Shape) (obstacle : List Layer) (u : FallingUnit) (dropDist : Nat...` | `S2IL/Operations/Gravity/Defs.lean:881` |
| `placeLDGroups` | `(origShape : Shape) (sorted : List FallingUnit) (obs : List Layer) : List Layer` | `S2IL/Operations/Gravity/Defs.lean:898` |
| `positions` | `: FallingUnit → List QuarterPos | cluster ps => ps | pin p => [p] / def minLa...` | `S2IL/Operations/Gravity/Defs.lean:442` |
| `floatingUnits` | `(s : Shape) : List FallingUnit` | `S2IL/Operations/Gravity/Defs.lean:461` |
### 直接使う補題（symbol-map.jsonl で sig 確認）

| 補題 | 役割 |
|---|---|
| `foldl_placeFU_mixed_fixed_d_groundingEdge_mono` | B3a mixed（1 group 分） |
| `pin_singleton_landing_empty` | pin landing empty on obs_k |
| `pin_landing_groundingEdge_false_left` / `_right` | pin 側 vacuous |
| `placeLDGroupsLandings_mem_exists_drop_ge_one_of_subset_fu` | landing → FU 還元（第二案） |

### 上流

- `Gravity.waveStep_grounding_mono` (`ProcessWave.lean:91`): 本補題完成で S1 全体完了

---

<details>
<summary>📚 詳細背景（戦略全文・反例検証・マイルストーン）</summary>

## 推奨実装順序（2026-04-23 第45報改訂）

### 🥇 第一案: `placeLDGroups.induct` 直接版（推奨）

本補題全体を `placeLDGroups.induct s` で induction し、各 step で
`placeLDGroupsLandings` と `placeLDGroups` を 1 段展開して閉じる。

**骨格**:
```lean
induction sortedSettling, obs_0 using placeLDGroups.induct s generalizing s_obs s_result with
| case1 obs => -- sorted = [] → landings は空、h_landing 矛盾で閉じる
| case2 obs v rest _ _ _ _ ih =>
    rw [placeLDGroupsLandings, placeLDGroups] at *
    -- h_landing を「現 group の landing か rest' の landing か」で分解
    -- 現 group → B3a mixed + pin_singleton_landing_empty で閉じる
    -- rest'   → obs' を新 s_obs として IH 適用
```

**利点**: pin 側の d-mismatch 問題を回避。既存の B3a mixed を各 step で直接使えるため新規補助補題がほぼ不要。

**ただし必要な中間補題候補**:
- **B3a-bridge**: `h_sub`, `h_min_fu`, `h_ps_layer` から `h_cluster_bond`, `h_pin_landing_empty`, `h_layer_ge`, `h_layer_lt`, `h_nodup` を導く補助。

---

### 🥈 第二案: `_subset_fu` 分解 + pin/cluster 場合分け

`placeLDGroupsLandings_mem_exists_drop_ge_one_of_subset_fu` で landing を FU に還元し `u` の型で場合分けする古典的アプローチ。

**課題**: pin 側の d-mismatch を解消するため以下の補助補題が追加で必要:

- **α (pin antimono)**: `landingDistance_antimono_of_isOccupied_ge`
  ```lean
  theorem landingDistance_antimono_of_isOccupied_ge
      (u : FallingUnit) (obs obs' : List Layer)
      (h_len : obs.length ≤ obs'.length)
      (h_mono : ∀ lay dir, lay < obs.length →
          isOccupied obs lay dir = true → isOccupied obs' lay dir = true) :
      landingDistance u obs' ≤ landingDistance u obs
  ```

- **β (pin path empty)**: `pin_path_isOccupied_false_in_clear`
  ```lean
  theorem pin_path_isOccupied_false_in_clear
      (s : Shape) (p : QuarterPos)
      (hp_fu : FallingUnit.pin p ∈ floatingUnits s)
      (h_min_fu : ∀ v ∈ floatingUnits s, v.minLayer ≥ p.layer)
      (ps : List QuarterPos)
      (h_ps_layer : ∀ q ∈ ps, q.layer ≥ p.layer)
      (d : Nat) (hd_ge : 1 ≤ d)
      (hd_le : d ≤ landingDistance (FallingUnit.pin p) (s.clearPositions ps).layers) :
      isOccupied (s.clearPositions ps).layers (p.layer - d) p.dir = false
  ```

---

## 証明戦略（補足）

### ケース 1: `u = FallingUnit.pin p'` (vacuous)

`u.positions = [p']` ゆえ `p' = p`。
戦略: `h_edge` に対し `groundingEdge s_obs a b = false` を exfalso で示す。
第一案: obs_k 側で `pin_singleton_landing_empty` + `groundingEdge_false_of_empty_quarter` → obs_k 側の edge = false を示し、IH + B3a mixed で s_obs 側に戻す。

### ケース 2: `u = FallingUnit.cluster ps` (B3b cluster 本体)

`foldl_placeFU_mixed_fixed_d_groundingEdge_mono` (B3a mixed) を `placeLDGroups.induct` で持ち上げる。

---

## 直接利用する補題（全量）

| 補題 | 役割 | ファイル |
|---|---|---|
| `placeLDGroupsLandings_mem_exists_drop_ge_one_of_subset_fu` | landing を FU に還元（第二案） | `CommExt/PlaceGrounding.lean:657` |
| `foldl_placeFU_mixed_fixed_d_groundingEdge_mono` | B3a mixed（1 group 分） | `GroundedMono.lean:800` |
| `pin_singleton_landing_empty` | obs_k 上の pin landing empty | `CommExt/LandingDist.lean:455` |
| `pin_landing_groundingEdge_false_left` / `_right` | pin 側 vacuous（d = 固定版） | `CommExt/LandingDist.lean:495` / `:517` |
| `foldl_placeFU_isOccupied_antimono` | obs_k → obs_0 bridge | `CommExt/PlaceGrounding.lean:1097` |
| `placeFallingUnit_cluster_groundingEdge_mono` | B1 cluster | `GroundedMono.lean:446` |
| `placeFallingUnit_pin_groundingEdge_mono` | B1 pin | `GroundedMono.lean:539` |
| `groundingEdge_false_of_empty_quarter` | edge=false の構築 | `CommExt/LandingDist.lean` 近辺 |

---

## 反例検証（継承）

- 主張相当テスト: 2L/3L 全列挙 + 4L/2-type, 4L/3-type PASSED
- α1/α4 戦略（2026-04-23 第42報）は反例で棄却 → 現戦略は pin/cluster 場合分け

---

## 撤退基準（継承）

- 3 セッション or 8 アプローチ失敗 → S1 は axiom 維持を検討、T-4b (S3 axiom 除去) へ pivot
- 撤退判断前に必ず: (1) `lean-proof-planning` スキル読み → (2) REPL で sorry-skeleton + ゴール確認 → (3) `lean-goal-advisor` エージェント呼び出し

---

## マイルストーン

| 日付 | 追加内容 |
|---|---|
| 2026-04-23 (第44報) | 本補題を新設（scaffold、sorry 1）。`waveStep_grounding_mono` から sorry 委譲。ビルド成功 |
| 2026-04-23 (第45報) | 推奨実装順序を改訂。`placeLDGroups.induct` 直接版を第一案（pin d-mismatch 回避）、`_subset_fu` + α/β を第二案。docstring に詳細戦略を同期 |
| 2026-04-23 (第46報) | **Plan A induction scaffold を実装**。case1 (sorted=[]) を vacuous で閉鎖、case2 に single sorry を集約。lake build OK (794 jobs)。sorry は GroundedMono.lean:1027 に移動 |
| 2026-04-23 (第47報) | 案 H 適用: 2 層構造化（クイックスタート 50 行 + `<details>` 詳細背景）。案 G の Preflight 行は前セッション (第47報) で追加済 |
| 2026-04-23 (第48報) | **case2 を 4 sub-goal に分解し 3 つ解消**。`set d/group/remaining/obs'` で定義展開 → `s_mid : Shape := ⟨obs', h_obs'_ne⟩` 構築 → `by_cases ha_rem/hb_rem` で 3 分岐 → IH a/b 枝を `ih ... (Or.inl/.inr _)` で閉鎖 → neither 枝を `groundingEdge_placeLDGroups_of_ne` + `layer_lt_of_isGroundingContact_left/right` で閉鎖。残 sorry は `h_edge_mid` (SUB-A, B3a mixed 適用) のみ。lake build OK (794 jobs)。sorry は GroundedMono.lean:1053 に移動 |
| 2026-04-23 (第49報) | **SUB-A 分析完了: Plan A scaffold の構造的障害を発見**。`generalize (s.clearPositions settlingPos).layers = obs0` により induction 変数 obs が「任意の List Layer」になり、B3a mixed 前提の 3 つが証明不能に。→ **案 3 (step lemma + 長さ帰納) へ pivot 推奨**。 |
| 2026-04-23 (第50報) | **Step lemma `placeLDGroups_landing_groundingEdge_mono_step` を 0-sorry で完全証明**。B3a mixed の 6 前提全て (`h_ne` / `h_cluster_bond` / `h_pin_landing_empty` / `h_layer_ge` / `h_layer_lt` / `h_group_nodup`) を `h_sub` / `h_min_fu` / `h_ps_layer` / `h_fixed_d` から組み立てて `foldl_placeFU_mixed_fixed_d_groundingEdge_mono` へ委譲。使用補題: `floatingUnits_cluster_positions_canFormBond`, `pin_singleton_landing_empty`, `landingDistance_le_minLayer`, `minLayer_le_layer`, `floatingUnits_positions_getQuarter`, `Shape.layerCount_clearPositions`。GroundedMono.lean:934-1075、lake build OK (794 jobs)。残 sorry は本補題本体のみ (行 1153、h_edge_mid)。次セッションは step lemma を長さ帰納で接続するだけ。 |
| 2026-04-23 (第51報) | **案 3 単純長さ帰納の構造的障害を crystallize**。step lemma の `h_obs : s_obs.layers = (s.clearPositions settlingPos).layers` 前提は再帰先 (foldl 後の obs') では満たせない（placeFU は書き込み、clearPositions は除去）。さらに d=1 pin 着地空性 (`pin_singleton_landing_empty_d_one_*`) が本質的に clearPositions 構造に依存。→ **案 3' aux-lemma 設計を確定**: (1) `placeLDGroups_landing_groundingEdge_mono_aux` (obs 抽象化 + 不変量 I1 `obs.length ≥ s.layerCount` + I2 `第一グループ pin 着地 empty on obs` を carry)、(2) step lemma obs 抽象版 `_step_generic` を追加、(3) 新規補題「foldl 後の残りリスト第一グループ pin 着地 empty 再確立」で I2' 再確立、(4) main theorem は aux に clearPositions 初期値を供給して呼出。Lean 変更なし（scaffold 内コメント更新のみ）、lake build 結果は前回と同じ 1-sorry。次セッションはこの設計を実装。 |
| 2026-04-23 (第52報) | **obs 抽象版 step lemma を実装**: `placeLDGroups_landing_groundingEdge_mono_step_generic` (GroundedMono.lean:902-954, 0-sorry) を新設し、I1 (`s.layerCount ≤ obs.length`) / I2 (`∀ p, FallingUnit.pin p ∈ group → isOccupied obs (p.layer - d) p.dir = false`) を明示的な hypothesis として切り出し。既存 `_step` を `_step_generic` への薄いラッパーへリファクタ（clearPositions 特化の I1/I2 導出部だけ残存）。main theorem の docstring を更新し、次セッションで必要な aux-lemma 実装経路を明示化。symbol-map.jsonl 更新済。sorry 1 維持、lake build OK (857 jobs)。 || 2026-04-23 (第54報) | **aux 内 I2' sorry を独立した補助補題 `placeLDGroups_remaining_head_pin_landing_empty` (private theorem, GroundedMono.lean:1063) として抽出**。signature は `(s, v, rest, h_sub, h_min_fu, h_nodup, obs, h_obs_ne, h_len_ge, h_pin_inv, v', rest', h_remaining, p)` を引数に取り、let-binder で `d`/`group`/`obs'` を導入した後 `takeWhile` membership → `isOccupied obs' (p.layer - LD v' obs') p.dir = false` を結論する形。aux の case2 では `fun v' rest' h_eq p hp => placeLDGroups_remaining_head_pin_landing_empty s v rest h_sub h_min_fu h_nodup obs h_obs_ne h_len_ge (h_pin_inv v rest rfl) v' rest' h_eq p hp` で `h_pin_inv'` を再確立。これにより aux は新補題への純粋な term-mode 委譲となり、残る数学的負担は新補題内部の証明 1 件に純化。docstring に 2 ケース分け戦略 (d≥2 / d=1) と必要な disjoint 補助補題候補を明記。sorry 1 維持、lake build OK。 |
---

## 関連資料

- 親カード: [`waveStep_grounding_mono.md`](./waveStep_grounding_mono.md)
- 計画: [`docs/plans/s1-proof-plan.md`](../../../docs/plans/s1-proof-plan.md)
- Gravity 全体計画: [`docs/plans/gravity-proof-execution-plan.md`](../../../docs/plans/gravity-proof-execution-plan.md)
- 構造化: [`sorry-plan.json`](../sorry-plan.json)
- 自動生成ビルド状態: [`sorry-goals.md`](../sorry-goals.md)

</details>


---

## ゴール

```lean
theorem placeLDGroups_landing_groundingEdge_mono
        (s : Shape) (sortedSettling : List FallingUnit)
        (settlingPos : List QuarterPos)
        (h_sub : ∀ u ∈ sortedSettling, u ∈ floatingUnits s)
        (h_min_fu : ∀ u ∈ sortedSettling, ∀ v ∈ floatingUnits s,
            u.minLayer ≤ v.minLayer)
        (h_ps_layer : ∀ q ∈ settlingPos, ∀ u ∈ sortedSettling,
            u.minLayer ≤ q.layer)
        (s_obs s_result : Shape)
        (h_obs : s_obs.layers = (s.clearPositions settlingPos).layers)
        (h_result : s_result.layers =
            placeLDGroups s sortedSettling (s.clearPositions settlingPos).layers)
        (a b : QuarterPos) (h_edge : groundingEdge s_obs a b = true)
        (h_landing :
            (a.layer, a.dir) ∈
                placeLDGroupsLandings s sortedSettling
                    (s.clearPositions settlingPos).layers ∨
            (b.layer, b.dir) ∈
                placeLDGroupsLandings s sortedSettling
                    (s.clearPositions settlingPos).layers) :
        groundingEdge s_result a b = true
```

## 上流（この補題を使う場所）

- `Gravity.waveStep_grounding_mono` (`ProcessWave.lean:91`): `h_edge_landing` 枝の唯一の供給源。
  本補題完成で S1 全体（`waveStep_nonGroundedLayerSum_lt`）が完了する。

---

## 推奨実装順序（2026-04-23 第45報改訂）

### 🥇 第一案: `placeLDGroups.induct` 直接版（推奨）

本補題全体を `placeLDGroups.induct s` で induction し、各 step で
`placeLDGroupsLandings` と `placeLDGroups` を 1 段展開して閉じる。

**骨格**:
```lean
induction sortedSettling, obs_0 using placeLDGroups.induct s generalizing s_obs s_result with
| case1 obs => -- sorted = [] → landings は空、h_landing 矛盾で閉じる
| case2 obs v rest _ _ _ _ ih =>
    -- placeLDGroups と placeLDGroupsLandings を展開
    -- 現 group = (v :: rest).takeWhile (LD == d)
    -- rest'   = (v :: rest).dropWhile
    -- obs'    = group.foldl placeFallingUnit obs
    rw [placeLDGroupsLandings, placeLDGroups] at *
    -- h_landing を「現 group の landing か rest' の landing か」で分解
    -- 現 group → B3a mixed (foldl_placeFU_mixed_fixed_d_groundingEdge_mono) で
    --           s_obs から s_mid (=.layers = obs') へ h_edge を伝播し、
    --           その後 IH で s_mid から s_result へ伸ばす
    -- rest'   → obs' を新 s_obs として B3a mixed で h_edge を伝播してから IH
```

**利点**:
- pin 側の d-mismatch 問題（`d = landingDistance (pin p) obs_k` vs obs_0）を回避。
  induction 内では obs_k がそのまま扱われ、`pin_singleton_landing_empty` を obs_k
  で直接適用できる（ただし前提 `h_min_fu`, `h_ps_layer` は obs_0 のまま維持）。
- cluster 側も同じ induction で一体化。
- 既存の B3a mixed (`foldl_placeFU_mixed_fixed_d_groundingEdge_mono`) を
  各 step で直接使えるため、新規補助補題がほぼ不要。

**ただし必要な中間補題候補**:
- **B3a-bridge**: 1 group 分の `foldl_placeFU_mixed_fixed_d_groundingEdge_mono`
  を使うのに必要な前提（`h_cluster_bond`, `h_pin_landing_empty`, `h_layer_ge`,
  `h_layer_lt`, `h_nodup`）を、現在の `h_sub`, `h_min_fu`, `h_ps_layer` から導く
  補助。特に `h_pin_landing_empty` は `pin_singleton_landing_empty` を group
  内 pin で適用する必要あり（group 内 FU の LD が等しいため `d = landingDistance (pin p) obs_k`
  が OK）。

---

### 🥈 第二案: `_subset_fu` 分解 + pin/cluster 場合分け

`placeLDGroupsLandings_mem_exists_drop_ge_one_of_subset_fu` で landing を FU に
還元し、`u` の型で場合分けする古典的アプローチ。

**課題**: pin 側の d-mismatch を解消するため以下の補助補題が追加で必要:

- **α (pin antimono)**: `landingDistance_antimono_of_isOccupied_ge`
  ```lean
  theorem landingDistance_antimono_of_isOccupied_ge
      (u : FallingUnit) (obs obs' : List Layer)
      (h_len : obs.length ≤ obs'.length)
      (h_mono : ∀ lay dir, lay < obs.length →
          isOccupied obs lay dir = true → isOccupied obs' lay dir = true) :
      landingDistance u obs' ≤ landingDistance u obs
  ```
  証明: `landingDistance.check` の recursion 上での induction（非自明）。

- **β (pin path empty)**: `pin_path_isOccupied_false_in_clear`
  ```lean
  theorem pin_path_isOccupied_false_in_clear
      (s : Shape) (p : QuarterPos)
      (hp_fu : FallingUnit.pin p ∈ floatingUnits s)
      (h_min_fu : ∀ v ∈ floatingUnits s, v.minLayer ≥ p.layer)
      (ps : List QuarterPos)
      (h_ps_layer : ∀ q ∈ ps, q.layer ≥ p.layer)
      (d : Nat) (hd_ge : 1 ≤ d)
      (hd_le : d ≤ landingDistance (FallingUnit.pin p) (s.clearPositions ps).layers) :
      isOccupied (s.clearPositions ps).layers (p.layer - d) p.dir = false
  ```
  証明: landingDistance の定義（着地までの路は空）+ `clearPositions` の定義
  （`p` は ps に含まれるので clear 済）の組合せ。`pin_singleton_landing_empty`
  (d = landingDistance 版) の一般化。

これらがあれば pin 側の vacuous 矛盾は機械的に閉じる。

---

## 証明戦略（補足）

### ケース 1: `u = FallingUnit.pin p'` (vacuous)

`u.positions = [p']` ゆえ `p' = p`。ゴールは (a 側着地の場合)
`groundingEdge s_result ⟨p.layer - d, p.dir⟩ b = true`。

戦略: `h_edge : groundingEdge s_obs a b = true` に対し、
`groundingEdge s_obs ⟨p.layer - d, p.dir⟩ b = false` を示して exfalso。

第一案: obs_k 側で `pin_singleton_landing_empty` + `groundingEdge_false_of_empty_quarter`
→ obs_k 側の edge = false を示し、IH と B3a mixed の組合せで s_obs 側に戻す。

第二案: 上記 α + β を使う。

### ケース 2: `u = FallingUnit.cluster ps` (B3b cluster 本体)

`foldl_placeFU_mixed_fixed_d_groundingEdge_mono` (B3a mixed) を
`placeLDGroups.induct` で持ち上げる。

- 各 group step で B3a mixed 適用 → `obs_k` が `obs_{k+1}` に更新
- cluster `canFormBond` は `s` ベース評価 → `obs_k` 更新で不変
- pin landing-empty は positions Nodup + 別 group 着地位置の disjoint 性で保存

---

## 直接利用する補題（シグネチャは `symbol-map.jsonl` 参照）

### 主要足場

| 補題 | 役割 | ファイル |
|---|---|---|
| `placeLDGroupsLandings_mem_exists_drop_ge_one_of_subset_fu` | landing を FU に還元（第二案） | `CommExt/PlaceGrounding.lean:657` |
| `foldl_placeFU_mixed_fixed_d_groundingEdge_mono` | B3a mixed（1 group 分） | `GroundedMono.lean:800` |
| `pin_singleton_landing_empty` | obs_k 上の pin landing empty | `CommExt/LandingDist.lean:455` |
| `pin_landing_groundingEdge_false_left` / `_right` | pin 側 vacuous（d = 固定版） | `CommExt/LandingDist.lean:495` / `:517` |
| `foldl_placeFU_isOccupied_antimono` | obs_k → obs_0 bridge | `CommExt/PlaceGrounding.lean:1097` |
| `placeFallingUnit_cluster_groundingEdge_mono` | B1 cluster | `GroundedMono.lean:446` |
| `placeFallingUnit_pin_groundingEdge_mono` | B1 pin | `GroundedMono.lean:539` |
| `groundingEdge_false_of_empty_quarter` | edge=false の構築 | `CommExt/LandingDist.lean` 近辺 |

---

## 反例検証（継承）

- 主張相当テスト: 2L/3L 全列挙 + 4L/2-type, 4L/3-type PASSED
- α1/α4 戦略（2026-04-23 第42報）は反例で棄却 → 現戦略は pin/cluster 場合分け

---

## 撤退基準（継承）

- 3 セッション or 8 アプローチ失敗 → S1 は axiom 維持を検討、T-4b (S3 axiom 除去) へ pivot
- 撤退判断前に必ず: (1) `lean-proof-planning` スキル読み → (2) REPL で sorry-skeleton
  + ゴール確認 → (3) `lean-goal-advisor` エージェント呼び出し

---

## マイルストーン

| 日付 | 追加内容 |
|---|---|
| 2026-04-23 (第44報) | 本補題を新設（scaffold、sorry 1）。`waveStep_grounding_mono` から sorry 委譲。ビルド成功 |
| 2026-04-23 (第45報) | 推奨実装順序を改訂。`placeLDGroups.induct` 直接版を第一案（pin d-mismatch 回避）、`_subset_fu` + α/β を第二案。docstring に詳細戦略を同期、次セッション向け骨格コードを追加 |
| 2026-04-23 (第46報) | **Plan A induction scaffold を実装**。`revert` + `generalize hobs_eq` で obs を自由変数化、`induction sortedSettling, obs0 using placeLDGroups.induct s generalizing s_obs s_result` で induction、**case1 (sorted=[]) を vacuous で閉鎖**（`simp [placeLDGroupsLandings] at h_landing`）、**case2 に single sorry を集約**。lake build OK (794 jobs)。sorry は GroundedMono.lean:1027 に移動 |

---

## 関連資料

- 親カード: [`waveStep_grounding_mono.md`](./waveStep_grounding_mono.md)
- 計画: [`docs/plans/s1-proof-plan.md`](../../../docs/plans/s1-proof-plan.md)
- Gravity 全体計画: [`docs/plans/gravity-proof-execution-plan.md`](../../../docs/plans/gravity-proof-execution-plan.md)
- 構造化: [`sorry-plan.json`](../sorry-plan.json)
- 自動生成ビルド状態: [`sorry-goals.md`](../sorry-goals.md)
