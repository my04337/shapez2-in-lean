# Gravity 証明計画（Phase D-10）

- 作成日: 2026-04-29
- 最終更新: 2026-04-29
- ステータス: **Phase D-10D セッション 2 完了。`Internal/Collision.lean` の §1 edge correspondence を axiom-free に閉じた。次は §2-§3 BFS 同値性 (`isGroundedFast_iff_isGrounded`)**
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
| §2 | `isGrounded_of_isGroundedFast` | ⬜ sorry |
| §2 | `isGroundedFast_of_isGrounded` | ⬜ sorry |
| §3 | `isGroundedFast_iff_isGrounded` | ⬜ 系（上 2 本に依存） |
| §4 | `structuralCluster_canFormBond` | ⬜ sorry |
| §4 | `structuralCluster_nonEmpty` | ⬜ sorry |
| §5 | `floatingClusters_eq_nil_of_isSettled` | ⬜ sorry |
| §5 | `floatingPins_eq_nil_of_isSettled` | ⬜ sorry |
| §5 | `floatingUnits_eq_nil_of_isSettled` | ⬜ ブリッジ axiom 解消の本命（§5 の合成） |
| §6 | `gravity_isSettled_collision` | ⬜ `gravity.isSettled` axiom 解消の本命 |

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

### 3.4 Internal — `BFS.lean`（実装済み）

汎用 BFS 骨格を Gravity 固有から分離: `listDedup` / `reachClosure {α} [DecidableEq α] (step) (init) (fuel)` / `horizontalAdj : QuarterPos → List QuarterPos`。

§2-§3 のため、追加 API 補題（**未実装**、次セッションで導入）:

- `mem_reachClosure_iff_exists_path`: `q ∈ reachClosure step init n ↔ ∃ p₀ ∈ init, ∃ k ≤ n, ReflTransGen' step p₀ q with k hops`
- `reachClosure_subset_succ`: 単調性
- `reachClosure_fixed_of_step_subset`: 不動点性（fuel 充足条件）

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

### Phase D-10D-3 / 4 / 5: BFS 同値性 → structuralCluster 不変 → ブリッジ theorem 化（次セッション以降）

§3.3 の §2 / §3 / §4 / §5 を順に証明。完了で axiom 25 → 24（`floatingUnits_eq_nil_of_isSettled` 解消）。

**作業順序**:

1. `Internal/BFS.lean` に §3.4 の API 補題 3 本を追加
2. `Internal/Collision.lean` §2 BFS soundness (`isGrounded_of_isGroundedFast`): `reachClosure` 上の fuel 帰納、各反復追加 `q` に対し `IsGroundingEdge` の `ReflTransGen` 拡張（§1.iff 経由）
3. §2 BFS completeness (`isGroundedFast_of_isGrounded`): `ReflTransGen` ホップ数 `n ≤ s.length * 4 + 4` から fuel 充足、ホップ数の帰納で reachClosure 到達
4. §4 `structuralCluster_canFormBond` / `structuralCluster_nonEmpty`: BFS 拡張が `canFormBond` を保つ
5. §5 `floatingClusters_eq_nil_of_isSettled` / `floatingPins_eq_nil_of_isSettled`: §3 + §4 合成
6. §5 `floatingUnits_eq_nil_of_isSettled`: 上 2 本より `unfold + rw + simp`。**ブリッジ axiom が theorem 化** → axiom 25 → 24

### Phase D-10D-6: `gravity.isSettled` 主証明

§3.3 §6 `gravity_isSettled_collision`: `dropOf` を 1 回計算した固定写像として扱い、配置後の全非空象限が `IsGrounded` であることを構成的に与える。障害物逐次更新は取らず、全代入位置を構成してから同時に論証する。完了で axiom 24 → 23。

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

---

## 6. 完了条件（残項目）

- [ ] §3.3 §2-§6 の sorry 解消
- [ ] `floatingUnits_eq_nil_of_isSettled` を theorem 化（axiom 25 → 24）
- [ ] `gravity.isSettled` を theorem 化（axiom 24 → 23）
- [ ] `gravity.rotateCW_comm` を theorem 化（axiom 23 → 22、Gravity 全消滅）
- [ ] `lake build` green、warning 0
- [ ] `S2IL/_agent/sorry-plan.json` の axioms[] から Gravity の 3 axiom が削除

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
