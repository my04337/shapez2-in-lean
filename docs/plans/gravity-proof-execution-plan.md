# Gravity 証明 — 実行計画

> 作成日: 2026-04-05
> 最終更新: 2026-04-20（S1-aux 構成的証明完了・axioms 4→3）

---

## 現状クイックリファレンス

> ビルド状態・sorry / axiom 件数は自動生成の [`S2IL/_agent/sorry-goals.md`](../../S2IL/_agent/sorry-goals.md) を参照。
> axiom 進捗・ next_actions は [`S2IL/_agent/sorry-plan.json`](../../S2IL/_agent/sorry-plan.json) を参照。

### 設計決定の記録（2026-04-20 アーカイブ — 読み取り専用）

#### 重大発見: FU 数減少定理は偽

`waveStep_floatingUnits_length_lt`（各 waveStep で FU 数が厳密減少する）は **偽** であることが判明。

- **反例形状** `testNoOverwrite`（10 レイヤ）: FU count 2→2→0
  - Layer 0: crystal NW（seed）、Layers 1-2: 空、Layers 3-9: settling cluster + pin at (7,NE)
  - Settling cluster が d=1 で着地するも非接地で残存、ピンも overwrite されず FU 数不変
- **反例形状** `testB2Counter`（9 レイヤ）: axiom `floatingUnits_waveStep_subset_nonSettling` が偽
  - s' の floating unit が fus.filter(nonSettling) に含まれない

#### 対策: nonGroundedLayerSum 測度への切替

**新測度**: `nonGroundedLayerSum(s) = Σ_{p: non-empty ∧ non-grounded} (p.layer + 1)`

**厳密減少の証明構造**:
1. 着地位置は obs 上で常に空（`landingDistance` の構造的保証: d=k で trigger する場合、d=k-1 では obs[L-k][D]=空）
2. Settling 位置は非接地 → clearing で接地パス不破壊
3. 各 settling 位置の純変化: -(L+1)+(L-d+1) = -d ≤ -1
4. 総変化 ≤ -d × |settlingPos| ≤ -1

**計算検証**: 2L/256, 3L/729, 4L/65536 全列挙テストで 0 failures


### 再利用可能な証明資産（axiom 除去で流用予定）

以下は Facade.lean に残存（`private`）: S3 の構成的証明で完成した補助補題群。

| 補題 | 役割 |
|---|---|
| `FallingUnit.rotateCW`, `positions_rotateCW`, `minLayer_rotateCW`, `typeOrd_rotateCW`, `sortGroup_rotateCW` | FU の rCW 作用 |
| `ofLayers_rotateCW`, `option_bind_normalize_rotateCW` | Shape 配管層の rCW 等変 |
| `isOccupied_rotateCW`, `landed_rotateCW`, `landingDistance_check_rotateCW`, `landingDistance_rotateCW` | landingDistance の rCW 不変 |
| `placeLDGroups_rotateCW`, `foldl_place_fixed_d_rotateCW` | placeLDGroups / fold の rCW 等変 |
| `floatingUnit_any_in_rotateCW` / `_rev` / `_cluster` / `_pin` | per-FU .any 双方向対応 |
| `floatingUnits_isEmpty_rotateCW`, `any_map_rotateCW_beq` | リスト・集合レベルの回転 |
| `foldl_min_fu_le_init`, `foldl_min_fu_eq_init_or_mem`, `foldl_min_fu_le_mem` | FU 版 fold-min |
| `minML_eq_rotateCW`, `settling_positions_any_rotateCW` | minML 不変 + settling 位置 .any 一致 |
| `beq_rotateCW_iff` | rotateCW 下の beq |

Equivariance.lean には `Direction.all_rotate180_perm`, `QuarterPos.allValid_rotate180_perm`
が残存（将来の rotate180 側 Perm 基盤の起点）。

### 次セッション方針（2026-04-20 最終更新）

**優先度 1: S1-new の構成的証明 — Sub-claim B + C**
- h_nodup (Sub-claim A): ✅ 完了（`allValid_nodup`, `allStructuralClustersList_nodup`, `floatingUnits_nodup`）
- S1-aux (`nonGroundedLayerSum_zero_fus_empty`): ✅ 完了（Equivariance.lean で構成的証明）
- Sub-claim B（settling 位置の性質）: 🔴 残課題
  - B1: 非 settling 位置のコンテンツ保存（`placeLDGroups` の書き込み範囲制限）
  - B2: settling 位置は非接地（`floatingUnits` 定義から直接）
  - B3: 着地位置は obs 上で空（`landingDistance` の構造的保証）
- Sub-claim C（算術証明）: 🔴 残課題（各 settling 位置の純変化 = -d ≤ -1、`Finset.sum_lt_sum` + `omega`）

**優先度 2: S3 の axiom 除去（P5 Perm 基盤）**
1. `allIsolatedPins_rotateCW_perm`, `allStructuralClustersList_rotateCW_perm`（テンプレ: `Direction.all_rotate180_perm`）
2. `floatingUnits_rotateCW_perm` — 上 2 つ + grounding filter の合成
3. `settling_rotateCW_perm : settling'.Perm (settling.map FU.rotateCW)` — Perm.filter 経由
4. `placeLDGroups_perm_within_LD` — 同一 LD の FU は位置重複なし（`placeFallingUnit_comm_of_layer_disjoint` 応用）
5. axiom を構成的定理に置換

**優先度 3: S2 の axiom 除去（S3 から 1 行導出）**
`Shape.rotate180_eq_rotateCW_rotateCW` + S3 で `simp only` 1 行（`crystallize_rotate180_comm` と同パターン）。
ただし S2 は現状 `Equivariance.lean`、S3 は `Facade.lean` なので、
導出時は S2 を `Facade.lean` に移動する（`processWave_rotate180_comm` / `process_rotate180` も併せて）。

---

## §1 残タスク

| # | 状態 | タスク | 推定工数 |
|---|---|---|---|
| T-4a | 🟡(進行中) | S1: axiom → sorry 化完了・`waveStep_ngs_strict_bound` 証明完了 (2026-04-22)・残 1 sorry `waveStep_grounding_mono` が最終ブロッカー（→ [`sorry-card`](../../S2IL/_agent/sorry-cards/waveStep_grounding_mono.md)） | — |
| T-4b | 🟡 | S3 axiom 除去（Perm 基盤構築 → 置換） | 2-3 s |
| T-4c | 🟡 | S2 axiom 除去（S3 から 1 行導出、配置移動） | 0.5 s |
| T-5 | 🟡 | 旧コード CommExt.lean 削減 | 2-3 s |

**推奨実施順**: T-4a（独立）→ T-4b → T-4c → T-5

### T-5 補足（旧コード残存状況）

| ファイル | 行数 | 状態 |
|---|---|---|
| ~~SettleFoldlEq.lean~~ | 11 | ✅ 削除済み |
| ~~FoldlBridge.lean~~ | 355 | ✅ 削除済み |
| ~~PermInvariance.lean~~ | 2,273 | ✅ 削除済み |
| CommExt.lean | 2,081 | ❌ 外部依存あり残存（Shatter/Cutter/Stacker/GroundedCore/GroundedPlacement が使用） |

CommExt.lean の削除には外部依存先への補題移動が必要。T-4 完了後に実施。

---

## §2 Task 4 詳細計画

> **ゴール**: `errors=0, warnings=0, sorries=0, axioms=0`
> **現状**: axioms=2（S2 + S3 が残存）。sorry 状況は [`S2IL/_agent/sorry-goals.md`](../../S2IL/_agent/sorry-goals.md)（自動生成）を参照。

### 残 axiom 概要

> sorry 状況は [`S2IL/_agent/sorry-goals.md`](../../S2IL/_agent/sorry-goals.md)（自動生成）を参照。

| # | 識別子 | ファイル | 性質 | 対応 |
|---|---|---|---|---|
| S2 | `waveStep_rotate180_comm` | Equivariance.lean | 等変性 (r180) | axiom（S3 から導出予定） |
| S3 | `waveStep_rotateCW_comm` | Facade.lean | 等変性 (rCW) | axiom（Perm 基盤で de-axiomatize 予定） |

### 依存関係

```
S1-new (nonGroundedLayerSum_lt) ──→ processWave 終端性 + S2/S3 の帰納ステップ
S1-aux (zero_fus_empty) ──→ processWave_floatingUnits_empty 基底ケース
S2 (r180 comm) ──→ processWave_rotate180_comm ──→ process_rotate180
S3 (rCW comm) ───→ processWave_rotateCW_comm ──→ process_rotateCW
```

S1 と S2/S3 は独立に解決可能。

---

### T-4a: S1 終了性 — nonGroundedLayerSum 測度

#### ★ 2026-04-20 更新: FU 数減少は偽、測度切替完了

旧アプローチ（`waveStep_floatingUnits_length_lt`: FU 数が各波で厳密減少）は
**偽定理** であることが判明。10 レイヤ反例で FU count 2→2 を確認。

新アプローチ: `nonGroundedLayerSum` 測度（非接地・非空位置の (layer+1) の合計）を使用。
理論的に厳密減少が保証され、計算検証で確認済み。

#### 現状

| 項目 | 状態 |
|---|---|
| `nonGroundedLayerSum` 定義 | ✅ Defs.lean に追加 |
| `waveStep_nonGroundedLayerSum_lt` | � sorry（証明進行中 — [`sorry-card`](../../S2IL/_agent/sorry-cards/waveStep_ngs_strict_bound.md) 参照） |
| `nonGroundedLayerSum_zero_fus_empty` | ✅ 構成的証明済み（Equivariance.lean:1596、対偶 + foldl 単調性下限） |
| `processWave` 終了性 | ✅ 新測度使用 |
| `processWave_floatingUnits_empty` | ✅ 新測度使用 |
| 旧 axiom/theorem 除去 | ✅ 完了 |

#### 除去した旧 axiom/theorem

| 識別子 | 種別 | 理由 |
|---|---|---|
| `floatingUnits_waveStep_subset_nonSettling` | axiom | **偽**（反例: testB2Counter 9L） |
| `floatingUnits_waveStep_le_nonSettling` | theorem | 偽 axiom 依存 |
| `waveStep_floatingUnits_length_lt` | theorem | **偽**（反例: testNoOverwrite 10L） |

#### 新 axiom の構成的証明方針（将来）

**`waveStep_nonGroundedLayerSum_lt`**: 3 段階の補題で構成
1. landing_positions_empty_in_obs: `landingDistance` の帰納構造から着地位置の空性
2. clearing_preserves_grounding: settling 位置の非接地性から接地パス不破壊
3. layer_sum_decrease: 各 settling 位置で -d ≤ -1 の純減少

**`nonGroundedLayerSum_zero_fus_empty`**: ✅ 2026-04-20 構成的証明済み
- 証明: 対偶（FU 非空 → sum > 0）+ `foldl_mem_ge_nat` + `floatingUnits_nonempty_implies_exists_ungrounded`
- 場所: Equivariance.lean:1596

---

### T-4b: S3 (`waveStep_rotateCW_comm`) axiom 除去

#### 証明戦略（P5 Perm 基盤）

非空分岐で以下を示す:

```
placeLDGroups s.rotateCW sorted' obs' = (placeLDGroups s sorted obs).map Layer.rotateCW
```

**段階 A**: `placeLDGroups_rotateCW`（完成済み）で map を外に出す。

**段階 B**（残課題）:
1. `settling_rotateCW_perm : settling'.Perm (settling.map FU.rotateCW)`
2. `placeLDGroups_perm_within_LD`（同一 LD グループ内 FU は位置重複なし → foldl 順序不変）

#### 必要な新規基盤

| 補題 | 目的 | 難易度 |
|---|---|---|
| `allIsolatedPins_rotateCW_perm` | Pin 列の Perm | ★★ |
| `allStructuralClustersList_rotateCW_perm` | クラスタ列の Perm（fold ベース BFS） | ★★★ |
| `floatingUnits_rotateCW_perm` | 上 2 つ + grounding filter の合成 | ★★ |
| `foldl_placeFU_fixed_d_perm` | 同一 LD の FU が位置重複なし → foldl 順序不変 | ★★★ |
| `placeLDGroups_perm_within_groups` | LD グループごとの Perm で結果同一 | ★★ |

#### 再利用可能な既存資産

Facade.lean / Equivariance.lean に残存する `rotateCW` / `rotate180` 等変補題群は
axiom 除去でそのまま使用可能。特に `settling_positions_any_rotateCW`, `minML_eq_rotateCW`
は Perm 版の前段 (.any レベル) として再利用できる。

**撤退基準**: 3 セッション超過時は `decide`/`native_decide` による計算的検証に転換、
または axiom を永続化して `#guard` ベースの検証で補う。

---

### T-4c: S2 (`waveStep_rotate180_comm`) axiom 除去

S3 の de-axiomatization が完了次第、`Shape.rotate180_eq_rotateCW_rotateCW` + S3 を
2 回適用する 1 行証明で置換:

```lean
theorem waveStep_rotate180_comm (s : Shape) :
        waveStep s.rotate180 = (waveStep s).rotate180 := by
    simp only [rotate180_eq_rotateCW_rotateCW, waveStep_rotateCW_comm]
```

パターン既出: `crystallize_rotate180_comm`, `paint_rotate180_comm`.

#### 実装メモ

- `waveStep_rotate180_comm` は現在 `Equivariance.lean` の axiom だが、導出時は
  `waveStep_rotateCW_comm`（Facade.lean）への依存が必要となる。
  `waveStep_rotate180_comm` / `processWave_rotate180_comm` を `Facade.lean` に移動する。
- `process_rotate180` は Facade.lean に既存、配置関係で影響なし。

---

### 成功基準

| 項目 | 基準 |
|---|---|
| ビルド状態 | errors=0, warnings=0, **sorries=0, axioms=0** |
| 制約なし | `layerCount ≤ 5` / `IsSettled` 等の仮説追加なし |
| 計算検証 | vanilla4/5/stress8 で waveStep 1 波あたり FU 減少を確認 |
| 後方互換 | `process_rotate180` / `process_rotateCW` の公開シグネチャ不変 |

---

## §3 Wave モデル概要

波動モデルは `iterate waveStep until floatingUnits = []` として定義される。

```
Wave Model:
  1. floatingUnits(shape) で不安定ユニットを特定
  2. 安定要素のみに接触する FU を即座に settle（接地化）
  3. 残りの FU を全て 1 レイヤ下に移動
  4. 安定するまで 2-3 を繰り返し
```

**ステップ 3 の発火条件**（2026-04-17 検証済み）: `placeAbove` + `shatterTopCrystals` により同一方角列に複数 FU が発生するとき（多数の結晶列が砕散する状況）に発火する。vanilla8 では結晶列が多い形状ほど発火頻度が高い。

**波数の上界**: 各 wave で ≥1 FU が settle → 波数 ≤ FU 数 ≤ maxLayers × 4（vanilla8 で ≤ 32）

### T-4/T-5 完了後の最終点検

| 確認項目 | 基準 |
|---|---|
| 冗長な場合分けの排除 | 構造的帰納法やジェネリック補題で代替可能か |
| 補題の一般性 | 不要な仮説がないか（`layerCount ≤ 5` 制約の不要化を確認） |
| 命名規約 | S2IL 固有ルール + Lean 4 / Mathlib 命名規則 |
| doc コメント | public def/theorem に日本語 `/-- ... -/` が付与されているか |

---

## 関連ドキュメント

| ドキュメント | 概要 |
|---|---|
| [MILESTONES.md](MILESTONES.md) | マイルストーン チェックシート |
| [偽定理カタログ](../s2il/false-theorem-catalog.md) | 棄却済みアプローチ・偽定理一覧 |
| [gravity-equivariance-analysis.md](../s2il/gravity-equivariance-analysis.md) | Gravity 証明の技術的知見 |
| [gravity-issettled-matrix.md](../s2il/gravity-issettled-matrix.md) | 全加工装置の gravity 利用・IsSettled 必要性マトリクス |
| [equivariance-proof-patterns.md](../s2il/equivariance-proof-patterns.md) | 等変性テーブル・証明パターン集 |

---

## Appendix A: axiom 除去履歴

全 5 件の axiom が構成的証明に置換済み（axiom = 0）。

| axiom 名 | ファイル | 除去方式 |
|---|---|---|
| `gravity_IsSettled` | Settled/GravityBridge.lean | iterate 終了条件 = `floatingUnits` が空 → 定義的に `IsSettled` |
| `all_grounded_settle_foldl` | Settled/GravityBridge.lean | `gravity_IsSettled` に包含され不要に（foldl モデル固有） |
| `process_rotate180_placeAbove_settled` | Stacker/Stacker.lean | `gravity_rotate180_comm` の無条件化により自明な系 |
| `process_rotateCW_placeAbove_settled` | Stacker/Stacker.lean | `gravity_rotateCW_comm` の無条件化により自明な系 |
| `IsSettled_liftUp_generatePins` | PinPusher/PinPusher.lean | pin 生成の接地性保存を BFS パスシフト構成で証明 |

**採用経緯**: sorry #4b（`all_grounded_settle_foldl` 内 pin NE コールバック）で 11 アプローチを消耗後 Plan B（axiom 化）を選択。Wave Gravity Model 導入により 5 axiom 中 4 件を構成的証明に置換。残 1 件（`IsSettled_liftUp_generatePins`）も BFS パスシフト証明で置換完了。

---

## Appendix B: 完了済み作業サマリ

### 主要完了項目

| 項目 | 内容 | 結果 |
|---|---|---|
| Wave Gravity Model 実装（Tasks 1-3） | `iterate waveStep until floatingUnits = []` + 終端性 + 等変性 | sorry=3 まで到達 |
| axiom 5 件除去 | 構成的証明への全置換 | axiom=0 |
| isGroundingContact バグ修正 | `groundingBfs` 探索辺を `isUpwardGroundingContact \|\| isStructurallyBonded` に修正 | sorry 6→2 |
| simp 安定化 | `lean --json` + `simp?` で 76 箇所を `simp only` / `simp_all only` 化 | 裸 simp=0 |
| 旧コード削減 | SettleFoldlEq + FoldlBridge + PermInvariance 削除 | -2,999 行 |
| rCW 等変性 + LayerPerm 統合 | rCW 重複を統合・ジェネリック化 | -128 行 |
| 証明品質リファクタリング | R-1〜R-14、F-1/F-3 完了 | |

### 確立済み計算検証結果

| 事実 | 根拠 |
|---|---|
| `process_rotate180` は ≤5L で真 | 合計 1,949,447+ shapes で 0 failures（1-4L 全数 + 5-16L サンプル） |
| `process_rotate180` は ≥6L で偽 | 6L 反例確認済み（Wave 7）。ゲーム内での到達は Stacker 前提で不可能 |
| `process_rotateCW` は真 | 65K+ shapes で 0 failures |
| `waveStep_floatingUnits_length_lt` は真 | vanilla4/5/stress8 で計算検証済み |

---

## Appendix C: Gravity モジュール構成

`S2IL/Operations/Gravity/` 以下のファイル:

| ファイル | 行数 | 役割 |
|---|---|---|
| `Defs.lean` | ~1,420 | コア定義（waveStep, processWave, placeLDGroups, landingDistance, floatingUnits）+ BFS インフラ・接地伝播補題群 |
| `Equivariance.lean` | ~1,960 | r180/rCW 等変性基盤証明 + waveStep/processWave 等変性 |
| `CommExt.lean` | ~2,081 | 配置可換性・拡張性基盤（T-5 削除候補、外部依存あり） |
| `Facade.lean` | ~536 | `process_rotate180/rotateCW` + 公開 API |
| `Gravity.lean` | — | 公開 import ラッパー |

### 各加工装置の gravity 利用パターン

| 加工装置 | gravity 利用 | layerCount ≤ 5? | 備考 |
|---|---|---|---|
| PinPusher | `truncated.gravity` | ≤ maxLayers ✅ | — |
| Stacker（1st gravity） | `afterShatter.gravity` | ≤ 2×maxLayers ❌ | IsSettled 仮説で対処済み |
| Stacker（2nd gravity） | `truncated.gravity` | ≤ maxLayers ✅ | — |
| Cutter / HalfDestroy / Swap | `settleAfterCut` 内 | ≤ maxLayers ✅ | — |
| Painter / CrystalGenerator / Rotator / ColorMixer | なし | — | gravity 不使用 |

詳細: [gravity-issettled-matrix.md](../s2il/gravity-issettled-matrix.md)
