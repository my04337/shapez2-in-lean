# Gravity Greenfield Rewrite 計画

- 作成日: 2026-04-23
- 最終更新: 2026-04-23（初版・第59報コミット直後）
- ステータス: **計画策定フェーズ / 実装未着手**
- 前提: 第58報までの Step B3b ブランチで基盤反例確定（`docs/plans/archive/s1-proof-plan.md` 履歴 / sorry-cards/archive/ 参照）
- 関連: [`gravity-proof-execution-plan.md`](gravity-proof-execution-plan.md) / [`agent-efficiency-proposals.md`](agent-efficiency-proposals.md) Phase 3 / [`MILESTONES.md`](MILESTONES.md)

---

## 0. 目的と背景

### 0.1 この計画が存在する理由

2026-04-22〜04-23（第36〜58報）の連続セッションで、`placeLDGroups_landing_groundingEdge_mono` （Step B3b）の証明を積み重ねた。しかし第58報で:

- **scaffold 補題 `landingDistance_foldl_placeFU_preserve_on_remaining`** が valid Shape 反例で FALSE
- **aux の IH 不変量 `h_sorted'` (`remaining` 側 Pairwise on obs')** 自体も valid Shape で FALSE

が判明し、累積した 14 サブプランすべての基盤が崩壊した。第59報で該当補題群を一時 axiom 化し sorry = 0 を回復したが、**既存 Gravity 層全体の証明ツリーを MECE の観点で点検する必要**がある。なぜなら:

1. `waveStep_grounding_mono` は axiom に委譲、その上位 `waveStep_ngs_strict_bound` も axiom に間接依存
2. `waveStep_rotate180_comm` も独立 axiom
3. `S2_axiom` / `S3_axiom` は placeholder のまま
4. 1 ブロック 1000 行超の `.lean` ファイル 4 本（CommExt/PlaceGrounding, CommExt/FloatUnits, GroundedMono, Equivariance/Clusters）で補題群が混在し、**内部補題と公開 API の境界が曖昧**

今後同じ罠を踏まないために、**Greenfield Rewrite（既存証明を一度アーカイブし、MECE に分割した新構造で再構築）** 方式を採る。

### 0.2 Greenfield の狙い

| 観点 | 現状の問題 | Greenfield で得るもの |
|---|---|---|
| **MECE 分割** | 補題が 1000 行ファイルに混在、相互依存が追跡困難 | 「落下物モデル / 障害物状態 / 配置操作 / 接地単調性 / 等変性」の 5 層にファイル分割 |
| **Internal 隔離** | `private` 補題と公開定理が 1 ファイル内で混在、エージェントが `read_file` で全量読む | 公開 API は `S2IL/Operations/Gravity.lean` の 200 行 facade に集約、internal は `S2IL/Operations/Gravity/Internal/` へ |
| **偽証明の混入防止** | scaffold 後に反例確定するパターンが連続発生 | 各 theorem の着手前に `lean-theorem-checker` を通し、真と確認された命題のみ signature 確定 |
| **エージェント認知負荷** | ファイル 1 本の sig-digest で 200〜400 行、symbol-map で数百シンボル | 各ファイル 300 行以下、facade は 50 シンボル以内 |
| **証明の簡略化** | 完成後の重複補題整理コストが残存 | 再構築時点で simp-normal form / `aesop` 相性 / `grind` 相性を考慮した統一インターフェース |

---

## 1. 方針概要

### 1.1 Greenfield Rewrite の基本形

次の 3 段階で進める:

1. **Archive フェーズ**: 既存 Gravity 層を `S2IL/Operations/Gravity/` から `S2IL/_archive/Gravity-pre-greenfield/` へ退避。ビルドから外す（Lake target を削る）。
2. **Skeleton フェーズ**: 新ツリーの公開 API を `axiom` だけで scaffold。下流（Stacker 等）が axiom 経由でビルド可能な状態を作る。
3. **De-axiomatization フェーズ**: 真偽を事前検証した命題から axiom → theorem へ段階的に置換。

### 1.2 真偽確認先行原則

本計画の全 theorem は次の順序で導入:

1. **数学的直感で真と思える命題をリストアップ**
2. 各命題について `lean-theorem-checker` エージェントに valid Shape 反例検索を依頼
3. 反例が出なければ `axiom` として scaffold 追加
4. 証明着手時に `lean-proof-planning` skill + REPL でゴール形状を確認
5. 証明完了後 axiom → theorem へ置換

偽と判明した命題は即座に signature を修正し、再度真偽検証する。

### 1.3 直感で真が明らかな基盤命題（優先着手候補）

ユーザー指摘の通り、**落下操作と回転の等変性**は直感でも原理上でも真。具体的に:

- `gravity_rotate180_comm`: 落下と 180° 回転は可換
- `gravity_rotateCW_comm`: 落下と CW 回転は可換
- `waveStep_rotateCW_comm`: waveStep 単体でも CW 可換（S3 相当、既存 axiom 候補）
- `waveStep_rotate180_comm`: 現 axiom (Equivariance/Clusters.lean)

これらは placeLDGroups の grounding 単調性に依存しないため、**B3b 群より先に構成的証明を確立できる可能性が高い**。

---

## 2. 新ディレクトリ構造（ドラフト）

```
S2IL/Operations/
├── Gravity.lean                    # 公開 API facade（200 行上限）
├── Gravity/
│   ├── Basic.lean                  # floating/settling の基本定義（≤ 300 行）
│   ├── Descent.lean                # landingDistance の意味論（≤ 400 行）
│   ├── PlaceOps.lean               # placeFallingUnit / placeLDGroups 定義と初等性質（≤ 500 行）
│   ├── GroundingMono.lean          # 接地単調性 (Step B1〜B4 相当、≤ 500 行)
│   ├── WaveStep.lean               # waveStep 定義と layer count 保存（≤ 300 行）
│   ├── ProcessWave.lean            # processWave 定義と終端性（≤ 400 行）
│   ├── Equivariance/
│   │   ├── Rotate180.lean          # rotate180 等変性（≤ 500 行）
│   │   └── RotateCW.lean           # rotateCW 等変性（≤ 500 行）
│   └── Internal/
│       ├── FloatUnitsNodup.lean    # 浮遊ユニット位置の重複無し等（≤ 600 行）
│       ├── LandingCheck.lean       # landingDistance.check の recursion 補題（≤ 400 行）
│       ├── PlaceFoldl.lean         # foldl_placeFU 系統の書込・保存補題（≤ 700 行）
│       └── SortStability.lean      # mergeSort による sort 不変量（≤ 400 行）
```

**新規な方針**:

- **`Internal/` は `import` 公開しない**: `Gravity.lean` と `Gravity/*.lean` からのみ参照可、外部ファイルからの直接 import を docstring / CI で禁止
- **公開補題はすべて `Gravity.lean` に `export` 形式で集約**: `Gravity/*.lean` 側で証明、`Gravity.lean` で `export Gravity (…)`
- **各ファイル冒頭 30 行で「目的 / 依存 / 公開シンボル」を明示**: sig-digest と併読で認知負荷を最小化

### 2.1 MECE 分割の意図

| ファイル | 数学的対象 | 直感の真偽 |
|---|---|---|
| Basic.lean | floatingUnits / settling の集合論的性質 | 全定理「真」（構造的 / 既証）|
| Descent.lean | landingDistance の step-wise 意味論 | 全定理「真」（landingDistance_not_occupied_at_landing 系）|
| PlaceOps.lean | placeFallingUnit / placeLDGroups の length・layerCount 保存 | 全定理「真」（構造的）|
| GroundingMono.lean | B1〜B4 の接地単調性 | **要反例検証**（B3b aux が破綻） |
| Equivariance/* | 落下と回転の可換性 | **直感で真**、反例リスク低（ユーザー指摘） |
| Internal/SortStability.lean | mergeSort の pairwise / Nodup 保存 | 全定理「真」（Mathlib 既存定理の薄い組立）|
| Internal/PlaceFoldl.lean | foldl_placeFU の isOccupied 保存・layer 書込位置 | **要反例検証**（`preserve_on_remaining` が反例で破綻） |

---

## 3. 実施フェーズ

### Phase A: Archive（1 セッション、範囲最小）

**目的**: 既存 Gravity を非 build な形で退避、新ブランチで空の skeleton ビルドが通る状態を作る

**タスク**:

- [ ] 新ブランチ `greenfield/gravity-rewrite` を作成
- [ ] `S2IL/Operations/Gravity/` 以下を `S2IL/_archive/Gravity-pre-greenfield-20260423/` に `Move-Item`
- [ ] `lakefile.toml` の Gravity ターゲットを削除し、下流（Stacker, Test, Verification）の import を一時コメントアウト
- [ ] `lake build` を green で通す（Gravity 依存以外のモジュール）
- [ ] `sorry-plan.json` 更新: `archive_reason = "greenfield-rewrite"`

**成果物**: 空の `S2IL/Operations/Gravity.lean`（`namespace Gravity end Gravity` のみ）がビルドする状態

### Phase B: Skeleton (axiom only)（2〜3 セッション）

**目的**: 新ディレクトリ構造の全公開 API を axiom で scaffold、下流が依存できる状態を作る

**タスク**:

- [ ] `S2IL/Operations/Gravity/Basic.lean`: 既存 `Defs.lean` から定義部のみコピー（theorem は全削除）
- [ ] 各 `Gravity/*.lean` に 公開 API を `axiom` で宣言（本計画 §2 構造に従う）
- [ ] `S2IL/Operations/Gravity.lean` facade を作成し `export` でまとめる
- [ ] 下流（Stacker, Test, Verification）の import を新 facade 経由に書換
- [ ] `lake build` green 確認、`sorry` 0 / `axiom` 数をスナップショット取得

**axiom の暫定数（推定）**: 20〜25（現行の 3 axiom + 既存 theorem 〜20 本の axiom 化）

**成果物**: 全機能が axiom で動作する状態。すべての `#eval` / `#guard` テストが通ることを確認。

### Phase C: De-axiomatization（多数セッション・順序は真偽リスク昇順）

**着手順推奨**（低リスク → 高リスク）:

1. **Basic.lean / Descent.lean / PlaceOps.lean の構造的補題**（定義展開・length 保存系）
2. **SortStability.lean**（Mathlib 既存の組立）
3. **Equivariance/Rotate180.lean**（ユーザー指摘: 直感で真）
4. **Equivariance/RotateCW.lean**（既存 S3 構造的証明資産の移植）
5. **GroundingMono.lean B1〜B3a**（既存 `_step_generic` / `_step` 資産の移植）
6. **Internal/PlaceFoldl.lean**（disjoint 性・書込位置・値保存系の再設計）
7. **GroundingMono.lean B3b**（↑ の成果を使い、aux IH 構造を新設計）
8. **ProcessWave.lean**（`waveStep_ngs_strict_bound` 再検証）

**各ステップ前に**:

- `lean-theorem-checker` で valid Shape 反例検索
- 直感で真だが反例が見つかった場合、signature を修正（前提追加 / 結論弱化）
- 既存 archive の証明を参考に取れるが、**そのまま持ち込まず一度破棄**（偽証明混入防止）

### Phase D: 後片付け（1〜2 セッション）

- [ ] `S2IL/_archive/` の削除またはアーカイブ永続化判断
- [ ] `docs/plans/gravity-proof-execution-plan.md` を新構造に合わせて更新
- [ ] `docs/plans/archive/` に旧 s1-proof-plan.md などを移動
- [ ] `AGENTS.md` / `docs/s2il/README.md` の Gravity 層参照を更新
- [ ] MILESTONES.md に「Greenfield 完了」マイルストーン追加

---

## 4. リスクと mitigation

| リスク | 影響 | mitigation |
|---|---|---|
| **下流 (Stacker 等) が Gravity の私的補題に依存** | Phase A/B で build 不能 | Phase A 前に `grep_search -r "import S2IL.Operations.Gravity.(Defs\|GroundedMono\|CommExt)"` で全下流依存を洗い出す |
| **Equivariance が意外と難航** | Phase C のスケジュール肥大 | 既存の `S3` 構造的証明資産（`gravity-proof-execution-plan.md` §再利用可能 list）を Phase C-4 でそのまま移植可能 |
| **B3b が再び破綻** | Greenfield 後も axiom 残留 | Phase C-6 (`PlaceFoldl.lean` internal 補題の再設計) を B3b 本体より先に整備。internal 補題に反例が出た時点で pivot 判断 |
| **archive 削除後に資産が欲しくなる** | 情報喪失 | `_archive/` は永続化、Phase D で `git tag pre-greenfield-20260423` を付与 |
| **agent のコンテキスト浪費** | Greenfield 中のセッション効率低下 | `agent-efficiency-proposals.md` Phase 3 の facade 化ルールを Phase B の skeleton 作成と同時適用（一石二鳥） |

---

## 5. 成功基準

- [ ] `lake build` green、`sorry = 0`、`axiom`（Gravity 関連）= 0（S2_axiom / S3_axiom は Phase C 完了時点で再評価）
- [ ] `S2IL/Operations/Gravity.lean`（facade）が 200 行以下
- [ ] 各 `Gravity/*.lean` が 500 行以下
- [ ] `Gravity/Internal/` は外部 import を受けない
- [ ] `S2IL/_agent/symbol-map.jsonl` で Gravity 関連シンボル数が ≤ 500（現状 ~1000）
- [ ] `lean-theorem-checker` による真偽検証ログが各 theorem について残る（`docs/plans/gravity-greenfield-rewrite-plan.md` の Phase C 進捗表に追加）
- [ ] vanilla4 / vanilla5 / stress8 の `#guard` テストがすべて通る

---

## 6. 着手判断（次セッション）

本計画の採否は **ユーザー判断**を要する。次の 3 つの分岐が考えられる:

### 選択肢 1: 全面 Greenfield（本計画通り）

**pros**: 数学的・コード的に最も美しい状態を最終的に得る。偽証明混入防止が恒久化。
**cons**: 10〜20 セッション相当のコスト。既存 1000 行資産の再検証 overhead。

### 選択肢 2: 部分 Greenfield（GroundedMono のみ）

B3b 周辺の `GroundedMono.lean` / 関連 `CommExt/*.lean` のみを archive し、他は現状維持。
**pros**: 2〜3 セッションで完了。リスクが低い。
**cons**: 他層の MECE 不整合は残存。エージェント認知負荷の削減効果は限定的。

### 選択肢 3: 計画自体の再検討

本計画のスコープ（Internal 隔離・ファイル分割 vs. 単純 axiom 維持）を再評価。
**pros**: 小さく pivot できる。
**cons**: 偽証明の再発リスク。

**著者推奨**: **選択肢 1 を段階実施**（Phase A + Phase B は 3〜5 セッションで完了可能、効果が見えてから Phase C に進むか判断）。

---

## 7. 進捗追跡

各 Phase 完了時に本ファイルの §3 タスクリストにチェックを入れ、`MILESTONES.md` に参照を追加する。
Phase C の着手順は真偽検証結果で動的に変更可能（例: Equivariance が直感通り早期クローズした場合 Phase C-6 に集中投資）。

詳細な sorry 進捗は `S2IL/_agent/sorry-plan.json` に記録（Greenfield 期間中は `status: "greenfield-pending"` を使用）。

---

## 付録 A: 既存資産の評価（Phase A 前の棚卸し）

### 継続利用候補（reusable without modification）

| 補題 | ファイル | 理由 |
|---|---|---|
| `placeLDGroups_landing_groundingEdge_mono_step_generic` | GroundedMono.lean:904 | 0-sorry、`foldl_placeFU_mixed_fixed_d_groundingEdge_mono` の薄い wrapper |
| `placeLDGroups_landing_groundingEdge_mono_step` | GroundedMono.lean:984 | 0-sorry、_step_generic の clearPositions 特化 |
| `foldl_placeFU_mixed_fixed_d_groundingEdge_mono` | GroundedMono.lean | B3a mixed 本体、2026-04-22 証明完了 |
| `placeLDGroups_landing_nonEmpty` | CommExt/PlaceGrounding.lean | B4 seed_landing 供給 |
| `floatingUnits_flatMap_positions_nodup` | CommExt/FloatUnits.lean | 浮遊ユニット位置の重複無し |
| `floatingUnits_positions_pairwise_disjoint` | CommExt/FloatUnits.lean | FU 間位置 disjoint |

### 廃棄決定（refuted / unused）

| 対象 | 理由 |
|---|---|
| `landingDistance_foldl_placeFU_preserve_on_remaining` | 第58報で反例確定（FALSE）|
| `placeLDGroups_remaining_head_pin_landing_empty` | `h_sorted` preservation 依存、IH 不健全 |
| `placeLDGroups_landing_groundingEdge_mono_aux` | IH 不変量 `h_sorted'` が valid Shape で FALSE |
| 第41報の `α1 / α4` | 反例確定（archive `docs/plans/archive/s1-proof-plan.md` 参照）|

### 要再検証（真偽が不確定）

現時点の axiom 全て（Phase B 後に `lean-theorem-checker` で一斉検証）。

---

## 付録 B: 関連ドキュメント

- [`docs/plans/gravity-proof-execution-plan.md`](gravity-proof-execution-plan.md): Gravity 全体の執行計画（Greenfield 完了後に更新）
- [`docs/plans/agent-efficiency-proposals.md`](agent-efficiency-proposals.md): Phase 3 facade 化案（本計画 Phase B で同時適用）
- [`docs/agent/proof-plan-current-focus-guide.md`](../agent/proof-plan-current-focus-guide.md): 新規 sorry 着手時の sorry-card 作成手順
- [`docs/agent/proof-retreat-pivot-guide.md`](../agent/proof-retreat-pivot-guide.md): 撤退判断基準（本計画の基礎）
- [`.github/skills/lean-counterexample/SKILL.md`](../../.github/skills/lean-counterexample/SKILL.md): 真偽検証手順
- [`S2IL/_agent/sorry-plan.json`](../../S2IL/_agent/sorry-plan.json): sorry / axiom の最新状態
- Archive: `S2IL/_agent/sorry-cards/archive/{placeLDGroups_landing_groundingEdge_mono.md, waveStep_grounding_mono.md}`（第36〜58報の詳細履歴）

---

**この計画自体の次アクション**: ユーザーによる選択肢 1〜3 の決定。決定後、Phase A 着手セッションで本ファイルの §3 タスクリストに従って実装開始。
