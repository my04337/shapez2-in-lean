# Layer A/B Greenfield Rewrite 実施計画

- 作成日: 2026-04-24
- 最終更新: 2026-04-29
- ステータス: **Phase 0 / A / A-R / B / B-R / C / C-R 完了。Phase D 進行中（Settled / Painter / CrystalGenerator / ColorMixer / Cutter / Swapper / Stacker / PinPusher 完了、axiom 48→15）**
- スコープ: S2IL Layer A（Shape / Kernel / Operations 純粋部 / Wires スケルトン / Machine）および Layer B（振る舞い系）の再構築
- 関連: 構造の正本は [architecture-layer-ab.md](architecture-layer-ab.md)

---

## 0. この計画の位置付け

「何を・どの順で実施するか」を定める手順書。構造の拘束条件は [architecture-layer-ab.md](architecture-layer-ab.md) に委譲する。

| ドキュメント | 責務 |
|---|---|
| `architecture-layer-ab.md` | 構造の正本（ディレクトリ・API 境界・MECE・命名・サイズ上限） |
| `layer-ab-rewrite-plan.md`（本書） | Phase 構成・着手順序・振り返り手順・リスク管理 |

---

## 1. ゴール

[architecture-layer-ab.md](architecture-layer-ab.md) §1 の原則を全て満たす状態へ Layer A/B を再構築する。最上位の成功基準:

1. **Facade のみを外部から参照すればよい** 状態（`Internal/` の外部 import 0）
2. **同じ意味を持つ補題が複数存在しない**（特に等変性の CW / 180° / CCW 並行チェーンの排除）
3. **インデックス機構なしで** エージェントが運用できる

既存の証明資産は全 archive した上で、補題単位で再評価して取り込む。

> **注記**: 旧コードの混色補題は `Color` の構成（`black` 追加）と `mix` の規則がゲーム側のアップデートで変わっている点に注意。新仕様は [docs/shapez2/game-system-overview.md](../shapez2/game-system-overview.md) 「混色規則」節を参照。`mix_self` は `a = white` で不成立（`w + w = k`）。

---

## 2. フェーズ全体像

```
Phase 0  計画書整備                          ✅ 完了
Phase A  Archive & Index 廃止                ✅ 完了
   └─ Phase A-R  振り返り                    ✅ 完了
Phase B  Skeleton（axiom で公開 API scaffold）✅ 完了
   └─ Phase B-R  振り返り                    ✅ 完了
Phase C  Layer A 脱 axiom 化                 ✅ 完了 (2026-04-28)
   └─ Phase C-R  振り返り                    ✅ 完了
Phase D  Layer B 脱 axiom 化                 ← 次のアクション
   └─ Phase D-R  振り返り
Phase E  総仕上げ（archive 削除・MILESTONES 整合・全点検）
```

各 `-R`（Retrospective）フェーズは実装フェーズの末尾に必ず挟む。構造の見直しを次フェーズに繰り越さない。

---

## 3. Phase 0–C 完了ログ（要約）

詳細な作業手順は git 履歴に保存されている。ここでは結果と参照点のみ残す。

### 3.1 Phase 0 ✅

[architecture-layer-ab.md](architecture-layer-ab.md) と本書を整備、旧 Gravity 限定計画を本書に統合、`MILESTONES.md` / `README.md` のリンクを更新。

### 3.2 Phase A: Archive & Index 廃止 ✅

- ブランチ `greenfield/layer-ab-rewrite` を切り、旧 `S2IL/{Shape,Kernel,Operations,Machine}/` を `S2IL/_archive/pre-greenfield/` へ退避
- `S2IL/_agent/` から `symbol-map.jsonl` / `dep-graph-baseline.json` / `sig-digest/` / `route-map.json` / `query-playbook.json` を削除（残るのは `sorry-plan.json` / `sorry-goals.md` / `sorry-cards/` のみ）
- `DevTool/Toolkit/{SymbolMap,DepGraph}.lean` 等のインデックス生成ツール、`.github/hooks/scripts/regen-indices.*` を削除
- 空 facade（`S2IL.lean` / `Shape.lean` / `Kernel.lean` / `Wires.lean` / `Operations.lean` / `Machine.lean`）で `lake build` green
- AGENTS.md / 各 SKILL.md / `docs/agent/` 配下のインデックス参照を全廃

`_archive/pre-greenfield/` は Phase E で削除する。削除前に `pre-greenfield-yyyymmdd` タグを git に付与する。

### 3.3 Phase B: Skeleton ✅

- 各 facade に目次コメント（[architecture-layer-ab.md §3.1](architecture-layer-ab.md)）を整備
- 全公開 API を `axiom` で signature 宣言（証明は書かず）
- 各操作の `_rotateCW_comm` を axiom、`_rotate180_comm` / `_rotateCCW_comm` は CW 版からの 1 行系 `theorem`（[§1.4 単一チェーン原則](architecture-layer-ab.md)）
- Phase B 末: axiom = 184, sorry = 0, warning = 0

### 3.4 Phase C: Layer A 脱 axiom 化 ✅（2026-04-28 完了）

Phase B 末 184 axiom → Phase C 末 **48 axiom**（-136）。Shape 型系 / Kernel は **完全に axiom-free**。残 axiom は全て Operations/* と Wires/Signal.lean の primitive・恒等式・CW 等変性で、Phase D（Layer B）で順次降格する。

| サブステップ | 内容 | 完了 |
|---|---|---|
| §8.1.1 | Kernel 再 scaffold（旧 `genericBfs` 廃止 → Mathlib `Relation.ReflTransGen` + Finset 表現） | 2026-04-27 |
| §8.1.2 | `IsSettled` の Prop primitive + `DecidablePred` 化 | 2026-04-27 |
| §8.1.3 | Behavior レイヤから `Option Shape` を追放（0 層シェイプを `Shape` に含める） | 2026-04-27 |
| §8.1.4 | Cutter / Swapper の `eastHalf` / `westHalf` / `combineHalves` primitive 化 | 2026-04-27 |
| §8.1.5 | `Direction := Fin 4` / `Layer := Fin 4 → Quarter` / `QuarterPos := Nat × Fin 4` 具体化 | 2026-04-27 |
| §8.1.6 | Normalization 規約適用（Prop primitive + `DecidablePred` + `normalize` 全関数） | 2026-04-27 |
| §8.1.7 | `Shape := List Layer`（0 層許容、`layerCount := List.length`） | 2026-04-27 |
| §8.1.8 | Prop/Bool 二層規約の統一（`IsBonded` Prop + `isBonded := decide`） | 2026-04-27 |
| §8.1.9 | `Shape/Types.lean` の opaque 型を inductive に降格（Color / Quarter / PartCode / RegularPartCode） | 2026-04-27 |
| §8.1.10 | `Shape/GameConfig.lean` を `structure` 化、`vanilla4` / `vanilla5` / `stress8` を具体値に | 2026-04-27 |
| §8.1.11 | `Shape/Notation.lean`（round-trip 定理）の脱 axiom | 2026-04-27 |
| §8.1.12 | `Kernel/Bond.lean`（`IsBonded` 具体定義、`symm` / `rotateCW` の証明） | 2026-04-28 |
| §8.1.13 | `Kernel/Cluster.lean`（`ClusterRel := Relation.ReflTransGen IsBonded`、`clusterSet` (Finset, noncomputable)、`clusterSet.rotateCW_comm`）。`clusterList` / `allClusters` は Phase D で MAM/Shatter 必要時に追加 | 2026-04-28 |

### 3.5 Phase A-R / B-R / C-R 振り返り ✅

各振り返りで次を確認した:

- **公開 API 境界の妥当性**: Internal が外部から参照されていないこと
- **補題の MECE 性**: Defs / Behavior / Equivariance / Internal の区分が重複していないこと
- **再モデリング残存チェック**: 旧モデル（`genericBfs` / `GenericReachable` / `Option Shape` 返り型 / 旧 `isSettled` axiom ペア / `axiom Layer : Type` / `axiom Direction : Type` / 各層 `rotateCW` axiom / `ofLayers.*Option` / `normalize.*Option`）が `grep_search` で 0 hit
- **次レイヤからの使いやすさ**: Layer B/C が必要とする API が公開されていること
- **認知負荷指標**: 各ファイル行数（facade ≤ 150 / 一般 ≤ 300）、1 ディレクトリのファイル数（≤ 8）、Internal ファイル数の爆発がないこと

---

## 4. Phase D: Layer B 脱 axiom 化（多セッション想定、← 次のアクション）

**目的**: Layer B（振る舞い系）の axiom を実証明に置換する。Phase C 末で Operations/* と Wires/Signal.lean に残存する 48 axiom を順次降格する。

### 4.1 着手順序（低リスク → 高リスク）

1. `Operations/Settled.lean`（構造的、IsSettled 具体定義） ✅ 2026-04-28
2. `Operations/Painter.lean`（着色系、Layer/Quarter map 経由） ✅ 2026-04-28
3. `Operations/CrystalGenerator.lean`（結晶化、Painter 同型） ✅ 2026-04-28
4. `Operations/ColorMixer.lean`（混色系、Color.mix 経由） ✅ 2026-04-28
5. `Operations/Cutter.lean`（E/W primitive、§1.4.1 例外規則） ✅ 2026-04-29
6. `Operations/Swapper.lean`（cut + combineHalves の派生） ✅ 2026-04-29
7. `Operations/Stacker.lean`（placeAbove / shatterTopCrystals / stack） ✅ 2026-04-29
8. `Operations/PinPusher.lean`（liftUp / generatePins / pinPush） ✅ 2026-04-29
9. `Operations/Shatter.lean`（Cluster 基盤に依存。`clusterList` を Phase D 内で導入する場合はここで追加） ✅ 2026-04-29
10. `Operations/Gravity.lean` — **§4.3 で別管理**（深い設計検討を別セッションで実施してから着手）
11. `Wires/*.lean`（Layer C 着手時まで延期可。スケルトンのまま残してもよい）

### 4.2 注意

- 各操作につき CW 版の等変性のみを証明し、180° / CCW は facade の 1 行系で済ませる
- 旧 Gravity の GroundingMono 複雑帰納（旧 B3b 相当）は Internal/Place の再設計を先に完了させてから着手する（→ §4.3 で詳述）
- `clusterList` / `allClusters` は Shatter / MAM 等が実際に必要としたタイミングで `Kernel/Internal/ClusterImpl.lean` として追加する（Cluster.lean の公開 API には影響しない）
- 各補題の着手前に [architecture-layer-ab.md §1.5](architecture-layer-ab.md) 真偽検証先行原則と `lean-proof-planning` skill を実行
- 大きな単位（例: Stacker 全体完了時）ごとに §5 のチェックリストを軽量実施し違反を即修正

### 4.3 Phase D-10 — `Operations/Gravity.lean` の脱 axiom（独立セクション）

**位置付け**: Phase D で残る最後の axiom 群。`Shape.gravity` / `gravity.isSettled` / `gravity.of_isSettled` / `gravity.rotateCW_comm` の 4 本を実装と証明に置換する。Layer B 全体で唯一の重実装ノード（Layer A は完了、Operations 配下は Gravity 以外すべて axiom-free）。

**現状（2026-04-29 時点）**:

- `S2IL/Operations/Gravity.lean` は 36 行のスケルトン。`Kernel.Cluster` / `Operations.Settled` の `IsBonded` / `IsContact` / `IsGroundingEdge` / `IsGrounded` / `IsSettled` 述語基盤は完成済みで、Gravity の意味論を述語で語る土台が揃っている。
- Phase D-9 完了で Operations 全体（Gravity 以外）が axiom 0 / sorry 0、非アーカイブ axiom は Wires.Signal の型 axiom 5 本と Gravity の 4 本のみ。

**今セッション（Phase D-9 末）の見解**:

1. **定義方針が未決**: `gravity` の executable 定義として 3 候補がある。
    - **(a) `gravityStep` の有限反復**（旧 `_archive/pre-greenfield/Operations/Gravity/` 採用）。`waveStep_grounding_mono_persistence` 系の終端性証明が極めて重く、過去に証明破綻（`/memories/repo/waveStep-grounding-mono-persistence.md`）。
    - **(b) `IsSettled` 判定 + `Classical.choice`**（`noncomputable def` で「最小の安定後継状態」を選ぶ）。等変性は容易だが `#eval` 不可、MAM（Layer D）の計算的完全性証明で詰む可能性。
    - **(c) LDGroup（Locally Detected Group）一発配置**。旧 `placeLDGroups` を再構築。構造的に綺麗だが Internal/Place の再設計が前提条件。
2. **既存資産の再評価が必要**: `_archive/pre-greenfield/Operations/Gravity/Equivariance/Clusters.lean` / `GroundedMono.lean` には旧 axiom（`waveStep_rotate180_comm` / `placeLDGroups_landing_groundingEdge_mono`）が残存しており、これらの教訓を抽出してから新実装に進む必要がある。
3. **基盤の活用余地**: 今回新設した `Direction.add_one_sub_one` 等の集約補題、`ClusterRel.rotateCW_two` / `rotateCW_three`、`Operations.Settled` の `IsGrounded` 述語は Gravity 等変性証明で多用される見込み。Phase D-9 までの整理が Gravity の証明シナリオを軽くする方向に効く。
4. **MECE 観点の懸念**: Gravity の意味論（「不安定象限が落下して安定状態に至る」）と `IsSettled` 判定（既に存在）は同じ言語で語れるが、`gravity` の構成と `gravity_isSettled` の証明では `Operations.Settled` の補題群がどこまで使えるかの境界を切る必要がある。

**判断**: Phase D-10 は **本セッションでは着手しない**。次の独立セッションで以下を順に実施する:

1. `lean-proof-planning` SKILL の徹底実行（証明戦略の事前検証）
2. `_archive/pre-greenfield/Operations/Gravity/` の証明構造を読み解き、(a)/(b)/(c) のどれが「数学的美しさ × 実装可能性 × MAM 互換」の最大化となるか評価（`/memories/repo/waveStep-grounding-mono-persistence.md` の失敗ノートを起点）
3. [architecture-layer-ab.md](architecture-layer-ab.md) §1.4.4 として「落下機構（Gravity）」設計セクションを追加
4. 反例検証先行原則に従い、`vanilla4` / `vanilla5` で `gravity` の期待出力を `#eval` できる定義（候補 (a) または (c) 推奨）を選好
5. 最小スケルトン（定義 + 等変性主補題 + sorry）を作成し、`sorry-cards/` 配下で個別 sorry の作業ノートを開始
6. その後本格証明（GroundingMono / 終端性 / 不動点性）に着手

**前提条件（Phase D-10 着手 GO 条件）**:

- [ ] §1.4.4 が記述され、定義方針 (a)/(b)/(c) の選択根拠が文章化されている
- [ ] `_archive` の旧証明から「移植可能な補題」と「破綻パスを避けるべき方向」が抽出されている
- [ ] `vanilla4` / `vanilla5` の期待出力が反例検証で確認可能な形になっている
- [ ] 必要な Internal ファイル（`Kernel/Internal/ClusterImpl.lean` 等）の追加要否が判断されている

これらが揃わないまま着手すると過去の `waveStep_grounding_mono_persistence` 失敗の再演リスクが高い。**焦って着手しない** ことを明記する。

---

## 5. Phase D-R / 共通振り返りチェックリスト

Phase D 完了時、および Phase 内軽量レビューで参照する共通チェック:

- **公開 API 境界の妥当性**: Internal が外部から参照されていないか / facade が薄すぎ・厚すぎでないか / Layer C から見て不足 API がないか
- **補題の MECE 性**: 重複・層またぎがないか / 同じ意味の補題が複数ないか / 等変性 CW/180°/CCW 並行チェーンが残っていないか
- **次レイヤからの使いやすさ**: Layer C/D（Machine / MAM）が必要とする API が公開されているか / Internal を覗く必要がないか
- **認知負荷指標**: 各ファイル行数（facade ≤ 150 / 一般 ≤ 300）、1 ディレクトリのファイル数（≤ 8）、Internal ファイル数の爆発がないか
- **特に Phase D**:
  - Layer C のフロー定義から見て `Operations.lean` だけを import すれば完結するか
  - MAM（Layer D）の完全性証明で参照が予想される定理（例: Stacker の `placeAbove ∘ gravity` の構造的保存則）が公開されているか

満たせない場合は Phase D に差し戻し、公開 API 境界の再設計や補題の整理を行う。

---

## 6. Phase E: 総仕上げ（1〜2 セッション想定）

**目的**: 全 Phase の整合を取り、`_archive/` を削除し、関連ドキュメントを更新する。

### 6.1 作業項目

- [ ] `S2IL/_archive/pre-greenfield/` に `pre-greenfield-yyyymmdd` タグを付与して削除（git 履歴で参照可能）
- [ ] [MILESTONES.md](MILESTONES.md) の Layer A / B の記述を新構造に合わせて更新
- [ ] `sorry-plan.json` / `sorry-goals.md` / `sorry-cards/` のクリーンアップ
- [ ] 各 facade に Layer C 向けの README コメント（典型的な呼び出しパターン）を追記
- [ ] axiom = 0, sorry = 0 の最終確認

### 6.2 成功基準

- `lake build` green
- axiom = 0
- sorry = 0
- 各 facade ≤ 150 行
- 一般ファイル ≤ 300 行
- Internal ファイル ≤ 300 行
- Internal の外部被参照 = 0
- `S2IL/_agent/` に `sorry-plan.json` / `sorry-goals.md` / `sorry-cards/` のみが残存
- [architecture-layer-ab.md](architecture-layer-ab.md) と実装の乖離が無い

---

## 7. 既存資産の扱い方針（Phase D / E で適用）

[architecture-layer-ab.md §1.6](architecture-layer-ab.md) に従い、`_archive/pre-greenfield/` の補題を **2 段階のフロー** で個別判定する。

**Step 1: 数学的真偽と構造的立ち位置**

| 判定 | 処置 |
|---|---|
| L が偽（反例あり） | 廃棄 |
| L が真だが誰にも使われない見込み | 廃棄（デッド補題候補） |
| L が真だが、似た意味の別補題 L' が存在 | L と L' を統合した 1 本に書き直す → Step 2 へ |
| L が真で、新構造の単一チェーンに収まる | Step 2 へ |

**Step 2: 証明アプローチの品質評価**

- (a) 数学的に美しく MECE か（補題チェーン内の立ち位置・前提の最小性）
- (b) 設計バグを持ち込まないか（偽前提依存・廃止予定補題依存・旧構造特有の迂回への依存）

| 結果 | 処置 |
|---|---|
| すべて YES | そのまま移植（必要なら改名） |
| 一部 NO | 証明の発想・アイデアのみ参考にし、補題定義・証明本体は再実装 |
| 判断できない | `lean-proof-planning` skill でゴール形状を確認後に再評価 |

---

## 8. リスクと mitigation

| リスク | mitigation |
|---|---|
| 再構築中に Layer B GroundingMono が再び破綻 | Phase D-10 着手前に Internal/Place の再設計を完遂してから取りかかる |
| CW 等変性の主証明が難航 | 既存資産の証明構造を §7 Step 2 で評価してから移植テンプレートとして採用する。ただし rotate180 専用の中間補題は系化して捨てる |
| 既存証明に設計バグ（偽前提依存・旧構造特有の迂回）が潜んでいた | §7 Step 2 のアプローチ品質評価で検出する。全体流用せず、証明の発想のみ参考にして補題定義・証明本体は再実装する |
| `_archive/` 読込でコンテキスト溢れ | `_archive/` は明示指示がない限り `read_file` しない。symbol 検索対象からも除外 |
| デッド補題の判断ミスで必要な補題を消す | フェーズ末レビューでは削除候補リストを先に作り、次フェーズ着手時に実際に必要かを再確認してから削除 |

---

## 9. 関連

| 参照先 | 用途 |
|---|---|
| [architecture-layer-ab.md](architecture-layer-ab.md) | 構造の正本 |
| [MILESTONES.md](MILESTONES.md) | 上位の最終目標 |
| [docs/agent/proof-plan-current-focus-guide.md](../agent/proof-plan-current-focus-guide.md) | 新規 sorry 着手時の手順 |
| [docs/agent/proof-retreat-pivot-guide.md](../agent/proof-retreat-pivot-guide.md) | 撤退判断基準 |
| [.github/skills/lean-counterexample/SKILL.md](../../.github/skills/lean-counterexample/SKILL.md) | 真偽検証 |
| [S2IL/_agent/sorry-plan.json](../../S2IL/_agent/sorry-plan.json) | sorry / axiom の最新状態 |
