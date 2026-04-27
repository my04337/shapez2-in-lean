# Layer A/B Greenfield Rewrite 実施計画

- 作成日: 2026-04-24
- 最終更新: 2026-04-27
- ステータス: **Phase B 完了 / Phase C 冒頭再 scaffold (§8.1.1〜§8.1.8) 完了。Phase C 後半（残 axiom 脱化）着手前**
- スコープ: S2IL Layer A（Shape / Kernel / Operations 純粋部 / Wires スケルトン / Machine）および Layer B（振る舞い系）の再構築
- 関連: 構造の正本は [architecture-layer-ab.md](architecture-layer-ab.md)

---

## 0. この計画の位置付け

本ドキュメントは「何を・どの順で実施するか」を定める **手順書** である。構造そのものの拘束条件は [architecture-layer-ab.md](architecture-layer-ab.md) に委譲する。両者の役割分担:

| ドキュメント | 責務 |
|---|---|
| `architecture-layer-ab.md` | 構造の正本（ディレクトリ・API 境界・MECE・命名・サイズ上限） |
| `layer-ab-rewrite-plan.md`（本書） | Phase 構成・着手順序・振り返り手順・リスク管理 |

本計画は Layer A/B 全体を対象とし、従来 `S2IL/_agent/` で支えてきたインデックス機構を **廃止** する前提で新構造を設計する。

---

## 1. ゴール

[architecture-layer-ab.md](architecture-layer-ab.md) §1 の原則をすべて満たす状態へ Layer A/B を再構築する。特に次の 3 条件を最上位の成功基準とする:

1. **Facade のみを外部から参照すればよい** 状態（`Internal/` の外部 import 0）
2. **同じ意味を持つ補題が複数存在しない**（特に等変性の CW / 180° / CCW 並行チェーンの排除）
3. **インデックス機構（symbol-map / dep-graph-baseline / sig-digest / route-map / query-playbook）なしで** エージェントが運用できる

既存の証明資産は全 archive した上で、**補題単位で再評価** して新構造へ取り込む。

---

## 2. フェーズ全体像

```
Phase 0  計画書整備（本書の整備）                          ← 完了
Phase A  Archive & Index 廃止                              ← 次のアクション
   └─ Phase A-R  振り返り
Phase B  Skeleton（axiom で公開 API scaffold）
   └─ Phase B-R  振り返り
Phase C  Layer A 脱 axiom 化
   └─ Phase C-R  振り返り
Phase D  Layer B 脱 axiom 化
   └─ Phase D-R  振り返り
Phase E  総仕上げ（archive 削除・MILESTONES 整合・全点検）
```

各 `-R`（Retrospective）フェーズは **実装フェーズの末尾に必ず挟む**。構造の見直しを次フェーズに繰り越さない。

---

## 3. Phase 0: 計画書整備

**目的**: 新アーキテクチャの正本と本実施計画を整備し、既存 Gravity 限定計画を archive 化する。

**成果物**:

- [x] [architecture-layer-ab.md](architecture-layer-ab.md) 作成
- [x] [layer-ab-rewrite-plan.md](layer-ab-rewrite-plan.md) 作成（本書）
- [x] 旧 Gravity 限定計画の内容を本計画へ統合
- [x] [MILESTONES.md](MILESTONES.md) と [README.md](README.md) の参照を更新

**完了条件**: `docs/plans/` 内の相互リンクが切れていない、Phase A 着手判断ができる。

---

## 4. Phase A: Archive & Index 廃止（1 セッション想定）

**目的**: 既存 Layer A/B を非 build 状態に退避し、空 facade のみで `lake build` green を実現する。同時に `S2IL/_agent/` のインデックス機構を廃止する。

### 4.1 作業手順

1. **ブランチ作成**: `greenfield/layer-ab-rewrite`
2. **下流依存の棚卸し**: `grep_search -r "import S2IL\."` で `S2IL.X.Internal` を直接 import している箇所を洗い出す（Test / Verification / Scratch 含む）
3. **既存ソースの退避**: 次を `S2IL/_archive/pre-greenfield/` へ移動
   - `S2IL/Shape/`
   - `S2IL/Kernel/`
   - `S2IL/Operations/`
   - `S2IL/Machine/`
   - `S2IL/SettledShape.lean` 等ルート直下のコード
4. **インデックス廃止**: `S2IL/_agent/` から以下を削除
   - `symbol-map.jsonl`
   - `dep-graph-baseline.json`
   - `sig-digest/`
   - `route-map.json`
   - `query-playbook.json`

   残すのは `sorry-plan.json` / `sorry-goals.md` / `sorry-cards/` のみ。
5. **インデックス生成ツールの棚卸し**: 削除 or Disable
   - `DevTool/Toolkit/SymbolMap.lean`
   - `DevTool/Toolkit/DepGraph.lean`
   - 必要に応じて `ProofStats.lean`
6. **フック / スクリプトの無効化**:
   - `.github/skills/lean-build/scripts/` 配下の `regen-indices.ps1` 等、廃止インデックスを生成する処理をすべてスキップ or 削除
   - Stop フックから呼び出されている箇所を削除
7. **空 facade の追加**: `S2IL.lean` / `Shape.lean` / `Kernel.lean` / `Wires.lean` / `Operations.lean` / `Machine.lean` を最小構成で作成（空 namespace のみ）
8. **Test / Verification の暫定対応**: 下流テストを一時的に `#guard True` で置換、もしくはファイルごとコメントアウト
9. **`lake build` green 確認**

### 4.2 既存資産の扱い方針

[architecture-layer-ab.md §1.6](architecture-layer-ab.md) に従い、**2 段階のフロー**で補題単位に判定する。

**Step 1: 数学的真偽と構造的立ち位置**

```
既存補題 L を評価
  │
  ├─ L が偽（反例あり）──────────────────────→ 廃棄
  │
  ├─ L が真だが誰にも使われない見込み──────→ 廃棄（デッド補題候補）
  │
  ├─ L が真だが、似た意味の別補題 L' が存在
  │     └─ L と L' を統合した 1 本に書き直す → Step 2 へ
  │
  └─ L が真で、新構造の単一チェーンに収まる → Step 2 へ
```

**Step 2: 証明アプローチの品質評価**（Step 1 で存続と判断された補題に対して）

```
証明アプローチを評価
  │
  ├─ 次の条件をすべて満たすか:
  │     (a) 数学的に美しく MECE か
  │           ─ 補題チェーン内の立ち位置が適切（冗長な中間補題・迂回路がない）
  │           ─ 仮定が必要最小限で、過剰な前提に依存していない
  │     (b) 設計バグを持ち込まないか
  │           ─ 偽の前提・廃止予定の補題への依存がない
  │           ─ 旧構造特有の迂回（例: rotate180 専用の中間補題）に依存していない
  │
  ├─ すべて YES → そのまま移植（必要なら改名）
  │
  ├─ 一部 NO  → 証明の発想・アイデアのみ参考にし、補題定義・証明本体は再実装
  │              （_archive/ への参照は発想メモとして残してよいが、コードは引き継がない）
  │
  └─ 判断できない → lean-proof-planning skill でゴール形状を確認後に再評価
```

`_archive/pre-greenfield/` は Phase E で削除し、削除前に `pre-greenfield-yyyymmdd` タグを付与する（git 履歴で参照可能）。

---

## 5. Phase A-R: 振り返り

**目的**: インデックス廃止後でもエージェントが facade だけで Layer A/B を辿れるかを実地検証する。

### 5.1 チェック項目

- [x] サンプルタスク 1 件（例: 「Shape の round-trip 定理の位置を特定して」）を `_agent/` インデックスなしで実行し、ワーキングメモリ消費が許容範囲か確認
  - 本セッションの Phase A 廃止作業自体が facade ベースで遂行され、旧インデックスなしでも問題なく完了
- [x] `_archive/` 参照がコンテキスト溢れを起こさないことを確認（Phase A では空 facade のみなので基本的に `_archive/` は読まない想定）
  - 本セッション中 `_archive/` 下のファイルを `read_file` する必要は発生せず、`grep_search` も preflight 除外設定で回避
- [x] `S2IL/AGENTS.md` / `AGENTS.md`（ルート）/ `.github/skills/` の `_agent` 依存記述を更新
  - Phase A 本体: ルート `AGENTS.md`, `S2IL/AGENTS.md`, `DevTool/AGENTS.md`, `.github/skills/lean-build/SKILL.md`, `.github/skills/lean-proof-progress/SKILL.md` を更新
  - 本追従: `.github/skills/lean-diagnostics/SKILL.md`, `.github/skills/session-efficiency/SKILL.md` から旧インデックス指標を削除
- [x] `docs/agent/` 配下の関連ドキュメント（`proof-plan-current-focus-guide.md` など）の `_agent` 参照を洗い出し、必要なら追補
  - `docs/agent/README.md`, `docs/agent/agent-operations-playbook.md` で Phase A 廃止注記済
  - 本追従: `docs/agent/proof-plan-current-focus-guide.md`, `docs/agent/repl-session-state-guide.md`, `docs/lean/naming-conventions.md`, `docs/lean/lean-proof-tips.md`, `docs/s2il/proof-workflow-playbook.md`, `README.md` から旧インデックス参照を除去
  - 追加撤去: `.github/hooks/hooks.json` から `regen-indices` エントリ削除、`.github/hooks/scripts/regen-indices.ps1/.sh` を削除、`.vscode/settings.json` の `s2il-toolkit` 許可削除、`.github/agents/lean-sorry-snapshot.agent.md` / `lean-session-restorer.agent.md` の `s2il-toolkit depgraph` 参照を `sorry-plan.json` 経路に置換

### 5.2 続行判断

次の条件をすべて満たしたら Phase B に進む:

1. `lake build` green
2. エージェント指示書のインデックス依存記述が更新済み
3. サンプルタスクでインデックスなしでも facade から目的のコードに 3 ステップ以内で到達できる

満たせない場合は Phase A に差し戻し、アーキテクチャ（facade 目次の記述量・サイズ上限）の再調整を検討する。

---

## 6. Phase B: Skeleton（2〜3 セッション想定）

**目的**: [architecture-layer-ab.md §2](architecture-layer-ab.md) の新構造に沿って全 facade / 公開部品 / Internal を axiom で scaffold し、下流が import だけで再ビルド可能になる状態を作る。

### 6.1 作業手順

1. 各 facade に目次コメント（[architecture-layer-ab.md §3.1](architecture-layer-ab.md)）を整備
2. 各公開 API を `axiom` で宣言（signature のみ）
3. 各操作の `_rotateCW_comm` を axiom、`_rotate180_comm` / `_rotateCCW_comm` は CW 版からの 1 行系として `theorem` で定義
4. 各 `Internal/<ファイル>.lean` に「import 禁止」docstring を付与し、主要補助補題を axiom で scaffold
5. `Test/` の import を新 facade 経由に書換え、代表値テストのみ先行復活
6. Phase B 終了時のスナップショットを取得:
   - axiom 総数
   - facade 行数（全 facade）
   - 各ディレクトリのファイル数

### 6.2 注意

- この段階では **証明を書かない**。すべて axiom で通す
- signature 設計は [architecture-layer-ab.md §1.5 真偽検証先行原則](architecture-layer-ab.md) に従い、真と判明したものだけを axiom 化する
- axiom 数がスナップショットのベースラインとなり、Phase C/D で減少していくことを確認する

---

## 7. Phase B-R: 振り返り

**目的**: 公開 API 境界が Layer C/D 視点で妥当かを確認し、MECE 性を検証する。

### 7.1 チェック項目（共通振り返りチェックリスト）

- [x] **公開 API 境界の妥当性**  Internal が外部から参照されていないか / facade が薄すぎ・厚すぎでないか / Layer C から見て不足 API がないか 
- [x] **補題の MECE 性**  Defs / Behavior / Equivariance / Internal の区分が重複していないか / 層をまたぐ補題がないか / 同じ意味の補題が複数ないか
- [x] **再モデリング残存チェック**  §8.1.1〜§8.1.8 の 8 件再モデリングが計画通り完了しているか。新コード側に **旧モデルの残存が無い** ことを `grep_search` で確認: `genericBfs` / `GenericReachable` / `Option Shape` を返す Behavior 操作 / `axiom isSettled\s*:` / `axiom .*Shape\.swap\s*:` / `axiom Direction : Type` / `axiom Layer : Type` / `axiom Shape : Type` / `ofLayers.*Option` / `normalize.*Option` / Layer・Shape・QuarterPos 側の `rotateCW` axiom 等で 0 hit
- [x] **次レイヤからの使いやすさ**  Layer C/D が必要とする API が公開されているか / 使うのに Internal を覗く必要がないか
- [x] **認知負荷指標**  各ファイル行数（facade ≤ 150 / 一般 ≤ 300）/ 1 ディレクトリ内のファイル数（≤ 8）/ Internal ファイル数の爆発がないか

### 7.2 続行判断

チェック項目をすべて満たしたら Phase C に進む。
満たせない場合は Phase B に差し戻し、公開 API 境界の再設計や補題の整理を行う。
再モデリングを完了させるために Phase C へ持ち越す場合は、次のセクション「7.3 Phase C への持ち越しメモ」に記載すること。


### 7.3 Phase C への持ち越しメモ

**ステータス: 2026-04-27 完了**。 §8.1.1〜§8.1.8 の **8 件の再モデリング** を一括適用済み。
Phase B 末 184 axiom → Phase C 冒頭再 scaffold 後 125 axiom（**-59**）。
全項目の新コード残存チェック（`genericBfs` / `GenericReachable` / `Option Shape` 返り型 / 旧 axiom 群）は新コード側で 0 hit を確認済み。
Phase C 後半（§8.1 の 9. 以降、残 axiom の `def` / `theorem` / `inductive` / `structure` 化）に進む。

| # | 対象 | 旧モデル → 新モデル | axiom 差し引き見込み | 適用状況 |
|---|---|---|---|---|
| 1 | BFS / Cluster | `genericBfs` + `GenericReachable` + 閉包規則 + 健全性/完全性 → Mathlib `Relation.ReflTransGen` + `clusterSet : Finset` + `clusterList : List` + 橋渡し 1 本 | `-9 / +3`（最終 0） | ✅ |
| 2 | IsSettled | `IsSettled : Prop` + `isSettled : Bool` + `isSettled_iff` → `IsSettled` のみ primitive + `DecidablePred` instance | `-2 / +1` | ✅ |
| 3 | Option Shape 追放 | `gravity/cut/swap/stack/pinPush/normalize : … → Option Shape` → 全関数化（0 層許容）。Machine レイヤに `Option` を押し出す | 型簡潔化（axiom 数微減） | ✅ |
| 4 | Cutter / Swapper | `cut` / `halfDestroy` / `swap` を individual axiom → `eastHalf` / `westHalf` / `combineHalves` を primitive とした派生 `def` 合成 | `-4 / +0` | ✅ |
| 5 | Direction ≃ Fin 4 + Layer | `axiom Direction/Layer/QuarterPos : Type` + 各 `rotateCW` axiom → `Direction := Fin 4` / `Layer := Fin 4 → Quarter` / `QuarterPos := Nat × Fin 4` + 回転は算術、4 周性は `omega` | `-20 以上` | ✅ |
| 6 | Normalization | `IsNormalized` + `normalize : Shape → Option Shape` + `truncate` 独立 → `IsNormalized` primitive + `DecidablePred` + `normalize` 全関数派生 + Cluster 同規約 | `-1 / +2` | ✅ |
| 7 | Shape := List Layer | `axiom Shape : Type` + `ofLayers : … → Option Shape` + `layers/layerCount/…` → `Shape := List Layer` + 全操作 `def` 化 | `-12 以上` | ✅ |
| 8 | Prop/Bool 統一 | `isBonded` 等の Bool axiom → `IsBonded : Prop` + `DecidablePred` + `isBonded := decide` | axiom 統合 | ✅ |

合計で Phase B の 184 axiom のうち **59 本** が `def` / `theorem` / instance / `abbrev` に降格した。
さらに各操作の `rotate180_comm` / `rotateCCW_comm` を [§1.4 単一チェーン原則](architecture-layer-ab.md) に従い **CW 版からの 1 行系 `theorem`** で完備（Cutter / Swapper / Painter / Crystallize / Gravity / Stacker / PinPusher / Shatter / Settled / Bond）。
Phase D 以降で残り axiom（opaque 型 6 本 + 各操作の primitive と恒等式 + CW 等変性）を最終的に theorem / inductive / structure 化し、総 axiom 数 0 への収束を目指す。

詳細手順と管理ポイントは §8.1.1〜§8.1.8 を参照（実適用済みのため検証用記録として保持）。

---

## 8. Phase C: Layer A 脱 axiom 化（多セッション想定）

**目的**: Layer A の axiom を実証明に置換する。

### 8.1 着手順序（低リスク → 高リスク）

Phase B 終了時点で識別された **二重証明・多重抽象化パターン** および **型レベルの構造改善**（[§8.1.1〜§8.1.8](#)）は Phase C 冒頭で一括再 scaffold 済み（[§7.3](#73-phase-c-への持ち越しメモ) 参照、2026-04-27 完了）。
本節 9. 以降が Phase C 後半の作業対象（残 axiom の脱化）である。

1. ~~**Kernel 再 scaffold**（§8.1.1）~~ ✅ 2026-04-27 完了
2. ~~**IsSettled の DecidablePred 化**（§8.1.2）~~ ✅ 2026-04-27 完了
3. ~~**Behavior レイヤからの Option Shape 追放**（§8.1.3）~~ ✅ 2026-04-27 完了
4. ~~**Cutter / Swapper の合成化**（§8.1.4）~~ ✅ 2026-04-27 完了
5. ~~**Direction ≃ Fin 4 + Layer := Fin 4 → Quarter**（§8.1.5）~~ ✅ 2026-04-27 完了
6. ~~**Normalization 規約適用**（§8.1.6）~~ ✅ 2026-04-27 完了
7. ~~**Shape := List Layer（0 層許容）**（§8.1.7）~~ ✅ 2026-04-27 完了
8. ~~**Prop/Bool 二層規約の統一適用**（§8.1.8）~~ ✅ 2026-04-27 完了
9. `Shape/Types.lean` の opaque 型を inductive / structure に降格（`Color` / `Quarter` / `PartCode` / `RegularPartCode`）
10. `Shape/GameConfig.lean` の `GameConfig` を `structure` 化、`vanilla4` / `vanilla5` / `stress8` を具体値に
11. `Shape/Notation.lean`（round-trip 定理、既存資産移植）
12. `Kernel/Bond.lean`（`IsBonded` の具体定義、`IsBonded.symm` / `IsBonded.rotateCW` の証明）
13. `Kernel/Cluster.lean`（`clusterList` の具体実装、`clusterList.toFinset` / `clusterSet.rotateCW_comm` の証明）
14. `Operations/*.lean` の各 primitive を `def` 化し、CW 等変性 axiom を theorem に降格
15. `Wires/*.lean`（スケルトンのみ済ませ、実装は Layer C 着手時に延期してもよい）

**Phase C 開始ゲート**: §8.1.1〜§8.1.8 完了時点で `grep_search` により旧モデル（`genericBfs` / `GenericReachable` / `Option Shape` を返す Behavior 操作 / 旧 `isSettled` axiom ペア / `axiom Layer : Type` / `axiom Direction : Type` / Layer/Shape/QuarterPos の `rotateCW` axiom / `ofLayers.*Option` / `normalize.*Option`）が残存していないことを確認し、軽量レビュー（§8.3）を挟む。

### 8.1.1 Kernel 再 scaffold（Phase C 着手直後）

Phase B で axiom 化した `Kernel/BFS.lean` は **公開 API から廃止する**。過去の foldl モデルから継承された BFS 中心設計は、証明用途では過剰であり、また List 等式を介した等変性は過去に大量の探索順序補題を膨らませた。Mathlib `Relation.ReflTransGen` と `Finset` ベースのクラスタ表現へ移行する（詳細は [architecture-layer-ab.md §1.8](architecture-layer-ab.md)）。

**再 scaffold 手順**:

1. `S2IL/Kernel/BFS.lean` を `S2IL/Kernel/Cluster.lean` へリネームし、公開 API を入れ替え:
   - 廃止: `genericBfs` / `GenericReachable` とその閉包規則 4 本 / `genericBfs_sound` / `genericBfs_complete`（axiom 9 本削除）
   - 追加: `ClusterRel s := Relation.ReflTransGen (fun p q => isBonded s p q = true)`、`clusterSet : Shape → QuarterPos → Finset QuarterPos`（`noncomputable`）、`clusterList : Shape → QuarterPos → List QuarterPos`
   - 橋渡し: `clusterList_toFinset`（1 本）
2. `Kernel/Bond.lean` の `cluster` / `clusterList` / `allClusters` / `cluster_sound` / `cluster_complete` / `cluster_rotateCW` は `Kernel/Cluster.lean` へ移動する。`Bond.lean` は `isBonded` 一式（`isBondedInLayer` / `isBondedCrossLayer` / `isBonded` / `isBonded_symm` / `isBonded_rotateCW`）のみに減量
3. `Kernel/Internal/BFSImpl.lean` は `Kernel/Internal/ClusterImpl.lean` へリネームし、`clusterList` の実装専用に縮小。関係層（`ClusterRel`）に触れず、`clusterList_toFinset` を介してのみ証明側と接続する
4. 等変性は **Finset 等式のみ** で記述する: `clusterSet_rotateCW s start : clusterSet s.rotateCW start.rotateCW = (clusterSet s start).image QuarterPos.rotateCW`。`clusterList` の順序依存等式は導入しない
5. 180° / CCW の等変性は CW 系として 1 行で導出（単一チェーン原則）
6. `Kernel.lean` facade の目次コメントを更新し、BFS 記述を削除、Cluster を記載する

**管理上のポイント**:

- 関係層補題は Mathlib の `Relation.ReflTransGen.refl` / `.head` / `.tail` / `.lift` / `.mono` をそのまま使う。自前 `inductive` を再定義しない
- `clusterList` は `#eval` / 決定可能なテスト用途に限定し、証明側からは `clusterList_toFinset` 経由でのみ触る
- 過去の学び: 探索順序に踏み込む補題を持たないのが最重要。List 等式で等変性を述べたい誘惑は無視し、必ず Finset 側で述べる
- 汎用グラフ探索 API を要求するユースケースが Layer C/D で発生した場合は、都度 `Kernel/Internal/ClusterImpl.lean` から派生定義を取り出して `Kernel/` 直下の新規公開 API として設計し直す（Phase C 着手時点では先回りしない）

### 8.1.2 IsSettled の DecidablePred 化（Phase C 着手直後）

Phase B では `IsSettled : Shape → Prop` と `isSettled : Shape → Bool` を独立 axiom として並列宣言し、両者を `isSettled_iff` で橋渡ししている。これは Cluster と同型の「関係層 / 計算層 二重化」であり、Bool 側へ `isSettled_rotateCW : isSettled s.rotateCW = isSettled s` 等の重複 axiom を追加する誘惑が Phase C/D で発生する。単一 primitive に集約する。

**再 scaffold 手順**:

1. `S2IL/Operations/Settled.lean` の `axiom isSettled : Shape → Bool` と `axiom isSettled_iff` を削除
2. `IsSettled` のみを primitive（Phase C では axiom、最終的には具体 `def`）として残し、`instance : DecidablePred IsSettled` を宣言
3. `noncomputable def isSettled (s : Shape) : Bool := decide (IsSettled s)`（または `simp` 属性付きで `isSettled s = decide (IsSettled s)` を `@[simp] theorem` 化）
4. `isSettled_iff` は 1 行系 `theorem isSettled_iff : isSettled s = true ↔ IsSettled s := decide_eq_true_iff` として再定義
5. Bool 側の等変性補題（将来登場する `isSettled_rotateCW` 等）は `IsSettled.rotateCW` + `decide_congr` から自動導出し、個別 axiom 化しない

**管理上のポイント**:

- axiom 差し引き見込み: `-2`（`isSettled` / `isSettled_iff`）/ `+1`（`DecidablePred IsSettled`）。最終的に Phase C で `IsSettled` 自体が `def` 化されれば `DecidablePred` も instance 化され axiom 0 に収束
- `decide` 経路を通すため `IsSettled` の具体定義（Phase C §10.1 Step 1）で決定可能述語として構成する必要がある

### 8.1.3 Behavior レイヤからの Option Shape 追放（Phase C 着手直後）

Phase B では `gravity` / `cut` / `halfDestroy` / `swap` / `stack` / `pinPush` / `normalize` / `ofLayers` が `Option Shape` を返すが、これらの `none` は全て「結果が 0 層シェイプになる」ケースに対応している。0 層シェイプ（= 空リスト）を `Shape` 型に含めれば `Option` は不要であり、等変性の全てから `Option.map` / `Option.bind` が消えて型が大幅に簡潔化する。

Behavior レベルでは 0 層シェイプへの操作は自然に閉じる:
- `gravity empty = empty`（浮遊 0 → 変化なし）
- `cut empty = (empty, empty)`
- `paint empty c = empty`（対象象限 0）
- `placeAbove empty s = s`（0 層 + n 層 = n 層）
- `normalize empty = empty`

「装置は有効な入力が揃わないと出力しない」制約は **Machine レイヤ（Layer C/D）** の型で表現し、Behavior レイヤ（Layer A/B）からは `Option Shape` を追放する。

**再 scaffold 手順**:

1. `Shape` 型の定義を `List Layer`（0 層 = 空リスト）に変更（§8.1.7 と連動）。旧 `ofLayers : List Layer → Option Shape` は `Shape` 自身が `List Layer` なので不要に
2. `gravity : Shape → Shape` に全関数化。`gravity_isSettled (s : Shape) : IsSettled s.gravity` を追加、`gravity_of_isSettled : IsSettled s → s.gravity = s`（Phase D で theorem へ降格）
3. `cut : Shape → Shape × Shape` に全関数化（0 層入力 → `(empty, empty)`）。`Option.map` の等変性を直接等式に
4. `halfDestroy : Shape → Shape` / `swap : Shape → Shape → Shape × Shape` も同様に全関数化
5. `stack : Shape → Shape → GameConfig → Shape` / `pinPush : Shape → GameConfig → Shape` も全関数化
6. `normalize : Shape → Shape` の全関数化（§8.1.6 と連動、`Option` を外す）
7. 全操作の等変性 axiom から `Option.map` / `Prod.map (Option.map f) (Option.map g)` を除去し、直接等式に書き換え
8. `Stacker` / `PinPusher` 等の合成部分で `Option.bind` していた経路を単純関数合成に書き換え

**管理上のポイント**:

- axiom 数は変わらないが、**型シグネチャの簡潔化** により Phase D の合成証明が大幅に楽になる（`Option.map_map` 書換えが全滅）
- Machine レイヤ（Layer C/D）の入出力インタフェースで `Option` を導入する: `Machine.process : MachineInput → Option Shape`（入力不正で `none`）
- 0 層シェイプは `Shape.empty : Shape := []` として定義。`layerCount empty = 0` は `List.length_nil` から即座に得られる

### 8.1.4 Cutter / Swapper の合成化（Phase C 着手直後）

Phase B の Cutter/Swapper は E/W 依存のため `architecture-layer-ab.md §1.4.1` 例外規則で `rotate180` を primitive として許容しているが、以下の 6 本の axiom が個別に並んでいる:

```text
Shape.eastHalf_rotate180_comm
Shape.westHalf_rotate180_comm
Shape.cut_rotate180_comm
Shape.halfDestroy_rotate180_comm
Shape.halfDestroy_eq_cut_east
Shape.combineHalves_eastHalf_westHalf
```

`cut_rotate180_comm` は `eastHalf_*` + `westHalf_*` から、`halfDestroy_rotate180_comm` は `cut_*` + `halfDestroy_eq_cut_east` から導出可能で、`Swapper.swap` も `cut` + `combineHalves` の合成で書ける。

**再 scaffold 手順**:

1. Primitive に残す axiom: `eastHalf_rotate180_comm`, `westHalf_rotate180_comm`, `halfDestroy_eq_cut_east`, `combineHalves_eastHalf_westHalf`
2. `def Shape.cut (s : Shape) : Shape × Shape := (s.eastHalf, s.westHalf)` に差し替え、`cut_rotate180_comm` は `theorem` 化
3. `def Shape.halfDestroy (s : Shape) : Shape := s.eastHalf` に差し替え、`halfDestroy_rotate180_comm` は `theorem` 化（`halfDestroy_eq_cut_east` は `rfl` / `simp` で閉じる）
4. `def Shape.swap (s1 s2 : Shape) : Shape × Shape := (combineHalves s1.eastHalf s2.westHalf, combineHalves s2.eastHalf s1.westHalf)` に差し替え、`swap_rotate180_comm` を `theorem` 化
5. Swapper.lean から旧 `axiom Shape.swap` / `axiom swap_rotate180_comm` を削除

**管理上のポイント**:

- axiom 差し引き見込み: `-4`（`cut` / `halfDestroy_*` / `swap` / `swap_rotate180_comm`）/ `+0`
- `architecture-layer-ab.md §1.4.1` の E/W 例外対象は `eastHalf` / `westHalf` / `combineHalves` の 3 基本操作のみとなり、他は派生 `def` / `theorem` で統一

### 8.1.5 Direction ≃ Fin 4 + Layer := Fin 4 → Quarter（Phase C 着手直後）

Phase B では `Direction` / `Quarter` / `Layer` / `Shape` が全て opaque `axiom T : Type` であり、`rotateCW` / `rotateCW_four` が各層で独立 axiom 化されている。`Direction` を `Fin 4` で具体化し、`Layer` を `Fin 4 → Quarter` に再定義することで、回転が算術演算に降格し、axiom を大幅に削減できる。Mathlib の `Fin 4` / `ZMod 4` の環構造・巡回群補題が利用可能になる。

**再 scaffold 手順**:

1. `abbrev Direction := Fin 4` として具体化。`Direction.ne := 0`, `se := 1`, `sw := 2`, `nw := 3`
2. `def Direction.rotateCW (d : Direction) : Direction := d + 1`（`Fin 4` の加算は mod 4）
3. `Direction.rotateCW_four` は `theorem`：`d + 1 + 1 + 1 + 1 = d` は `omega` or `Fin.val_add` で即閉じ
4. `def Direction.adjacent (d1 d2 : Direction) : Bool := (d1 - d2 = 1) || (d2 - d1 = 1)`（`Fin 4` 上の±1 判定）
5. `def Direction.isEast (d : Direction) : Bool := d.val < 2`
6. `abbrev Layer := Fin 4 → Quarter`（関数型）
7. `def Layer.mk (ne se sw nw : Quarter) : Layer := ![ne, se, sw, nw]`（`Matrix.vecCons` リテラル）
8. `def Layer.rotateCW (l : Layer) : Layer := fun d => l (d - 1)`（index shift）
9. `Layer.rotateCW_four` は `theorem`：`ext d; simp [Layer.rotateCW]; ring_nf` で即閉じ
10. `def Layer.empty : Layer := fun _ => Quarter.empty`
11. `QuarterPos := Nat × Fin 4`（レイヤ番号 × 方角）。`QuarterPos.rotateCW (n, d) := (n, d + 1)`
12. `Shape.rotateCW s := s.map Layer.rotateCW`（`Shape = List Layer`、§8.1.7 と連動）
13. `Shape.rotateCW_four` は `theorem`：`List.map_map` + `Layer.rotateCW_four` + `funext` で即閉じ
14. `Shape.rotate180` / `rotateCCW` は既に単一チェーン（`rotateCW` の合成）なので追加対応不要
15. `Shape.mapLayers s f := s.map f`（`List.map` のエイリアス、定義が自明化）
16. 隣接判定の全 4 ケース（NE↔SE, SE↔SW, SW↔NW, NW↔NE）は `(d1 - d2 = 1) ∨ (d2 - d1 = 1)` の一式で統一

**管理上のポイント**:

- axiom 差し引き見込み: `axiom Direction : Type` / `axiom Layer : Type` / `axiom QuarterPos : Type` + 各 `rotateCW` + 各 `rotateCW_four` + `Layer.mk` / `Layer.empty` / `Layer.isEmpty` + `Direction.*` 合計 **-20 本以上**（Direction 8, Layer 4, QuarterPos 3, Shape 系 5 を `def` / `theorem` に降格）
- `Fin 4` は `DecidableEq` / `Fintype` を自動で持つため、`Direction.decEq` / `Direction.all` 等の axiom も不要に
- `Layer := Fin 4 → Quarter` は `Fintype` + `DecidableEq Quarter` から `DecidableEq Layer` を自動取得
- Mathlib `Equiv.addRight 1` (on `Fin 4`) を使えば回転を群作用として扱え、`MulAction` の補題群が利用可能
- E/W 判定（`isEast d ↔ d.val < 2`）は `omega` で全自動化

### 8.1.6 Normalization 規約適用（Phase C 着手直後）

Phase B では `IsNormalized : Shape → Prop` / `normalize : Shape → Option Shape` / `truncate : Shape → GameConfig → Shape` の三者が独立 axiom として並列している。`IsNormalized ↔ normalize s = some s` の橋渡しは未定義で、Phase C/D で別 axiom として導入すると Cluster / Settled と同型の二重化が再発する。Cluster と同じ規約（関係層 / 計算層 / 橋渡し 1 本）を事前適用する。

**再 scaffold 手順**:

1. Primitive に残す axiom: `IsNormalized`
2. `instance : DecidablePred IsNormalized` を宣言（§8.1.2 と同じ規約）
3. `noncomputable def normalize (s : Shape) : Shape := if IsNormalized s then s else truncate s defaultConfig`（または適切な既定処理）として派生定義化。`Option` を外す
4. `normalize_isNormalized : IsNormalized (normalize s)` / `normalize_of_isNormalized : IsNormalized s → normalize s = s` を `theorem` として導出
5. `truncate` は `GameConfig` 依存のため引き続き primitive に残すが、`truncate_isNormalized : IsNormalized (truncate s cfg)` を追加し `normalize` との関係を theorem で連結
6. `Shape/Types.lean` の `Shape.IsNormalized` docstring に「関係層 primitive / 計算層は `normalize` 派生 / Cluster §1.8 と同じ規約」と明記

**管理上のポイント**:

- axiom 差し引き見込み: `-1`（`normalize` の `Option` 版）/ `+1`（`DecidablePred IsNormalized`）+ `+1`（`truncate_isNormalized`）
- Normalization と Settled / Cluster が同一規約に揃うことで、Phase C/D の学習コストと補題発散を抑制
- `GameConfig` 依存（`truncate`）は例外として docstring で明記する

### 8.1.7 Shape := List Layer（0 層許容）（Phase C 着手直後）

Phase B では `axiom Shape : Type` + `axiom Shape.layers : Shape → List Layer` + `axiom Shape.ofLayers : List Layer → Option Shape` として Shape を opaque にしているが、§8.1.3（Option 追放）と §8.1.5（Layer := Fin 4 → Quarter）の帰結として、Shape を `List Layer`（= `List (Fin 4 → Quarter)`）に具体化する。

**再 scaffold 手順**:

1. `abbrev Shape := List Layer`（= `List (Fin 4 → Quarter)`）
2. `def Shape.empty : Shape := []`（0 層シェイプ）
3. `def Shape.layers (s : Shape) : List Layer := s`（identity）
4. `def Shape.ofLayers (ls : List Layer) : Shape := ls`（旧 `Option` ラッパの代わり。恒等関数として `Shape = List Layer` なので不要だが、名前は互換性のため残してもよい）
5. `def Shape.single (l : Layer) : Shape := [l]`、`double l1 l2 := [l1, l2]` 等はリストリテラル
6. `def Shape.layerCount (s : Shape) : Nat := s.length`
7. `def Shape.bottomLayer (s : Shape) : Layer := s.head? |>.getD Layer.empty`
8. `def Shape.topLayer (s : Shape) : Layer := s.getLast? |>.getD Layer.empty`
9. `def Shape.mapLayers (s : Shape) (f : Layer → Layer) : Shape := s.map f`
10. `def Shape.rotateCW (s : Shape) : Shape := s.map Layer.rotateCW`
11. `QuarterPos.getQuarter (s : Shape) (pos : QuarterPos) : Quarter := if pos.1 < s.length then s[pos.1]! pos.2 else Quarter.empty`（範囲外は空象限）
12. 旧 axiom `Shape.decEq` は `List.instDecidableEq` + `Layer` の `DecidableEq`（§8.1.5 で自動取得済）から instance 化

**管理上のポイント**:

- axiom 差し引き見込み: `axiom Shape : Type` + `layers` / `ofLayers` / `single` / `double` / `triple` / `quadruple` / `layerCount` / `bottomLayer` / `topLayer` / `mapLayers` / `decEq` 等 **-12 本以上** が `def` / instance に降格
- `layerCount_rotateCW` は `List.length_map` から即座に得られ、axiom 不要
- `placeAbove_layerCount` は `List.length_append` から即座
- `Shape.empty` を許容することで §8.1.3 の Option 追放が成立する
- Layer C/D で「1 層以上の Shape」が必要な場面では `Subtype (fun s : Shape => 0 < s.length)` または `Structure { layers : List Layer // layers ≠ [] }` を使い、型制約で表現する

### 8.1.8 Prop/Bool 二層規約の統一適用（Phase C 着手直後）

§8.1.2（IsSettled）と §8.1.6（IsNormalized）で個別に導入した `DecidablePred` 規約を、類似の Prop/Bool ペアを持つ他のシンボルにも横展開する。

**対象**:

| シンボル | 規約適用 |
|---|---|
| `IsSettled` | §8.1.2 で対応済 |
| `IsNormalized` | §8.1.6 で対応済 |
| `isBondedInLayer` / `isBondedCrossLayer` / `isBonded` | Prop 版 `IsBonded` を定義し `instance : Decidable (IsBonded s p q)` を宣言。`isBonded s p q := decide (IsBonded s p q)` に派生化。現状 axiom の `isBonded_symm` は `IsBonded.symm` に |
| `Quarter.isEmpty` / `Quarter.canFormBond` / `Quarter.isFragile` | Phase C で `Quarter` を具体化する際に `match` ベースの `def` にするため、`Decidable` 化は自然に成立 |

**管理上のポイント**:

- `isBonded` 系は `Kernel/Bond.lean` で `IsBonded : Shape → QuarterPos → QuarterPos → Prop` として Prop 版を定義し、`isBonded := decide` とする。`ClusterRel` の定義が `Relation.ReflTransGen (fun p q => IsBonded s p q)` に単純化される（Bool → Prop 変換が不要に）
- axiom 差し引き: `isBonded` / `isBondedInLayer` / `isBondedCrossLayer` の 3 axiom は `IsBonded` の合成定義に統合可能（Phase C で要検討）

### 8.2 各補題の着手前に

- [architecture-layer-ab.md §1.5 真偽検証先行原則](architecture-layer-ab.md) に従い真偽確認
- `lean-proof-planning` skill でゴール形状を確認
- 反例が出たら signature を修正し再検証

### 8.3 Phase 内軽量レビュー

大きな単位（例: Kernel 全体完了時、Operations の Defs 全完了時）ごとに §11.1 のチェックリストを軽量実施し、違反があればその場で修正する。

---

## 9. Phase C-R: 振り返り（Layer A）

**目的**: Layer A 完了時点で Layer B 側から見た使いやすさを検証し、Internal のデッド補題を削除する。

### 9.1 チェック項目

- §7.1 の共通チェックリストを実施
- Layer B の 1 補題（例: Gravity の終端性か単純な等変性）を試し書きしてワーキングメモリ消費と摩擦を計測
- `grep_search` で参照 0 の Internal 補題を列挙し削除候補リストを作成

### 9.2 続行判断

- Layer A の axiom = 0
- デッド補題レビュー完了
- Layer B 着手のための公開 API が揃っていることを確認

---

## 10. Phase D: Layer B 脱 axiom 化（多セッション想定）

**目的**: Layer B の axiom を実証明に置換する。

### 10.1 着手順序（低リスク → 高リスク）

1. `Operations/Settled.lean`（構造的）
2. `Operations/Shatter.lean`（Cluster 基盤が済んでいる前提）
3. `Operations/Gravity.lean` の Basic / Descent / Place 相当（旧 `Gravity/Defs.lean`, `Descent.lean`, `Place.lean` 系）
4. `Operations/Gravity/` の GroundingMono 単純部（旧 B1〜B3a 相当）
5. `Operations/Gravity/Internal/` の書込・値保存系
6. `Operations/Gravity/` の GroundingMono 複雑帰納（旧 B3b 相当）
7. `Operations/Gravity/` の ProcessWave 終端性（旧 `waveStep_ngs_strict_bound` 相当）
8. Behavior 付き操作（`Stacker.lean` / `Cutter.lean` / `Swapper.lean` / `PinPusher.lean`）

### 10.2 注意

- 旧 gravity 計画のリスクが Phase D に継承される。特に GroundingMono 複雑帰納は Internal/Place の再設計を先に完了させてから着手する
- 等変性は各操作につき CW 版のみを証明し、180° / CCW は facade の 1 行系で済ませる

---

## 11. Phase D-R: 振り返り（Layer B）

§7.1 の共通チェックリストを実施したうえで、Layer C/D から見た api 不足を先取り確認する。

**特に**:

- Layer C のフロー定義から見て、`Operations.lean` だけを import すれば完結するか
- MAM（Layer D）の完全性証明で参照が予想される定理（例: Stacker の `placeAbove ∘ gravity` の構造的保存則）が公開されているか

---

## 12. Phase E: 総仕上げ（1〜2 セッション想定）

**目的**: 全 Phase の整合を取り、`_archive/` を削除し、関連ドキュメントを更新する。

### 12.1 作業項目

- [ ] `S2IL/_archive/pre-greenfield/` に `pre-greenfield-yyyymmdd` タグを付与して削除（git 履歴で参照可能）
- [ ] [MILESTONES.md](MILESTONES.md) の Layer A / B の記述を新構造に合わせて更新
- [ ] `sorry-plan.json` / `sorry-goals.md` / `sorry-cards/` のクリーンアップ
- [ ] `.github/skills/` の Lean 関連スキルから `_agent` 依存記述を完全除去
- [ ] 各 facade に Layer C 向けの README コメントを追記（どう使うか、典型的な呼び出しパターン）
- [ ] axiom = 0, sorry = 0 の最終確認
- [ ] 認知負荷指標の最終スナップショットを §13 に記録

### 12.2 成功基準

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

## 13. リスクと mitigation

| リスク | mitigation |
|---|---|
| 下流が旧 private 補題に依存していた | Phase A 前に `grep_search -r "import S2IL\."` で全下流依存を洗い出す。`Internal/` 直接 import があれば移植候補リストに記録 |
| 再構築中に Layer B GroundingMono が再び破綻 | Phase D-5（Internal/Place の再設計）を Phase D-6 より先に完遂してから着手 |
| CW 等変性の主証明が難航 | 既存資産（`processWave_rotate180_comm` など）の証明構造を §4.2 Step 2 で評価してから移植テンプレートとして採用する。ただし rotate180 専用の中間補題は系化して捨てる |
| 既存証明に設計バグ（偽前提依存・旧構造特有の迂回）が潜んでいた | §4.2 Step 2 のアプローチ品質評価で検出する。全体流用せず、証明の発想のみ参考にして補題定義・証明本体は再実装する |
| インデックス廃止で agent のコンテキスト探索が悪化 | facade 目次コメントと行数上限を硬く守る。Phase A-R でサンプルタスク実測を行い、違反があれば facade 設計を是正 |
| `_archive/` 読込でコンテキスト溢れ | `_archive/` は明示指示がない限り `read_file` しない。symbol 検索対象からも除外（インデックス廃止後はそもそも対象にならない） |
| デッド補題の判断ミスで必要な補題を消す | フェーズ末レビューでは削除候補リストを先に作り、次フェーズ着手時に実際に必要かを再確認してから削除 |

---

## 14. 関連

| 参照先 | 用途 |
|---|---|
| [architecture-layer-ab.md](architecture-layer-ab.md) | 構造の正本 |
| [MILESTONES.md](MILESTONES.md) | 上位の最終目標 |
| [docs/agent/proof-plan-current-focus-guide.md](../agent/proof-plan-current-focus-guide.md) | 新規 sorry 着手時の手順 |
| [docs/agent/proof-retreat-pivot-guide.md](../agent/proof-retreat-pivot-guide.md) | 撤退判断基準 |
| [.github/skills/lean-counterexample/SKILL.md](../../.github/skills/lean-counterexample/SKILL.md) | 真偽検証 |
| [S2IL/_agent/sorry-plan.json](../../S2IL/_agent/sorry-plan.json) | sorry / axiom の最新状態 |
