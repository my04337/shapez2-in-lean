# Layer A/B Greenfield Rewrite 実施計画

- 作成日: 2026-04-24
- 最終更新: 2026-04-24
- ステータス: **Phase A 完了 / Phase B 着手前**
- スコープ: S2IL Layer A（Shape / Kernel / Operations 純粋部 / Wires スケルトン / Machine）および Layer B（振る舞い系）の再構築
- 関連: 構造の正本は [architecture-layer-ab.md](architecture-layer-ab.md)、前身は [archive/gravity-greenfield-rewrite-plan.md](archive/gravity-greenfield-rewrite-plan.md)

---

## 0. この計画の位置付け

本ドキュメントは「何を・どの順で実施するか」を定める **手順書** である。構造そのものの拘束条件は [architecture-layer-ab.md](architecture-layer-ab.md) に委譲する。両者の役割分担:

| ドキュメント | 責務 |
|---|---|
| `architecture-layer-ab.md` | 構造の正本（ディレクトリ・API 境界・MECE・命名・サイズ上限） |
| `layer-ab-rewrite-plan.md`（本書） | Phase 構成・着手順序・振り返り手順・リスク管理 |

前身の [archive/gravity-greenfield-rewrite-plan.md](archive/gravity-greenfield-rewrite-plan.md) は Layer B の Gravity 層のみを対象としていた。本計画はそのスコープを **Layer A 全体 + Layer B 全体** に拡張し、従来 `S2IL/_agent/` で支えてきたインデックス機構を **廃止** する前提で新構造を設計する。

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
- [x] 既存 `gravity-greenfield-rewrite-plan.md` を [archive/](archive/) へ移動
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

- [ ] サンプルタスク 1 件（例: 「Shape の round-trip 定理の位置を特定して」）を `_agent/` インデックスなしで実行し、ワーキングメモリ消費が許容範囲か確認
- [ ] `_archive/` 参照がコンテキスト溢れを起こさないことを確認（Phase A では空 facade のみなので基本的に `_archive/` は読まない想定）
- [ ] `S2IL/AGENTS.md` / `AGENTS.md`（ルート）/ `.github/skills/` の `_agent` 依存記述を更新
  - 「symbol-map.jsonl を grep」等の手順を削除
  - 「facade から読み始める」への置換
- [ ] `docs/agent/` 配下の関連ドキュメント（`proof-plan-current-focus-guide.md` など）の `_agent` 参照を洗い出し、必要なら追補

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

| 観点 | 確認内容 |
|---|---|
| **公開 API 境界の妥当性** | Internal が外部から参照されていないか / facade が薄すぎ・厚すぎでないか / Layer C から見て不足 API がないか |
| **補題の MECE 性** | Defs / Behavior / Equivariance / Internal の区分が重複していないか / 層をまたぐ補題がないか / 同じ意味の補題が複数ないか |
| **次レイヤからの使いやすさ** | Layer C/D が必要とする API が公開されているか / 使うのに Internal を覗く必要がないか |
| **認知負荷指標** | 各ファイル行数（facade ≤ 150 / 一般 ≤ 300）/ 1 ディレクトリ内のファイル数（≤ 8）/ Internal ファイル数の爆発がないか |

### 7.2 続行判断

指標を `docs/plans/layer-ab-rewrite-plan.md` の末尾に付録として記録する（本書の「付録 A: Phase 末スナップショット」セクション）。逸脱項目があれば Phase B を延長して是正する。

---

## 8. Phase C: Layer A 脱 axiom 化（多セッション想定）

**目的**: Layer A の axiom を実証明に置換する。

### 8.1 着手順序（低リスク → 高リスク）

1. `Shape/Types.lean` + `Shape/GameConfig.lean`（構造的性質のみ）
2. `Shape/Notation.lean`（round-trip 定理、既存資産移植）
3. `Kernel/Bond.lean`
4. `Kernel/BFS.lean`（完全性定理、既存資産が効く）
5. `Kernel/Transform.lean`（CW / 180° / CCW の基本等式と `rotate180_eq_rotateCW_rotateCW`）
6. `Operations/*.lean` の Defs 部分（純粋関数定義）
7. 各操作の `Equivariance.lean`（CW 等変性のみ）
8. `Wires/*.lean`（スケルトンのみ済ませ、実装は Layer C 着手時に延期してもよい）

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
2. `Operations/Shatter.lean`（BFS 基盤が済んでいる前提）
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

## 13. 付録 A: Phase 末スナップショット

各 Phase 終了時に次の指標を追記する（Phase ごとにセクション追加）。

### Phase A 終了時

- 実施日: 2026-04-24
- axiom 数: 0（空 facade のみ）
- sorry 数: 0
- warning 数: 0
- facade 行数一覧:
  - `S2IL.lean`: 26 行
  - `S2IL/Shape.lean`: 26 行
  - `S2IL/Kernel.lean`: 24 行
  - `S2IL/Wires.lean`: 24 行
  - `S2IL/Operations.lean`: 37 行
  - `S2IL/Machine.lean`: 18 行
- `_agent/` 削除済みファイル:
  - `symbol-map.jsonl`
  - `dep-graph-baseline.json`
  - `sig-digest/` (45 ファイル)
  - `route-map.json`
  - `query-playbook.json`
- 廃止スクリプト:
  - `update-symbol-map.ps1` / `update-symbol-map.sh`
  - `update-sig-digest.ps1`
  - `update-sorry-card-context.ps1`
  - `extract-goal-context.ps1`
- 退避先:
  - `S2IL/_archive/pre-greenfield/` (Shape / Kernel / Operations / Machine / Kernel.lean / Operations.lean / SettledShape.lean / S2IL.lean)
  - `_archive/pre-greenfield/Test/`
  - `_archive/pre-greenfield/Verification/`
  - `_archive/pre-greenfield/DevTool/Toolkit/` + `Toolkit.lean`
- lakefile 変更:
  - `defaultTargets` から `Test` を除外
  - `[[lean_lib]] Test` セクション削除
  - `[[lean_exe]] s2il-toolkit` セクション削除
- 特記事項:
  - clean build green、2026-04-24 時点の toolchain (Lean 4.29.0) で再現
  - `s2il-diag` は S2IL 非依存なので継続利用可能
  - `_archive/pre-greenfield/` は Phase E で `pre-greenfield-yyyymmdd` タグ付与後に削除予定

### Phase B 終了時

（以下、Phase C / D / E も同様）

---

## 14. リスクと mitigation

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

## 15. 関連

| 参照先 | 用途 |
|---|---|
| [architecture-layer-ab.md](architecture-layer-ab.md) | 構造の正本 |
| [MILESTONES.md](MILESTONES.md) | 上位の最終目標 |
| [archive/gravity-greenfield-rewrite-plan.md](archive/gravity-greenfield-rewrite-plan.md) | 本計画の前身（Gravity 限定）|
| [docs/agent/proof-plan-current-focus-guide.md](../agent/proof-plan-current-focus-guide.md) | 新規 sorry 着手時の手順 |
| [docs/agent/proof-retreat-pivot-guide.md](../agent/proof-retreat-pivot-guide.md) | 撤退判断基準 |
| [.github/skills/lean-counterexample/SKILL.md](../../.github/skills/lean-counterexample/SKILL.md) | 真偽検証 |
| [S2IL/_agent/sorry-plan.json](../../S2IL/_agent/sorry-plan.json) | sorry / axiom の最新状態 |
