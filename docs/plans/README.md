# 計画・マイルストーン

S2IL プロジェクトの開発計画・マイルストーン・証明アプローチの検討資料をまとめた入口ページです。

マイルストーンの更新や証明計画の策定時にはまずここを参照すること。

---

## ファイル一覧

### プロジェクト管理

| ファイル | 概要 |
|---|---|
| [MILESTONES.md](MILESTONES.md) | マイルストーン チェックシート。フェーズ 0〜 の各タスクと達成状況を管理 |

### 証明計画

| ファイル | 概要 |
|---|---|
| [gravity-greenfield-rewrite-plan.md](gravity-greenfield-rewrite-plan.md) | **2026-04-23 新規**: Gravity 層を archive + skeleton + de-axiomatization の 3 phase で再構築する計画（第58報で基盤反例確定を受けて策定）|
| [gravity-proof-execution-plan.md](gravity-proof-execution-plan.md) | Gravity 証明 統合実行計画（Plan B）。axiom インベントリ・確立済みの事実・Gravity モジュール概要・Wave Gravity Model ロードマップを統合 |
| [s1-proof-plan.md](s1-proof-plan.md) | S1 axiom (`waveStep_nonGroundedLayerSum_lt`) 証明計画。Telescoping Sum 戦略・sub-lemma 分解（証明状況は sorry-card 参照） |

### インフラ改善提案

| ファイル | 概要 |
|---|---|
| [agent-efficiency-proposals.md](agent-efficiency-proposals.md) | エージェントのコンテキスト消費削減提案。Tier 1 は 2026-04-23 適用済み（sig-digest / extract-goal-context / セッション圧縮ルール）、Tier 2・3 は保留 |

**現在のフォーカス**: Gravity 層の Greenfield Rewrite（`gravity-greenfield-rewrite-plan.md`）
→ Step B3b `placeLDGroups_landing_groundingEdge_mono` は第59報で一時 axiom 化（sorry = 0）

アーカイブ済: `archive/session-efficiency-followup-plan.md`（2026-04-21 に一通り適用済みのため退避）

---

## エージェント向け参照ガイダンス

### いつ参照するか

| 作業 | 参照先 |
|---|---|
| マイルストーンの確認・更新 | `MILESTONES.md` |
| 落下処理に関わる実装・証明 | `../shapez2/falling.md` + `../shapez2/adjacency.md` + `gravity-proof-execution-plan.md` |
| 新しい証明に着手する前 | 既存の証明計画ファイルを確認し、関連する計画がないか調べる |
| 証明が難航した場合 | 既存のアプローチ候補を確認し、代替戦略を検討 |
| 証明が完了した場合 | 該当する計画ファイルとマイルストーンを更新 |

### 証明計画の新規作成

新しい証明計画を策定するときは **必ず** `docs/agent/proof-plan-current-focus-guide.md` の手順に従い、
Current Focus セクション・sorry-plan.json エントリ・sorry-cards を同時に整備すること。

### 新規ファイルの追加基準

- **追加する**: 新しい大規模な証明計画・アプローチ調査を開始する場合
- **追加しない**: 小規模な証明（1〜2 sorry 程度）は `docs/s2il/` に知見として記録する
- **ファイル名**: 対象をケバブケースで（例: `stacker-equivariance-proof-plan.md`）
- 新規ファイルを追加した際は、この README のファイル一覧にも追記すること
