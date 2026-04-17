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
| [gravity-proof-execution-plan.md](gravity-proof-execution-plan.md) | Gravity 証明 統合実行計画（Plan B）。axiom インベントリ・SettledShape 完了計画・rCW/rCCW 等変性・Wave Gravity Model ロードマップ・リファクタリング計画を統合 |
| [codebase-restructure-plan.md](codebase-restructure-plan.md) | コード分割単位見直し計画。分割案 A〜D の比較、段階導入プラン、Appendix の具体ディレクトリ構成案を整理 |

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

### 新規ファイルの追加基準

- **追加する**: 新しい大規模な証明計画・アプローチ調査を開始する場合
- **追加しない**: 小規模な証明（1〜2 sorry 程度）は `docs/s2il/` に知見として記録する
- **ファイル名**: 対象をケバブケースで（例: `stacker-equivariance-proof-plan.md`）
- 新規ファイルを追加した際は、この README のファイル一覧にも追記すること
