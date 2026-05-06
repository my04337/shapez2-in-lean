# S2IL プロジェクト固有ナレッジ

S2IL（Shapez2 in Lean）プロジェクトに固有の技術知識・分析資料・補題インデックスを集約するディレクトリです。

一般的な Lean 4 やゲームシステムの情報とは区別し、**このプロジェクトのコードベース・証明チェーンに直結する知見**をここに配置します。

---

## ファイル一覧

### コードベース索引

| ファイル | 概要 |
|---|---|
| [game-config.md](game-config.md) | GameConfig（ゲーム設定）の設計方針・プリセット一覧 |

### 証明パターン・分析

| ファイル | 概要 |
|---|---|
| [architecture-layer-ab.md](architecture-layer-ab.md) | Layer A/B のディレクトリ構造・設計原則・主要 theorem チェーンの正本 |
| [mam-foundation-theorems.md](mam-foundation-theorems.md) | MAM 前提 theorem の完了済み inventory。象限抽出フロー例・Stacker correctness・残る強化条件 |
| [proof-workflow-playbook.md](proof-workflow-playbook.md) | S2IL/AGENTS.md から移設した証明運用の詳細ルール（Proof-First-Test・REPL 優先・探索閾値） |

---

## アーキテクチャ決定記録

現行アーキテクチャの正本は [architecture-layer-ab.md](architecture-layer-ab.md) を参照。

---

## エージェント向け参照ガイダンス

### いつ参照するか

| 作業 | 参照先 |
|---|---|
| 新しい証明に着手する前 | `proof-workflow-playbook.md` を確認 |
| MAM 前提 theorem の現状を確認 | `mam-foundation-theorems.md` を確認 |
| 等変性証明を書く | `architecture-layer-ab.md` の単一チェーン原則と主要 theorem チェーンを確認 |
| sorry の状態を確認 | `S2IL/_agent/sorry-plan.json` |

### 新規ファイルの追加基準

- **追加する**: S2IL プロジェクトのコードベースに直結する技術知見・分析結果
- **追加しない**: 一般的な Lean 4 Tips → `docs/lean/`、ゲーム仕様 → `docs/shapez2/`、開発計画 → `docs/plans/`
- **ファイル名**: ケバブケースで内容を表す（例: `stacker-equivariance-analysis.md`）
- 新規ファイルを追加した際は、この README のファイル一覧にも追記すること
