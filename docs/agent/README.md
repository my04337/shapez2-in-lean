# エージェントカスタマイズ

GitHub Copilot のエージェント動作をカスタマイズするためのドキュメント群の入口ページです。

Skills・Hooks の追加・修正時にはまずここを参照すること。

---

## ファイル一覧

| ファイル | 概要 |
|---|---|
| [opus-47-design-principles.md](opus-47-design-principles.md) | Opus 4.7 向けエージェント・スキル設計原則。委任思想・サブエージェント 5 原則・スキル 3 原則・指示文の書き方 |
| [custom-agent-guide.md](custom-agent-guide.md) | カスタムエージェント ベストプラクティスガイド。`.agent.md` のフォーマット・設計パターン |
| [skill-authoring-guide.md](skill-authoring-guide.md) | Agent Skills 記述ガイド。SKILL.md のフォーマット・ベストプラクティス |
| [hooks-guide.md](hooks-guide.md) | GitHub Copilot Hooks リファレンス。ライフサイクルイベント・設定 |
| [agent-operations-playbook.md](agent-operations-playbook.md) | AGENTS.md から移設した詳細運用ルール集。検索閾値・撤退基準・編集ツール方針 |
| [session-memory-guide.md](session-memory-guide.md) | セッションメモリ運用ガイド。テンプレート・更新ルール・クリーンアップ手順 |
| [proof-plan-current-focus-guide.md](proof-plan-current-focus-guide.md) | 証明計画策定時の Current Focus 整備手順。計画ファイル・sorry-plan.json の一貫した作成チェックリスト |
| [proof-retreat-pivot-guide.md](proof-retreat-pivot-guide.md) | 証明の撤退・pivot 判断手順。sorry-card マイルストーン記述テンプレート・`remaining_steps` status の使い分け |
| [powershell-conventions.md](powershell-conventions.md) | PowerShell 文字列置換の規則 |
| [license-policy.md](license-policy.md) | 外部ライブラリのライセンス方針 |

---

## `lake build` 成功時の自動生成物

`lake build` が成功すると `.github/skills/lean-tooling/scripts/build.ps1` が以下を自動実行する。

| 生成物 | 目的 | 手動起動スクリプト（デバッグ用のみ） |
|---|---|---|
| `S2IL/_agent/sorry-goals.md` | sorry 宣言シグネチャ（常時最新） | `update-sorry-goals.ps1` |

Phase A (2026-04-24) で `sig-digest` / `symbol-map` / `extract-goal-context` / sorry-card context 事前埋込は廃止された。
シンボル位置の特定は facade (`S2IL/<Namespace>.lean`) の冒頭目次を出発点に `grep_search` を使う。

> **手動実行は通常不要**。スクリプト修正・デバッグ時のみ直接実行する。

---

## エージェント一覧

`.github/agents/` 配下の 4 エージェント。設計原則は [opus-47-design-principles.md](opus-47-design-principles.md) を参照。

| エージェント | 役割 | 主な用途 |
|---|---|---|
| `lean-build-doctor` | `lake build` 後の診断スキャン（エラー triage + sorry インベントリ） | セッション開始 / 大きな編集後 / コミット前の健康診断 |
| `lean-theorem-investigator` | 1 件の theorem 候補 / 既存 sorry / def 挙動を反例→ゴール→補題探索→タクティク試行で調査 | 単一 theorem target の triage、複数 target の並列 fan-out |
| `lean-simp-stabilizer` | 1 行の `simp` を `simp only [...]` に安定化 | コミット前の bare simp 解消 |
| `lean-session-restorer` | 前回記録・現状 build・未完 target を復元（内部で build-doctor + theorem-investigator を委任） | セッション再開・`/compact` 後の復元 |

---

## スキル一覧

| スキル | 概要 | 発動条件 |
|---|---|---|
| `lean-tooling` | build / REPL / run / setup と Windows terminal safety の統合入口 | Lean 実行系コマンド・JSONL・PATH 確認 |
| `lean-diagnostics` | 診断 JSONL の解析と error pattern → 修正クラスのルーティング | エラー分類ロジックの参照 |
| `lean-proof-methods` | 反例・タクティク選択・補題探索・証明計画・撤退判断の統合参照 | theorem / lemma の証明戦略決定時 |
| `lean-simp-guide` | simp 系比較とバルク安定化パイプライン | simp 系判断・10 行超のバルク変換 |
| `s2il-proof-workflow` | facade-first 探索、Layer A/B、Prop/Bool bridge、validation の S2IL 固有運用 | S2IL theorem 化・仕様照合・文書更新 |

実行系 scripts と詳細資料は `lean-tooling/scripts/`・`lean-tooling/references/` に集約済み。証明方法系の本文と追加資料は `lean-proof-methods/references/` に集約済み。

---

## エージェント向け参照ガイダンス

### いつ参照するか

| 作業 | 参照先 |
|---|---|
| 新しいカスタムエージェントの作成 | `custom-agent-guide.md` |
| 既存カスタムエージェントの修正 | `custom-agent-guide.md` |
| 新しい Skill の作成 | `skill-authoring-guide.md` |
| 既存 Skill の修正・デバッグ | `skill-authoring-guide.md` |
| Hook の追加・設定変更 | `hooks-guide.md` |
| エージェントの動作がおかしい場合 | 両方を確認し、設定の整合性をチェック |

### 新規ファイルの追加基準

- **追加する**: 新しいカスタマイズ手法（Agent modes、prompt files 等）のガイドを文書化する場合
- **ファイル名**: 機能名をケバブケースで（例: `agent-modes-guide.md`）
- 新規ファイルを追加した際は、この README のファイル一覧にも追記すること
