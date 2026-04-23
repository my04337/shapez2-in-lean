# エージェントカスタマイズ

GitHub Copilot のエージェント動作をカスタマイズするためのドキュメント群の入口ページです。

Skills・Hooks の追加・修正時にはまずここを参照すること。

---

## ファイル一覧

| ファイル | 概要 |
|---|---|
| [custom-agent-guide.md](custom-agent-guide.md) | カスタムエージェント ベストプラクティスガイド。`.agent.md` のフォーマット・設計パターン |
| [skill-authoring-guide.md](skill-authoring-guide.md) | Agent Skills 記述ガイド。SKILL.md のフォーマット・ベストプラクティス |
| [hooks-guide.md](hooks-guide.md) | GitHub Copilot Hooks リファレンス。ライフサイクルイベント・設定 |
| [license-policy.md](license-policy.md) | 外部ライブラリのライセンス方針 |
| [powershell-conventions.md](powershell-conventions.md) | PowerShell 文字列置換の規則 |
| [session-memory-guide.md](session-memory-guide.md) | セッションメモリ運用ガイド。テンプレート・更新ルール・クリーンアップ手順 |
| [agent-operations-playbook.md](agent-operations-playbook.md) | AGENTS.md から移設した詳細運用ルール集。検索閾値・撤退基準・編集ツール方針 |
| [proof-plan-current-focus-guide.md](proof-plan-current-focus-guide.md) | 証明計画策定時の Current Focus 整備手順。計画ファイル・sorry-plan.json・sorry-cards の一貫した作成チェックリスト |
| [proof-retreat-pivot-guide.md](proof-retreat-pivot-guide.md) | 証明の撤退・pivot 判断手順。sorry-card マイルストーン記述テンプレート・`remaining_steps` status の使い分け |
| [repl-session-state-guide.md](repl-session-state-guide.md) | REPL セッション状態ファイル (`Scratch/_state/`) の書式・運用 |

アーカイブ済: `archive/` 配下（subagent 最適化提案 2026-04-18、内容は AGENTS.md / 各スキルに吸収済み）

---

## `lake build` 成功時の自動生成物

`lake build` が成功すると `.github/skills/lean-build/scripts/build.ps1` が以下を自動実行する。

| 生成物 | 目的 | 手動起動スクリプト（デバッグ用のみ） |
|---|---|---|
| `S2IL/_agent/sig-digest/*.md` | ファイル概観・宣言行インデックス | `update-sig-digest.ps1` |
| `S2IL/_agent/symbol-map.jsonl` | シンボル名 → `line`/`endLine`/`digest` の逆引き | `update-symbol-map.ps1` |
| `S2IL/_agent/sorry-goals.md` | sorry 宣言シグネチャ（常時最新） | `update-sorry-goals.ps1` |
| `S2IL/_agent/sorry-cards/*.md` の候補補題セクション | extract-goal-context 出力の事前埋込 | `update-sorry-card-context.ps1` |

> **手動実行は通常不要**。スクリプト修正・デバッグ時のみ直接実行する。

---

## スキル一覧

| スキル | 概要 | 発動条件 |
|---|---|---|
| `lean-error-fixer` | ビルドエラーの自動分類・修正候補生成・REPL 検証 | ビルドエラーの修正を依頼された場合 |
| `lean-session-restorer` | セッション再開準備の自動化（差分比較・WIP 確認・着手推奨） | セッション再開・作業再開を依頼された場合 |
| `session-efficiency` | セッションの効率分析・改善提案 | **手動実行のみ**。明示的に指示された場合 |

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
