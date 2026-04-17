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
| [protected-wip-workflow.md](protected-wip-workflow.md) | REPL 対応スコープ管理。private / protected の使い分けと WIP 証明中の一時公開フロー |
| [session-memory-guide.md](session-memory-guide.md) | セッションメモリ運用ガイド。テンプレート・更新ルール・クリーンアップ手順 |

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
