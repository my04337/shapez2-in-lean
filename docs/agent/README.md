# エージェントカスタマイズ

GitHub Copilot のエージェント動作をカスタマイズするためのドキュメント群の入口ページです。

Skills・Hooks の追加・修正時にはまずここを参照すること。

---

## ファイル一覧

| ファイル | 概要 |
|---|---|
| [skill-authoring-guide.md](skill-authoring-guide.md) | Agent Skills 記述ガイド。SKILL.md のフォーマット・ベストプラクティス |
| [hooks-guide.md](hooks-guide.md) | GitHub Copilot Hooks リファレンス。ライフサイクルイベント・設定 |

---

## エージェント向け参照ガイダンス

### いつ参照するか

| 作業 | 参照先 |
|---|---|
| 新しい Skill の作成 | `skill-authoring-guide.md` |
| 既存 Skill の修正・デバッグ | `skill-authoring-guide.md` |
| Hook の追加・設定変更 | `hooks-guide.md` |
| エージェントの動作がおかしい場合 | 両方を確認し、設定の整合性をチェック |

### 新規ファイルの追加基準

- **追加する**: 新しいカスタマイズ手法（Agent modes、prompt files 等）のガイドを文書化する場合
- **ファイル名**: 機能名をケバブケースで（例: `agent-modes-guide.md`）
- 新規ファイルを追加した際は、この README のファイル一覧にも追記すること
