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
| [proof-plan-current-focus-guide.md](proof-plan-current-focus-guide.md) | 証明計画策定時の Current Focus 整備手順。計画ファイル・sorry-plan.json・sorry-cards の一貫した作成チェックリスト |
| [proof-retreat-pivot-guide.md](proof-retreat-pivot-guide.md) | 証明の撤退・pivot 判断手順。sorry-card マイルストーン記述テンプレート・`remaining_steps` status の使い分け |
| [repl-session-state-guide.md](repl-session-state-guide.md) | REPL セッション状態ファイル (`Scratch/_state/`) の書式・運用 |
| [powershell-conventions.md](powershell-conventions.md) | PowerShell 文字列置換の規則 |
| [license-policy.md](license-policy.md) | 外部ライブラリのライセンス方針 |

---

## `lake build` 成功時の自動生成物

`lake build` が成功すると `.github/skills/lean-build/scripts/build.ps1` が以下を自動実行する。

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
| `lean-sorry-investigator` | 1 件の sorry / 候補定理を反例→骨格→補題探索→タクティク試行で A→Z 調査 | 単一 sorry の triage、複数 sorry の並列 fan-out |
| `lean-simp-stabilizer` | 1 行の `simp` を `simp only [...]` に安定化 | コミット前の bare simp 解消 |
| `lean-session-restorer` | 前回記録との差分計算 + 着手推奨（内部で build-doctor + sorry-investigator を委任） | セッション再開・`/compact` 後の復元 |

---

## スキル一覧

| スキル | 概要 | 発動条件 |
|---|---|---|
| `lean-build` | `lake build` 起動と診断 JSONL の参照リファレンス | ビルドコマンド・JSONL レイアウト確認 |
| `lean-counterexample` | 反例テストケースカタログと GameConfig tier 指針 | 反例検証ロジックの参照 |
| `lean-diagnostics` | 診断 JSONL の解析と error pattern → 修正クラスのルーティング | エラー分類ロジックの参照 |
| `lean-mathlib-search` | Mathlib/Batteries 補題検索のクエリパターンとカタログ | 補題探索クエリ参照 |
| `lean-proof-planning` | 着手前チェックリスト・偽定理回避 | 証明戦略決定時 |
| `lean-proof-progress` | 長期 sorry 進捗・撤退判断基準 | 進捗トラッキング・pivot 判断 |
| `lean-repl` | REPL JSONL 起動と結果スキーマ | REPL 利用時 |
| `lean-run` | `lake exe` 実行（手動のみ） | 実行可能ターゲット起動時 |
| `lean-setup` | elan/lake/lean PATH 解決（手動のみ） | toolchain トラブルシュート時 |
| `lean-simp-guide` | simp 系比較とバルク安定化パイプライン | simp 系判断・10 行超のバルク変換 |
| `lean-tactic-select` | ゴール形状 → タクティク優先マップ | タクティク選択時 |
| `session-efficiency` | セッション効率分析・改善提案 | **手動実行のみ** |

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
