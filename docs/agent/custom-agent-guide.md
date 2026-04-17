# カスタムエージェント ベストプラクティスガイド

エージェントがカスタムエージェント（`.agent.md`）を新規作成・改善する際に参照するリファレンス。
簡潔さと正確さを優先し、エージェントのコンテキスト消費を最小化する構成とする。

---

## 0. 情報の鮮度と最新情報について

このドキュメントは 2026-04-14 時点の VS Code カスタムエージェント仕様を基に作成されている。
カスタムエージェントの仕様はまだ発展途上であり、将来的に変更される可能性がある。
最新の仕様やベストプラクティスについては以下の公式リソースを参照することを推奨する:

- [Custom agents in VS Code](https://code.visualstudio.com/docs/copilot/customization/custom-agents) — 公式ドキュメント
- [Agent Skills](https://code.visualstudio.com/docs/copilot/customization/agent-skills) — スキルとの使い分け
- [Prompt Files](https://code.visualstudio.com/docs/copilot/customization/prompt-files) — プロンプトファイルとの使い分け

---

## 1. カスタムエージェントとは

カスタムエージェントは **`.agent.md` ファイル** で定義される、AI に特定のペルソナ・ツール制約・指示を付与する仕組みである。
エージェント切り替え時に、指定されたツール・指示が自動適用される。

### スキル・プロンプトファイルとの使い分け

| カスタマイズ手法 | 用途 | ツール制約 | ハンドオフ |
|---|---|---|---|
| **カスタムエージェント** (`.agent.md`) | 特定ロール（レビュー・計画等）のペルソナ | ✅ 制御可能 | ✅ 対応 |
| **プロンプトファイル** (`.prompt.md`) | 単発タスクの再利用可能な指示 | ✅ 制御可能 | ❌ |
| **スキル** (`SKILL.md`) | ポータブルな専門知識 + スクリプト | ❌ | ❌ |

**判断基準**:
- ツール制約やモデル指定が必要 → カスタムエージェント
- 繰り返し使いたい指示がありツール制約不要 → プロンプトファイル
- スクリプト・リソース付きの再利用可能な専門知識 → スキル

---

## 2. ファイル配置

| スコープ | パス | 用途 |
|---|---|---|
| ワークスペース | `.github/agents/` | チーム共有（本プロジェクト採用） |
| ワークスペース（Claude 形式） | `.claude/agents/` | Claude Code 互換 |
| ユーザープロファイル | `~/.copilot/agents/` | 全ワークスペース共通 |
| 組織レベル | GitHub 組織設定 | 組織全体で共有 |

> `.github/agents/` 内の `.md` ファイルはすべてカスタムエージェントとして認識される。

---

## 3. ファイル構造

カスタムエージェントファイルは **YAML フロントマター（任意）+ Markdown 本文** で構成される。

### 3.1 フロントマター（YAML）

```yaml
---
description: エージェントの説明。チャット入力欄にプレースホルダーとして表示される
name: エージェント名（省略時はファイル名）
argument-hint: ユーザーへの入力ヒント
tools: ['search', 'read', 'execute']
agents: ['*']
model: Claude Sonnet 4 (copilot)
user-invocable: true
disable-model-invocation: false
handoffs:
  - label: 実装を開始
    agent: implementation
    prompt: 上記の計画に従って実装してください。
    send: false
    model: GPT-5 (copilot)
hooks:
  postResponse:
    - command: echo "done"
---
```

### 3.2 フロントマターフィールド一覧

| フィールド | 型 | 必須 | 説明 |
|---|---|---|---|
| `description` | string | 推奨 | エージェントの機能説明。チャット入力欄にプレースホルダーとして表示 |
| `name` | string | No | 表示名。省略時はファイル名 |
| `argument-hint` | string | No | ユーザーへの入力ヒント |
| `tools` | string[] | No | 使用可能なツール/ツールセットの一覧。MCP サーバーは `<server>/*` 形式 |
| `agents` | string[] | No | サブエージェントとして使用可能なエージェント名の一覧。`*` で全許可、`[]` で禁止 |
| `model` | string \| string[] | No | 使用する AI モデル。配列指定時は優先順に試行 |
| `user-invocable` | bool | No | エージェントドロップダウンに表示するか（デフォルト: `true`） |
| `disable-model-invocation` | bool | No | 他エージェントからサブエージェントとして呼び出されることを禁止（デフォルト: `false`） |
| `target` | string | No | ターゲット環境（`vscode` または `github-copilot`） |
| `handoffs` | object[] | No | ハンドオフ定義（後述） |
| `hooks` | object | No | エージェントスコープのフック定義（Preview。`chat.useCustomAgentHooks` 有効化が必要） |

### 3.3 Markdown 本文

フロントマターの後に Markdown で指示を記述する。
エージェント選択時に、この内容がユーザープロンプトの前に付加される。

- 他ファイルの参照: Markdown リンク（`[参照](path/to/file.md)`）
- ツールの参照: `#tool:<tool-name>` 構文（例: `#tool:web/fetch`）

---

## 4. ハンドオフ

ハンドオフは、エージェント間のシーケンシャルなワークフローを構築する機能である。
チャット応答完了後にハンドオフボタンが表示され、次のエージェントに遷移できる。

### ユースケース例

| フロー | 説明 |
|---|---|
| 計画 → 実装 | 計画エージェントで分析後、実装エージェントに引き継ぐ |
| 実装 → レビュー | 実装完了後、コードレビューエージェントに渡す |
| テスト作成 → テスト通過 | 失敗テストを書いてレビュー後、実装エージェントでパスさせる |

### ハンドオフフィールド

| フィールド | 型 | 説明 |
|---|---|---|
| `label` | string | ボタンの表示テキスト |
| `agent` | string | 遷移先エージェント名 |
| `prompt` | string | 遷移先に送るプロンプト |
| `send` | bool | `true` でプロンプト自動送信（デフォルト: `false`） |
| `model` | string | 遷移先で使用するモデル（任意） |

---

## 5. ベストプラクティス

### 5.1 最小権限の原則

エージェントのツール一覧は **タスクに必要な最小限** に絞る。

```yaml
# ✅ 良い: 計画エージェントは読み取り専用
tools: ['search', 'read', 'web']

# ❌ 悪い: 計画エージェントに編集権限を与える
tools: ['*']
```

| エージェント種別 | 推奨ツール |
|---|---|
| 計画・分析 | `search`, `read`, `web` |
| コードレビュー | `search`, `read`, `web`, `execute` |
| 実装 | `search`, `read`, `execute`, `edit` |
| デバッグ | すべて（必要に応じて） |

### 5.2 description を丁寧に書く

`description` はエージェント選択時のヒントとして表示される。
また、サブエージェントとして呼び出される際の判断材料になる。

```yaml
# ✅ 良い: 目的とトリガー条件が明確
description: >
  Lean 4 の sorry ゴールを分析し、候補タクティクを REPL で実際に試行して
  最良結果を返す自動アドバイザー。Use when: stuck on sorry, what tactic to use,
  goal advisor, tactic suggestion.

# ❌ 悪い: 曖昧
description: 証明を手伝う。
```

### 5.3 指示は具体的に・簡潔に

本文の指示はエージェントが **知らなければ間違える情報** に絞る。
汎用的な AI 知識の重複は不要。

| 書くべき | 書くべきでない |
|---|---|
| プロジェクト固有の制約・規約 | プログラミング言語の基本文法 |
| ツールの呼び出し手順（プロジェクト固有部分） | ツールの一般的な使い方 |
| 出力フォーマットの指定 | 「エラーを適切に処理せよ」等の一般論 |
| 落とし穴（Gotchas） | 自明な注意事項 |

### 5.4 サブエージェントの設計

サブエージェント専用のエージェントは `user-invocable: false` を設定し、ドロップダウンから非表示にする。

```yaml
---
description: 内部用の検証エージェント
user-invocable: false
tools: ['read', 'execute']
---
```

逆に、サブエージェントとして呼び出されたくないエージェントには `disable-model-invocation: true` を設定する。

### 5.5 モデル指定の活用

タスクに応じて最適なモデルを指定する。フォールバック用に配列で複数モデルを列挙できる。

```yaml
# 単一指定
model: Claude Sonnet 4 (copilot)

# フォールバック付き
model:
  - Claude Sonnet 4 (copilot)
  - GPT-5 (copilot)
```

### 5.6 ハンドオフでワークフローを構築する

複数ステップの作業は、各ステップを独立したエージェントとして設計し、ハンドオフで接続する。
各ステップの間でユーザーがレビュー・承認できるようにする。

```yaml
# planning.agent.md
---
description: 実装計画を生成する
tools: ['search', 'read', 'web']
handoffs:
  - label: 実装を開始
    agent: implementation
    prompt: 上記の計画に従って実装してください。
    send: false
---
```

- `send: false`（デフォルト）: ユーザーが確認してから送信
- `send: true`: 自動で次のエージェントに送信（注意して使用）

---

## 6. 本プロジェクトでの設計パターン

### 6.1 ファイル配置

本プロジェクトでは `.github/agents/` にカスタムエージェントを配置する。

```
.github/agents/
├── lean-error-fixer.agent.md
├── lean-goal-advisor.agent.md
├── lean-lemma-finder.agent.md
├── lean-proof-skeleton.agent.md
├── lean-session-restorer.agent.md
├── lean-simp-stabilizer.agent.md
├── lean-sorry-snapshot.agent.md
└── lean-theorem-checker.agent.md
```

### 6.2 命名規則

- ファイル名: `<domain>-<role>.agent.md`（ケバブケース）
- 例: `lean-goal-advisor.agent.md`, `lean-sorry-snapshot.agent.md`

### 6.3 共通パターン

本プロジェクトのカスタムエージェントは以下の構造に従う:

```yaml
---
description: >
  <機能の簡潔な説明>。
  Use when: <トリガーキーワードをカンマ区切りで列挙>。
tools: [execute, read, search]
argument-hint: "<ユーザーへの入力ヒント>"
---
```

- **`tools`**: 読み取り専用操作のエージェントには `[read, search]`、REPL 実行が必要なら `[execute, read, search]`
- **`argument-hint`**: ユーザーが何を渡すべきかを明示
- **制約セクション**: プロダクションコードの変更禁止等を明記
- **手順セクション**: ステップバイステップで具体的な操作手順を記述

---

## 7. セキュリティ考慮事項

- ツール一覧は最小権限にする（セクション 5.1 参照）
- セキュリティ重視のワークフローには読み取り専用ツールのみのエージェントを使う
- リポジトリで共有する `.agent.md` のツール一覧と指示を必ずレビューする
- ハンドオフの `send: true` は慎重に使用する（ユーザー確認をスキップするため）

---

## 8. トラブルシューティング

### エージェントが表示されない

1. ファイルが `.github/agents/` に配置されているか確認
2. 拡張子が `.agent.md`（または `.github/agents/` 内の `.md`）であることを確認
3. YAML フロントマターの構文エラーがないか確認
4. Chat Customizations エディタ（`Chat: Open Chat Customizations`）の diagnostics ビューで確認

### サブエージェントとして呼び出されない

1. 呼び出し元の `agents` フィールドに対象エージェント名が含まれているか確認
2. 対象エージェントに `disable-model-invocation: true` が設定されていないか確認
3. 呼び出し元の `tools` に `agent` ツールが含まれているか確認

### ツールが使えない

- 指定したツールが環境で利用可能か確認（利用不可のツールは無視される）
- プロンプトファイルの `tools` がエージェントの `tools` より優先される点に注意

---

## 9. 関連リソース

- [Custom agents in VS Code](https://code.visualstudio.com/docs/copilot/customization/custom-agents) — 公式ドキュメント
- [Agent Skills](https://code.visualstudio.com/docs/copilot/customization/agent-skills) — スキル仕様
- [Prompt Files](https://code.visualstudio.com/docs/copilot/customization/prompt-files) — プロンプトファイル仕様
- [Agent Tools](https://code.visualstudio.com/docs/copilot/agents/agent-tools) — ツール一覧
- [Planning with agents](https://code.visualstudio.com/docs/copilot/agents/planning) — 計画エージェント
