# GitHub Copilot Hooks リファレンス

エージェントセッションのライフサイクルイベントでカスタムシェルコマンドを実行する仕組み。
Skills が「知識・手順の注入」なら、Hooks は「確定的なコード実行による自動化」。

> **ステータス**: Preview（2026-03-25 時点）。仕様は今後変更される可能性あり。

---

## 0. Skills との違い

| 観点 | Skills | Hooks |
|---|---|---|
| 提供するもの | 知識・手順・リファレンス | シェルコマンドの自動実行 |
| 発動タイミング | エージェントが判断 | ライフサイクルイベントで確定的に発火 |
| 制御の性質 | ソフト（指示に従うかはモデル依存） | ハード（exitコード・JSONで強制） |
| 適した用途 | 複雑な判断・知識参照 | フォーマッタ実行・セキュリティポリシー・監査ログ |

---

## 1. 配置場所

| スコープ | パス | 備考 |
|---|---|---|
| ワークスペース | `.github/hooks/*.json` | 本プロジェクト推奨 |
| ワークスペース (Claude互換) | `.claude/settings.json` | VS Code が読み込み可能 |
| ユーザー | `~/.copilot/hooks/` or `~/.claude/settings.json` | 全プロジェクト共通 |
| カスタムエージェント | `.agent.md` の frontmatter `hooks` フィールド | エージェント限定 |

ワークスペース hooks がユーザー hooks より優先される。

---

## 2. ライフサイクルイベント

### VS Code (ローカルエージェント)

| イベント | 発火タイミング | 主な用途 |
|---|---|---|
| `SessionStart` | セッション開始 | 環境初期化・コンテキスト注入 |
| `UserPromptSubmit` | ユーザーがプロンプト送信 | 監査・入力検証 |
| `PreToolUse` | ツール実行前 | 危険操作ブロック・承認制御・入力変更 |
| `PostToolUse` | ツール実行後 | フォーマッタ・リンター・ログ |
| `PreCompact` | コンテキスト圧縮前 | 重要情報の退避 |
| `SubagentStart` | サブエージェント生成時 | コンテキスト注入 |
| `SubagentStop` | サブエージェント完了時 | 結果検証・続行制御 |
| `Stop` | セッション終了 | レポート生成・続行強制 |

### GitHub Coding Agent (クラウド)

| イベント | 発火タイミング |
|---|---|
| `sessionStart` | セッション開始 |
| `sessionEnd` | セッション終了 |
| `userPromptSubmitted` | プロンプト送信時 |
| `preToolUse` | ツール実行前 |
| `postToolUse` | ツール実行後 |
| `agentStop` | メインエージェント完了時 |
| `subagentStop` | サブエージェント完了時 |
| `errorOccurred` | エラー発生時 |

---

## 3. 設定フォーマット

### VS Code 形式

```json
{
  "hooks": {
    "PostToolUse": [
      {
        "type": "command",
        "command": "./scripts/post-edit.sh",
        "windows": "powershell -File scripts\\post-edit.ps1",
        "timeout": 30
      }
    ]
  }
}
```

| プロパティ | 必須 | 説明 |
|---|---|---|
| `type` | ○ | `"command"` 固定 |
| `command` | ○ | 実行コマンド（クロスプラットフォーム既定） |
| `windows` | - | Windows 固有コマンド |
| `linux` | - | Linux 固有コマンド |
| `osx` | - | macOS 固有コマンド |
| `cwd` | - | 作業ディレクトリ（リポジトリルート相対） |
| `env` | - | 追加環境変数 |
| `timeout` | - | タイムアウト秒数（既定: 30） |

### GitHub Coding Agent 形式

```json
{
  "version": 1,
  "hooks": {
    "postToolUse": [
      {
        "type": "command",
        "bash": "./scripts/post-edit.sh",
        "powershell": "./scripts/post-edit.ps1",
        "timeoutSec": 30
      }
    ]
  }
}
```

**VS Code との差異**: `version: 1` 必須、イベント名 camelCase、コマンドキーは `bash`/`powershell`、タイムアウトは `timeoutSec`。

### エージェントスコープ Hooks (.agent.md)

```markdown
---
name: "My Agent"
hooks:
  PostToolUse:
    - type: command
      command: "./scripts/check.sh"
---
```

`chat.useCustomAgentHooks: true` の設定が必要。

---

## 4. 入出力

### 入力 (stdin JSON)

全イベント共通:
```json
{
  "timestamp": "2026-02-09T10:30:00.000Z",
  "cwd": "/path/to/workspace",
  "sessionId": "session-id",
  "hookEventName": "PreToolUse",
  "transcript_path": "/path/to/transcript.json"
}
```

追加フィールド（イベント別）:

| イベント | 追加フィールド |
|---|---|
| `PreToolUse` | `tool_name`, `tool_input`, `tool_use_id` |
| `PostToolUse` | `tool_name`, `tool_input`, `tool_use_id`, `tool_response` |
| `UserPromptSubmit` | `prompt` |
| `SessionStart` | `source` |
| `Stop` | `stop_hook_active` (無限ループ防止用) |
| `SubagentStart` | `agent_id`, `agent_type` |
| `SubagentStop` | `agent_id`, `agent_type`, `stop_hook_active` |
| `PreCompact` | `trigger` |

### 出力 (stdout JSON)

共通:
```json
{
  "continue": true,
  "stopReason": "理由（continue=false 時）",
  "systemMessage": "ユーザーへの警告メッセージ"
}
```

`PreToolUse` 固有 — ツール実行の制御:
```json
{
  "hookSpecificOutput": {
    "hookEventName": "PreToolUse",
    "permissionDecision": "allow|deny|ask",
    "permissionDecisionReason": "理由",
    "updatedInput": {},
    "additionalContext": "モデルへの追加コンテキスト"
  }
}
```

`PostToolUse` 固有 — フォローアップ制御:
```json
{
  "hookSpecificOutput": {
    "hookEventName": "PostToolUse",
    "additionalContext": "追加コンテキスト"
  }
}
```

`Stop` / `SubagentStop` 固有 — 続行強制:
```json
{
  "hookSpecificOutput": {
    "hookEventName": "Stop",
    "decision": "block",
    "reason": "テスト完了前に終了しないでください"
  }
}
```

### 終了コード

| コード | 意味 |
|---|---|
| 0 | 成功（stdout を JSON パース） |
| 2 | ブロッキングエラー（処理停止、stderr をモデルに表示） |
| その他 | 非ブロッキング警告（警告表示、処理続行） |

---

## 5. UI からの設定

- チャット入力で `/hooks` と入力
- コマンドパレット → `Chat: Configure Hooks`
- チャットビューの設定アイコン → Hooks
- `/create-hook` で AI にフック生成を依頼可能

---

## 6. セキュリティ上の注意

- フックは VS Code と同じ権限でシェルコマンドを実行する
- 信頼できないソースのフックスクリプトは必ずレビューする
- stdin 入力は必ず検証・サニタイズする（インジェクション対策）
- シークレットをハードコードしない
- `chat.tools.edits.autoApprove` でフックスクリプト自体の自動編集を禁止推奨

---

## 7. トラブルシューティング

| 問題 | 対処 |
|---|---|
| フック未実行 | `.github/hooks/` に `.json` 拡張子で配置されているか確認。`type: "command"` があるか確認 |
| 権限エラー | `chmod +x script.sh`（Unix）。shebang `#!/bin/bash` があるか確認 |
| PowerShell 実行ポリシーエラー | `windows` フィールドに `pwsh -ExecutionPolicy Bypass -NoProfile -File <script>` 形式で指定する |
| タイムアウト | `timeout` 値を増やす。既定 30 秒 |
| JSON パースエラー | stdout が有効な JSON か確認。`jq -c` や `ConvertTo-Json -Compress` で検証 |
| ログ確認 | Output パネル → "GitHub Copilot Chat Hooks" チャンネル |
| 診断確認 | View Logs → "Load Hooks" で読み込み状況確認 |

---

## 8. VS Code 固有の制限と対処法

### PostToolUse はすべてのツールで発火する

**制限**: VS Code は hooks の `matcher` フィールドを解析するが適用しない。
`PostToolUse` はツール名に関わらず、`read_file`・`semantic_search` 等を含む
すべてのツール呼び出しで発火する（2026-03-25 時点）。

> *「Currently, VS Code ignores matcher values, so hooks run on all tool invocations regardless of the matcher.」― VS Code 公式ドキュメント*

**対処法**: スクリプト内で早期終了する最速パスを実装する。
JSON パース（`ConvertFrom-Json`）は重いため、パース前に文字列レベルで判定する:

```powershell
# JSON パース前に正規表現で早期終了（高速）
if ($rawInput -notmatch '"tool_name"\s*:\s*"(replace_string_in_file|...)"') {
    '{}'; exit 0
}
# .lean ファイルへの言及がない場合も即座に終了
if ($rawInput -notmatch '\.lean') {
    '{}'; exit 0
}
# ここまで来たら JSON パース（低頻度なのでコスト許容）
$inputJson = $rawInput | ConvertFrom-Json
```

### Windows の PowerShell 起動オーバーヘッド

`PostToolUse` がすべてのツールで発火するため、Windows ではプロセス起動コストが累積する。
`-NoProfile` フラグでプロファイルロードをスキップし、起動時間を短縮する:

```json
"windows": "pwsh -ExecutionPolicy Bypass -NoProfile -File .github/hooks/scripts/script.ps1"
```

`-NoProfile` なし: ~400-500ms / 呼び出し → `-NoProfile` あり: ~150-250ms / 呼び出し

### VS Code と Claude Code のツール名の違い

Claude Code 向けの hooks を VS Code に移植する場合、ツール名が異なる:

| Claude Code | VS Code |
|---|---|
| `Write` | `create_file` |
| `Edit` | `replace_string_in_file` |
| `MultiEdit` | `multi_replace_string_in_file` |
| `Read` | `read_file` |

---

## 参考リンク

- [VS Code Hooks ドキュメント](https://code.visualstudio.com/docs/copilot/customization/hooks)
- [GitHub フックについて](https://docs.github.com/ja/copilot/concepts/agents/coding-agent/about-hooks)
- [GitHub フックの使用](https://docs.github.com/ja/copilot/how-tos/use-copilot-agents/coding-agent/use-hooks)
- [フックの構成リファレンス](https://docs.github.com/ja/copilot/reference/hooks-configuration)
