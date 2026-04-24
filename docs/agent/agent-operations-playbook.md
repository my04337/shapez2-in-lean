# エージェント運用プレイブック（詳細版）

`AGENTS.md` には頻出・必須ルールのみを置き、ここには参照頻度が低い詳細ルールを集約する。

## 目的

- 指示の肥大化を防ぎ、日常作業のトークン消費を抑える
- 例外運用・閾値付きルールを一箇所にまとめる
- ルールの更新履歴を追いやすくする

## 検索戦略（詳細）

### 加工操作タスクの探索プロトコル

1. まず対応する facade（`S2IL/<Namespace>.lean`、例: `S2IL/Operations.lean`）の冒頭目次コメントを読む
2. facade で宣言されている公開 API シグネチャを確認
3. 具体的な実装が必要な場合は、facade が import している公開部品ファイル (`S2IL/<Namespace>/<Component>.lean`) を辿る
4. `Internal/` は facade / 同 namespace からのみ参照可能。外部からは触らない
5. それでも見つからなければ `grep_search` で対象 namespace に限定して検索

### シンボル検索

- `grep_search` でシンボル名を検索（対象は `S2IL/**/*.lean`、`_archive/` は除外）
- facade から import 経路で見つけるほうが早ければそちらを優先

Phase A (2026-04-24) で `symbol-map` / `sig-digest` / `route-map` / `query-playbook` / `dep-graph-baseline` は廃止された。
エージェントは facade 目次をインデックス代替として使う。

### Explore 委譲の閾値

- 長大ファイルで、同一ファイルに対する探索が 3 回以上続き、目的情報が未取得なら Explore に委譲
- 複数シンボル（3 件以上）の位置特定は、ファイルサイズに関わらず Explore 推奨
- 同一ファイルへの `grep_search` は原則 2 回まで

## セッションメモリ運用（詳細）

- 多段作業（Wave / 証明チェーン）では、初期ツール呼び出し 3 回以内に `/memories/session/` を作成
- 1 セッションあたり原則 2 ファイル以内
- 長大ドキュメント（5000 tokens 超）を扱う場合は、先に要約メモを作り、全文再読を避ける

詳細テンプレート: `docs/agent/session-memory-guide.md`

## タスク管理と進捗報告

### 進捗報告

- 長文コンテキストの常時同梱を禁止
- 収集系ツールを目的単位でバッチ化
- 中間報告は「現在地 + 次アクション」の短文に限定

## 証明作業の撤退閾値

- 同一 sorry に 8 アプローチ以上失敗したら撤退判断
- 同一ゴール形状が戦略変更後に 2 回再出現したら撤退検討

## ビルド後チェックリスト

### `lake build` 直接実行時の必須フォロー

VS Code task や `lake build` 単体実行では `sorry-goals.md` が自動更新されない。
コミット直前に以下を必ず確認する:

1. **sorry-goals 更新**: sorry が増減した場合
   ```powershell
   .github/skills/lean-build/scripts/update-sorry-goals.ps1
   ```
2. **`git status` で未追跡を確認**: `S2IL/_agent/sorry-goals.md` の差分が想定通りか確認

### 推奨: スキル経由のビルド

上記ルーティンが組み込まれているため、手動フォローを省略したい場合は
[`.github/skills/lean-build/scripts/build.ps1`](../../.github/skills/lean-build/scripts/build.ps1) を直接使う。
成功時に `update-sorry-goals.ps1` が自動実行される。

## ファイル編集ツール方針（詳細）

### Lean

- 変更後は必ず差分確認

### 置換失敗時

`replace_string_in_file` が失敗しても未変更とは限らない。`grep_search` または `read_file` で現状確認してから再試行する。

## シェル運用（補足）

- PowerShell の文字列置換は常に `-creplace`
- `.github/skills/` スクリプトはシェル前置なしで直接実行
- 非同期ビルド監視で `get_terminal_output` を連打しない

詳細: `docs/agent/powershell-conventions.md`
