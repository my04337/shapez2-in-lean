# エージェント運用プレイブック（詳細版）

`AGENTS.md` には頻出・必須ルールのみを置き、ここには参照頻度が低い詳細ルールを集約する。

## 目的

- 指示の肥大化を防ぎ、日常作業のトークン消費を抑える
- 例外運用・閾値付きルールを一箇所にまとめる
- ルールの更新履歴を追いやすくする

## 検索戦略（詳細）

### 加工操作タスクの探索プロトコル

1. まず `S2IL/_agent/route-map.json` の `routes.{operation}.entry` を読む
2. entry の公開 API シグネチャ（先頭約 50 行）を確認
3. 必要時のみ `chain` を辿る（lazy exploration）
4. Kernel 層には `chain` か `kernel_deps` 経由で到達する（直接 grep しない）
5. タスク種別が明確なら `S2IL/_agent/query-playbook.json` のレシピを使う

### symbol-map 優先

- シンボル名が分かる場合、最初に `S2IL/_agent/symbol-map.jsonl` を検索する
- symbol-map は `build.ps1` / `build.sh` によるビルド成功時に自動再生成される（`update-symbol-map.ps1` / `update-symbol-map.sh`）
- 行番号が必要な場合のみ追加検索する
- symbol-map にないシンボルは「存在しない」と見なしてよい

### Explore 委譲の閾値

- 3000 行超ファイルで、同一ファイルに対する探索が 3 回以上続き、目的情報が未取得なら Explore に委譲
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

VS Code task や `lake build` 単体実行では `symbol-map.jsonl` が自動更新されない。
コミット直前に以下を必ず確認する:

1. **symbol-map 更新**: 新規 `theorem` / `lemma` を追加した場合は明示的に実行
   ```powershell
   .github/skills/lean-build/scripts/update-symbol-map.ps1
   ```
2. **sorry-goals 更新**: sorry が増減した場合
   ```powershell
   .github/skills/lean-build/scripts/update-sorry-goals.ps1
   ```
3. **`git status` で未追跡を確認**: `S2IL/_agent/symbol-map.jsonl` / `sorry-goals.md` の差分が想定通りか確認

### 推奨: スキル経由のビルド

上記ルーティンが組み込まれているため、手動フォローを省略したい場合は
[`.github/skills/lean-build/scripts/build.ps1`](../../.github/skills/lean-build/scripts/build.ps1) を直接使う。
成功時に `update-symbol-map.ps1` が自動実行される。

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
