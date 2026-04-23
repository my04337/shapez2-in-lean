# Scratch/ — 一時ファイル運用（簡約版）

## 用途

`Scratch/` は実験・検証専用ディレクトリ。

- `*.lean`: 断片検証、`#eval`、局所テスト
- `*.jsonl`: REPL バッチコマンド

## 役割分担

- `Scratch/`: エージェントが作成する一時ファイル
- `.repl/<session>/`: REPL インフラ専用（直接編集しない）

## 実行

```powershell
lake env lean Scratch/MyFile.lean
lake env lean --run Scratch/MyFile.lean
```

## JSONL 作成ルール

- JSONL は `run_in_terminal` + `Set-Content` で作成
- **並列実行時の衝突回避のため、毎回一意な名前を使う**
- 推奨形式: `Scratch/commands-<sessionId>-<topic>-<runId>.jsonl`
- `runId` は時刻ベース（例: `yyyyMMdd-HHmmss-fff`）を使う
- `sessionId` が不明な場合は `unknown` を使う（例: `Scratch/commands-unknown-goal-advisor-20260418-103015-123.jsonl`）
- 固定名（`Scratch/commands.jsonl` など）は禁止

## JSONL 蓄積管理

- **自セッションのファイル**（`Scratch/commands-<自sessionId>-*.jsonl`）は **証明・検証が完了したタイミングごとに** 不要なものを削除する
  - セッション終了時にも `Get-ChildItem Scratch\commands-<sessionId>-*.jsonl | Remove-Item` で一括削除
- **他セッションのファイルは削除しない**: 自分の sessionId を含まないファイルは別セッションが使用中の可能性があるため削除禁止
- Scratch/ 内の JSONL が 30 件を超えたら整理を検討する（**自セッション分のみ**を削除対象にする）
- 将来参照する可能性がない実験 JSONL は即座に削除して構わない

## 禁止

- トップレベルへの一時ファイル作成（`tmp_*.lean` など）
- `.repl/` への Lean/JSONL 作成

## 補足

- `Scratch/commands.jsonl` は編集前に必ず内容確認する
- 長い Unicode 含み検証は JSONL より `Scratch/*.lean` を優先する
