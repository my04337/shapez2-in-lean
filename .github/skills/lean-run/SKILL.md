---
name: lean-run
description: 'Run Lean 4 executable via lake exe and verify output. Use when: run lean executable, execute lean program, lake exe, verify output, check program result.'
metadata:
  argument-hint: 'Pass executable name (or omit for default)'
disable-model-invocation: true
---

# Lean Run スキル

> ⚠️ **このスキルは `lake exe <target>` 専用**。  
> `Scratch/` ファイルを直接実行したい場合は **`lake env lean --run Scratch/MyFile.lean`** を使うこと（`--run` はファイル名より前）。  
> 本スキルを `Scratch/` 実行に使っても動作しない。

`lean-build` → `lake exe` の順にビルド＋実行し、出力を検証する。
証明作業や lint チェックが目的なら **lean-build** で十分。本スキルは `Main.lean` の出力確認用。

## スクリプト

```powershell
.github/skills/lean-run/scripts/run.ps1          # Windows
.github/skills/lean-run/scripts/run.sh            # macOS / Linux
```

| オプション | デフォルト | 説明 |
|---|---|---|
| `-Target <name>` / `--target <name>` | `s2il` | 実行ターゲット名 |
| `-Expected <string>` / `--expected <string>` | — | 期待する出力文字列（検証用） |

## 出力仕様

**stdout** にビルド診断サマリー + 実行結果サマリーを出力する。

```
=== BUILD DIAGNOSTICS ===
...（lean-build と同形式）
=== END DIAGNOSTICS ===

=== RUN RESULT ===
status: success|failure|skipped
exit_code: 0
target: s2il
log: .lake/run-log.txt
output_lines: 12
---
<実行出力 (先頭50行)>
=== END RUN ===
```

| フィールド | 内容 |
|---|---|
| `status: skipped` | ビルド失敗のため実行せずスキップ |
| `status: success` | 実行成功（exit 0） |
| `status: failure` | 実行失敗（非ゼロ終了） |
| `output_lines` | 総行数（50行超は先頭50行のみ表示） |
| `verification` | `-Expected` 指定時のみ: `pass` / `fail` |

実行ログ全体は `.lake/run-log.txt` に保存される。

## バックグラウンド実行時のポーリング指針

`lake env lean --run` を `isBackground=true` で起動した場合、進捗を確認する手段がないため
ポーリングが必要になる。以下の指針に従い、**コンテキスト消費を最小化**すること。

### 実行時間の目安

| 対象 | 推定実行時間 | 初回ポーリング | 以降の間隔 | 打ち切り上限 |
|---|---|---|---|---|
| 1L-4L 全数テスト（~200万件） | 2-5 分 | 120 秒後 | 120 秒 | 5 回 |
| 5L+ ランダムサンプリング（~2万件） | 1-3 分 | 60 秒後 | 60 秒 | 5 回 |
| 単体テスト・小規模 #eval | 10-30 秒 | 30 秒後 | 30 秒 | 3 回 |
| ビルド (`lake build`) | 30-180 秒 | 60 秒後 | 60 秒 | 5 回 |

### ポーリング時の注意

- `get_terminal_output` の出力は毎回数千トークンになりうる。**上限回数を超えたらタイムアウトとして扱い、ユーザーに報告する**
- ポーリング間で他の作業（メモリ保存、ドキュメント整理等）を並行して行い、待機時間を有効活用する
- 出力が既に完了していた場合（exit code 表示済み）、追加ポーリングは不要
