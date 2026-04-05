---
name: lean-run
description: 'Lean 4 プロジェクトの実行ファイルを lake exe で実行し、出力結果を検証する。Use when: run lean executable, execute lean program, lake exe, verify output, check program result.'
metadata:
  argument-hint: 'Lean プロジェクトを実行して結果を確認します'
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
