---
name: lean-build
description: 'Lean 4 プロジェクトを lake build でビルドする。Use when: build lean project, compile lean code, lake build, check compilation errors, resolve build failures.'
metadata:
  argument-hint: 'Lean プロジェクトのビルドを実行します'
---

# Lean Build スキル

PATH 解決・ビルド・診断 JSONL 生成を 1 コマンドで実行する。

## スクリプト

```powershell
.github/skills/lean-build/scripts/build.ps1          # Windows
.github/skills/lean-build/scripts/build.sh            # macOS / Linux
```

| オプション | 説明 |
|---|---|
| `-Clean` / `--clean` | `lake clean` 後にビルド |
| `-Update` / `--update` | `lake update` 後にビルド |
| `-Target <name>` / `--target <name>` | 特定ターゲットのみビルド |

## 出力仕様

**stdout** にマーカー区切りサマリー、ファイルに詳細を出力する。

| 出力先 | 内容 |
|---|---|
| stdout | `=== BUILD DIAGNOSTICS ===` 〜 `=== END DIAGNOSTICS ===` |
| `.lake/build-log.txt` | `lake build` の全ログ |
| `.lake/build-diagnostics.jsonl` | 診断メッセージ（1行1JSON） |

### サマリーブロック

```
=== BUILD DIAGNOSTICS ===
status: success|failure
exit_code: 0
errors: 0    sorries: 3    warnings: 0    info: 12
log: .lake/build-log.txt
diagnostics: .lake/build-diagnostics.jsonl

[SORRY] S2IL/Behavior/Gravity.lean:5019:16: declaration uses `sorry`
=== END DIAGNOSTICS ===
```

### JSONL フィールド

```json
{"file":"S2IL/Behavior/Gravity.lean","line":5019,"col":16,"severity":"warning","message":"declaration uses `sorry`","isSorry":true}
```

| フィールド | 内容 |
|---|---|
| `file` | ソースファイルの相対パス |
| `line` / `col` | 行・列番号 |
| `severity` | `"error"` / `"warning"` / `"info"` |
| `message` | 診断メッセージ本文 |
| `isSorry` | `true` = sorry 由来の warning |

### パイプラインキャプチャ（PowerShell）

```powershell
$output = .github/skills/lean-build/scripts/build.ps1
$text   = $output -join "`n"                                  # 配列→文字列（$Matches を使うために必要）
if ($text -match 'status: (\w+)')  { $status  = $Matches[1] }
if ($text -match 'errors: (\d+)')  { $errors  = [int]$Matches[1] }
if ($text -match 'sorries: (\d+)') { $sorries = [int]$Matches[1] }
# $status  → "success" / "failure"
# $errors  → 0 ならビルド成功、>0 なら修正必要
# $sorries → 残り sorry 数（証明進捗の指標）
```

▶ 注意: サマリーは stdout のみ。`Write-Host` では取得できないため `$output = script` 形式で使う。
$status = ($output | Select-String "^status:").Line

$diags = Get-Content .lake/build-diagnostics.jsonl | ConvertFrom-Json
$diags | Where-Object { $_.severity -eq "error" }                          # エラー
$diags | Where-Object { $_.isSorry -eq $true }                             # sorry
$diags | Where-Object { $_.severity -eq "warning" -and !$_.isSorry }       # 非sorry warning
```

## 単一ファイルの高速チェック

```powershell
lake env lean S2IL/Behavior/Gravity.lean 2>&1 | Select-String "error|sorry"
```

| 状況 | 推奨方法 |
|---|---|
| 証明作業中の頻繁なチェック | `lake env lean <file>` |
| 全体の整合性確認 | ビルドスクリプト |
| CI / リリース前 | ビルドスクリプト + `--update` |

詳細な診断分析・トリアージは **lean-diagnostics** スキルを参照。
