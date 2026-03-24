---
name: lean-diagnostics
description: 'Lean 4 ビルド・実行結果の診断メッセージを解析・トリアージする。Use when: analyze build errors, triage warnings, prioritize fixes, parse diagnostics, review build output, sorry detection.'
metadata:
  argument-hint: 'ビルド結果の診断とトリアージを行います'
---

# ビルド診断の解析とトリアージ

**lean-build** / **lean-run** スクリプトが出力する診断情報を解析し、
修正すべき問題を優先順位付けする。

## 診断出力の構造

### マーカー区切りサマリー (stdout)

ビルドスクリプトは以下の形式で構造化サマリーを標準出力に書き出す:

```
=== BUILD DIAGNOSTICS ===
total_errors: 2
total_warnings: 5
total_sorries: 1
build_status: failure
exit_code: 1

[error] S2IL/Shape/Color.lean:42:0: unknown identifier 'Foo'
[sorry] S2IL/Shape/Layer.lean:10:4: declaration uses 'sorry'
[warning] S2IL/Processing/Cutter.lean:88:0: unused variable 'x'
...
=== END DIAGNOSTICS ===
```

run スクリプトはビルド診断に加えて実行結果を出力する:

```
=== RUN RESULT ===
status: success
exit_code: 0
target: s2il
log: .lake/run-log.txt
output_lines: 12
=== END RUN ===
```

### 出力ファイル

| ファイル | 内容 |
|---|---|
| `.lake/build-log.txt` | `lake build` の全出力（stdout + stderr） |
| `.lake/build-diagnostics.jsonl` | 診断メッセージの JSONL（1行1JSON） |
| `.lake/run-log.txt` | `lake exe` の実行出力 |

### JSONL フォーマット

`.lake/build-diagnostics.jsonl` の各行は以下の形式:

```json
{"file":"S2IL/Shape/Color.lean","line":42,"col":0,"severity":"error","message":"unknown identifier 'Foo'"}
```

`severity` は `error`, `warning`, `info` のいずれか。
`sorry` は `warning` レベルだが、メッセージに `` declaration uses `sorry` `` を含む。

## トリアージ優先順位

診断メッセージは以下の優先順位で対応する:

| 優先度 | レベル | 対応方針 |
|---|---|---|
| 1 (最高) | **error** | ビルドを阻害する。必ず修正する |
| 2 | **sorry** | 未証明の定理。機能は動作するが証明が不完全 |
| 3 | **warning** | 未使用変数・非推奨 API 等。品質改善として対応 |
| 4 (最低) | **info** | 情報メッセージ。通常は対応不要 |

### sorry の検出方法

`sorry` は Lake の出力では `warning` として報告されるが、
メッセージ本文に `declaration uses 'sorry'` を含む。
スクリプトはこれを自動的に `[sorry]` カテゴリに分類する。

## 診断ファイルの参照方法

### JSONL を読み込む

エージェントは `read_file` で `.lake/build-diagnostics.jsonl` を読み込み、
JSON をパースして構造的に解析できる。

### 全ログからフィルタ

全ログから特定レベルの診断だけを抽出する例:

**PowerShell**:
```powershell
Select-String -Path .lake/build-log.txt -Pattern ':\s*error:'
Select-String -Path .lake/build-log.txt -Pattern "declaration uses 'sorry'"
```

**bash / zsh**:
```bash
grep ': error:' .lake/build-log.txt
grep "declaration uses 'sorry'" .lake/build-log.txt
```

## Lake の診断関連オプション

ビルドスクリプトに渡す前に Lake のオプションを理解しておくと便利:

| オプション | 説明 |
|---|---|
| `--no-ansi` | ANSI エスケープシーケンスを無効化（スクリプトでは既定で使用） |
| `--log-level=<LV>` | ログレベル: `trace`, `info`, `warning`, `error` |
| `--wfail` | 警告をエラーとして扱う（CI 向け） |
| `--fail-level=<LV>` | 指定レベル以上でビルド失敗扱い |

## 関連スキル

- **lean-build**: ビルドの実行
- **lean-run**: ビルド＋実行
- **lean-setup**: ツールチェインの PATH 解決
- **lean-proof-progress**: sorry の進捗管理と撤退判断
- **lean-depgraph**: sorry 間の依存関係の可視化

## sorry の依存関係分析

証明作業では sorry 間の依存関係が重要。以下の手順で分析する。

### sorry 依存グラフの取得

**lean-depgraph** を使って sorry を含む宣言の依存関係を可視化する:

```powershell
# sorry を含むノードが赤色で強調される
.github/skills/lean-depgraph/scripts/depgraph.ps1
```

### sorry の分類

| 分類 | 意味 | 対応方針 |
|---|---|---|
| **独立 sorry** | 他の sorry に依存しない | 即座に着手可能。優先候補 |
| **依存 sorry** | 他の sorry の結果を前提とする | 依存先を先に解決 |
| **被依存 sorry** | 多くの宣言がこの sorry に依存 | 解決のインパクトが大きい |

### sorry の型シグネチャ要約

sorry の対象（何を証明する必要があるか）を素早く把握するには:

```powershell
# Windows: sorry を含む宣言の一覧
Get-Content .lake/build-diagnostics.jsonl |
    ConvertFrom-Json |
    Where-Object { $_.isSorry -eq $true } |
    Select-Object file, line, message
```

```bash
# macOS / Linux
grep '"isSorry":true' .lake/build-diagnostics.jsonl | jq '{file, line, message}'
```

sorry の行番号から対象の `theorem` / `lemma` 宣言を特定し、
その型シグネチャ（ゴール）を確認する。
