---
name: lean-run
description: 'Lean 4 プロジェクトの実行ファイルを lake exe で実行し、出力結果を検証する。Use when: run lean executable, execute lean program, lake exe, verify output, check program result.'
metadata:
  argument-hint: 'Lean プロジェクトを実行して結果を確認します'
---

# Lean プロジェクトの実行と検証

`lake exe` でビルド済み実行ファイルを起動し、出力を確認・検証する。

## 前提条件

- **lean-build** スキルでプロジェクトがビルド済みであること
- `lakefile.toml` に `[[lean_exe]]` が定義されていること

## 依存関係

```
lean-setup → lean-build → lean-run
```

スクリプトは内部で lean-build (→ lean-setup) を自動呼び出しするため、
通常は lean-run のスクリプトだけ実行すれば PATH 解決からビルド・実行まで一括で行われる。

## 手順

### 1. 実行スクリプトの実行

ビルド → 実行 → (任意) 出力検証をまとめて行う。
シェル名を前置せず、スクリプトを直接実行すること。

- **Windows**: `.github/skills/lean-run/scripts/run.ps1`
- **macOS / Linux**: `.github/skills/lean-run/scripts/run.sh`

オプション:

| オプション | デフォルト | 説明 |
|---|---|---|
| `-Target <name>` / `--target <name>` | `s2il` | 実行ターゲット名 |
| `-Expected <string>` / `--expected <string>` | *(なし)* | 期待する出力文字列 (指定時のみ検証) |

### 2. 実行ターゲットの確認

`lakefile.toml` の `[[lean_exe]]` セクション:

```toml
[[lean_exe]]
name = "s2il"
root = "Main"
```

### 3. 手動実行

```shell
lake exe s2il
```

`lake exe` は必要に応じて自動でビルドも行うため、単独での実行も可能。

## 構造化出力

スクリプトはビルド診断サマリーに加え、実行結果を以下の形式で出力する:

- **ビルド診断**: `=== BUILD DIAGNOSTICS ===` 〜 `=== END DIAGNOSTICS ===`
- **実行結果**: `=== RUN RESULT ===` 〜 `=== END RUN ===`
- **実行ログ**: `.lake/run-log.txt`

ビルド失敗時は実行がスキップされ、`status: skipped` が報告される。

診断の詳細な分析・トリアージは **lean-diagnostics** スキルを参照。

## トラブルシューティング

- 実行ファイルが見つからない → `lakefile.toml` の `[[lean_exe]]` 定義を確認
- 実行時エラー → `.lake/run-log.txt` で詳細を確認
- `lake` が見つからない → **lean-setup** スキルを参照
- ビルドエラー → サマリーの `[error]` 行を確認、**lean-build** スキルを参照
