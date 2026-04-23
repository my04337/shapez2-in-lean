-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import DevTool.Diag.SorryList

/-!
# S2IL 診断ツール (s2il-diag)

S2IL ライブラリに依存しない開発診断ツール。
S2IL のビルドエラー時でも利用可能。

## 使用方法

```
lake exe s2il-diag <subcommand> [OPTIONS]
```

### サブコマンド

| サブコマンド | 説明 |
|---|---|
| `sorry-list` | `.lake/build-diagnostics.jsonl` から sorry 一覧を出力 |

### オプション

| フラグ | 対象 | 説明 |
|---|---|---|
| `--json` | sorry-list | JSONL 形式で出力（デフォルト: テーブル） |
-/

unsafe def main (args : List String) : IO Unit := do
    match args with
    | "sorry-list" :: rest => DevTool.Diag.SorryList.run rest
    | [] | ["--help"] | ["-h"] => do
        IO.println "Usage: lake exe s2il-diag <subcommand> [OPTIONS]"
        IO.println ""
        IO.println "サブコマンド:"
        IO.println "  sorry-list    sorry 一覧を出力（S2IL 非依存）"
        IO.println ""
        IO.println "オプション:"
        IO.println "  --json        JSONL 形式で出力"
        IO.println "  --help, -h    このヘルプを表示"
    | cmd :: _ => do
        IO.eprintln s!"不明なサブコマンド: {cmd}"
        IO.eprintln "lake exe s2il-diag --help でヘルプを表示"
        IO.Process.exit 1
