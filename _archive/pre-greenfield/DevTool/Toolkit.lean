-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import DevTool.Toolkit.DepGraph
import DevTool.Toolkit.SymbolMap
import DevTool.Toolkit.ProofStats

/-!
# S2IL Toolkit (s2il-toolkit)

S2IL 環境にアクセスする開発ツール群。
S2IL のビルドが正常に完了している（sorry 警告は許容）前提で使用する。

## 使用方法

```
lake exe s2il-toolkit <subcommand> [OPTIONS]
```

### サブコマンド

| サブコマンド | 説明 |
|---|---|
| `depgraph` | 依存グラフを Mermaid/JSON で出力 |
| `symbol-map` | シンボル位置 DB を JSONL で出力 |
| `proof-stats` | モジュール別の証明統計を出力 |
-/

open Lean

unsafe def main (args : List String) : IO Unit := do
    match args with
    | "depgraph" :: rest => do
        let env ← DevTool.Toolkit.Common.loadEnv
        DevTool.Toolkit.DepGraph.run env rest
    | "symbol-map" :: rest => do
        let env ← DevTool.Toolkit.Common.loadEnv
        DevTool.Toolkit.SymbolMap.run env rest
    | "proof-stats" :: rest => do
        let env ← DevTool.Toolkit.Common.loadEnv
        DevTool.Toolkit.ProofStats.run env rest
    | [] | ["--help"] | ["-h"] => do
        IO.println "Usage: lake exe s2il-toolkit <subcommand> [OPTIONS]"
        IO.println ""
        IO.println "サブコマンド:"
        IO.println "  depgraph      依存グラフを Mermaid/JSON で出力"
        IO.println "  symbol-map    シンボル位置 DB を JSONL で出力"
        IO.println "  proof-stats   モジュール別の証明統計を出力"
        IO.println ""
        IO.println "共通オプション:"
        IO.println "  --ns <prefix>     対象モジュールプレフィックス（デフォルト: S2IL）"
        IO.println "  --output <path>   出力ファイルパス（デフォルト: stdout）"
        IO.println "  --json            JSON 形式で出力"
        IO.println "  --help, -h        このヘルプを表示"
        IO.println ""
        IO.println "depgraph オプション:"
        IO.println "  --private         private 宣言を含める"
        IO.println "  --theorems-only   定理のみ表示"
        IO.println "  --root <name>     起点宣言を指定（部分グラフ）"
        IO.println "  --root-reverse    依存元を逆方向に辿る"
        IO.println "  --sorry-only      sorry 宣言のみ表示"
    | cmd :: _ => do
        IO.eprintln s!"不明なサブコマンド: {cmd}"
        IO.eprintln "lake exe s2il-toolkit --help でヘルプを表示"
        IO.Process.exit 1
