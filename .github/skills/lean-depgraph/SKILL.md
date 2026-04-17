---
name: lean-depgraph
description: 'Generate Lean 4 proof dependency graph as Mermaid/JSON. Use when: visualize proof dependencies, analyze theorem relationships, generate dependency graph, mermaid diagram, proof structure, lemma dependencies.'
metadata:
  argument-hint: 'Omit to generate full project dependency graph'
disable-model-invocation: true
---

# 証明依存グラフスキル

`Environment` API でコンパイル済み環境から定理・定義間の依存を高精度に抽出し、Mermaid / JSON で出力する。

## スクリプト

```powershell
.github/skills/lean-depgraph/scripts/depgraph.ps1    # Windows
.github/skills/lean-depgraph/scripts/depgraph.sh      # macOS / Linux
```

| オプション | デフォルト | 説明 |
|---|---|---|
| `-Private` / `--private` | off | private 宣言を含める |
| `-Json` / `--json` | off | JSON 形式で出力（デフォルト: Mermaid） |
| `-Namespace <name>` / `--ns <name>` | `S2IL` | 対象モジュールプレフィックス |
| `-TheoremsOnly` / `--theorems-only` | off | 定理のみ表示 |
| `-Output <path>` / `--output <path>` | `.lake/depgraph.md` | 出力ファイルパス |
| `-Root <name>` / `--root <name>` | 全体 | 起点宣言を指定（部分グラフ） |
| `-RootReverse` / `--root-reverse` | off | `-Root` と併用。依存元を逆方向に辿る |
| `-SorryOnly` / `--sorry-only` | off | sorry 宣言のみ表示（sorry 間依存分析用） |

## サブエージェント向けレシピ

### sorry 依存スナップショット（lean-sorry-snapshot の Step 3）

```powershell
.github/skills/lean-depgraph/scripts/depgraph.ps1 -SorryOnly -Json
```

### 特定宣言の依存先追跡

```powershell
.github/skills/lean-depgraph/scripts/depgraph.ps1 -Root "S2IL.Foo.myThm" -Json
```

### 特定宣言の依存元追跡

```powershell
.github/skills/lean-depgraph/scripts/depgraph.ps1 -Root "S2IL.Foo.myDef" -RootReverse -Json
```

## 出力仕様

**stdout** にサマリーブロック、ファイルにグラフ本体を出力する。

```
=== DEPGRAPH RESULT ===
status: success|failed
exit_code: 0
output: .lake/depgraph.json
=== DEPGRAPH STATISTICS ===
  nodes: 42 (theorems: 15, other: 27)
  edges: 87
  sorry: 5 (independent: 2)
=== END STATISTICS ===
=== END DEPGRAPH ===
```

### JSON 形式

```json
{
  "nodes": [{"name": "Layer.rotateCW", "kind": "def", "module": "S2IL.Behavior.Rotate", "sorry": false, "private": false}],
  "edges": [{"from": "Layer.rotateCW_four", "to": "Layer.rotateCW"}]
}
```

### パイプラインキャプチャ（PowerShell）

```powershell
$output = .github/skills/lean-depgraph/scripts/depgraph.ps1 -SorryOnly -Json
$text   = $output -join "`n"                           # 配列→文字列（$Matches を使うために必要）
if ($text -match 'nodes: (\d+)')  { $nodes      = $Matches[1] }
if ($text -match 'sorry: (\d+)')  { $sorryCount = $Matches[1] }
# グラフ本体は stdout に含まれない → .lake/depgraph.json を読む
$graph = Get-Content .lake/depgraph.json | ConvertFrom-Json
```

▶ 注意: stdout はサマリー (~10行) のみ。`-Json` を省略すると出力先は `.lake/depgraph.md`（Mermaid 形式）になる。

▶ 注意: stdout はサマリー (~10行) のみ。`-Json` を省略すると出力先は `.lake/depgraph.md`（Mermaid 形式）になる。
```powershell
$stats = .github/skills/lean-depgraph/scripts/depgraph.ps1 -SorryOnly -Json
$g = Get-Content .lake/depgraph.json | ConvertFrom-Json

# 独立 sorry（出辺がないノード — 他 sorry に依存しない）
$fromNames = $g.edges | Select-Object -ExpandProperty from -Unique
$g.nodes | Where-Object { $fromNames -notcontains $_.name }
```

## 使い分け

| 目的 | 推奨オプション |
|---|---|
| 全容の俯瞰 | `-TheoremsOnly` |
| sorry 間依存の確認 | `-SorryOnly -Json` |
| 特定定理の依存先 | `-Root <name>` |
| 特定定義の利用箇所 | `-Root <name> -RootReverse` |

## トラブルシューティング

- `lake` が見つからない → **lean-setup** スキルを参照
- ビルドエラー → **lean-build** スキルで先にビルドを確認
- 出力が空 → `--ns` プレフィックスが正しいか確認（デフォルト: `S2IL`）
- グラフが巨大 → `--theorems-only` で定理のみに絞る、または `--ns` でサブモジュールに限定
