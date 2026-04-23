#!/usr/bin/env pwsh
# update-sorry-card-context.ps1
# 案 J（2026-04-23）: 各 sorry-card に extract-goal-context 出力を事前埋込する。
#
# 使用例:
#   ./update-sorry-card-context.ps1                     # sorry-plan.json の全 sorry を更新
#   ./update-sorry-card-context.ps1 -Symbol placeLDGroups_landing_groundingEdge_mono
#   ./update-sorry-card-context.ps1 -DryRun             # ファイル書き込みなしで出力確認
#
# 効果: sorry-card の「候補補題（事前抽出）」セクションを upsert する。
#       エージェントは card を読むだけで extract-goal-context の出力が得られるため、
#       「コマンドを読んでも実行しない」問題（案 G の失敗）を能動的事前実行で回避する。

param(
    [string]$Symbol = "",          # 特定シンボルのみ更新（空なら全件）
    [switch]$DryRun,               # ファイル書き込みをスキップして stdout に出力
    [string]$Root
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

if (-not $Root) {
    $Root = (Resolve-Path (Join-Path $PSScriptRoot "..\..\..\..")).Path
}
$Root = $Root.TrimEnd('\', '/')

$sorryPlanPath = Join-Path $Root "S2IL" "_agent" "sorry-plan.json"
$sorryCardsDir = Join-Path $Root "S2IL" "_agent" "sorry-cards"
$extractScript = Join-Path $PSScriptRoot "extract-goal-context.ps1"

if (-not (Test-Path $sorryPlanPath)) { Write-Error "sorry-plan.json not found: $sorryPlanPath"; exit 1 }
if (-not (Test-Path $extractScript)) { Write-Error "extract-goal-context.ps1 not found: $extractScript"; exit 1 }

$planText = Get-Content $sorryPlanPath -Raw
# sorry-plan.json は単一 JSON オブジェクト（末尾に古いオブジェクトが付いている場合は最初のみ使う）
# 連続した JSON オブジェクトが存在する場合は最初の "}" で終わるブロックを取り出す
$firstObjEnd = $planText.IndexOf("`n{", 1)
if ($firstObjEnd -gt 0) {
    $planText = $planText.Substring(0, $firstObjEnd)
}
$plan = $planText | ConvertFrom-Json
$today = Get-Date -Format 'yyyy-MM-dd'

# sorry エントリの列挙: sorrys 配下の各エントリのうち status が resolved 以外
$entries = @()
foreach ($step in $plan.sorrys) {
    if ($Symbol -and $step.symbol -ne $Symbol) { continue }
    if ($step.status -eq "resolved") { continue }
    if (-not $step.file -or -not $step.line) {
        Write-Warning "Skip $($step.symbol): file/line missing in sorry-plan.json"
        continue
    }
    $entries += $step
}

if ($entries.Count -eq 0) {
    Write-Host "No matching sorry entries found."
    exit 0
}

foreach ($entry in $entries) {
    $sym = $entry.symbol
    $file = $entry.file
    $line = [int]$entry.line

    $cardPath = Join-Path $sorryCardsDir "$sym.md"
    if (-not (Test-Path $cardPath)) {
        Write-Warning "Sorry-card not found, skip: $cardPath"
        continue
    }

    Write-Host "Processing $sym ($file`:$line)..."

    # extract-goal-context.ps1 を実行して出力を取得
    $rawOutput = & $extractScript -File $file -Line $line -Root $Root *>&1
    $outputLines = @($rawOutput | ForEach-Object { "$_" } | Where-Object { $_ -match '^\s*\*?\s*\{' })

    if ($outputLines.Count -eq 0) {
        Write-Warning "  No hits from extract-goal-context, skip."
        continue
    }

    # JSONL 行をパースして markdown テーブルを構築
    $rows = [System.Collections.ArrayList]::new()
    foreach ($jsonLine in $outputLines) {
        $clean = $jsonLine -replace '^\*? +', ''
        try {
            $obj = $clean | ConvertFrom-Json -ErrorAction Stop
            $simpleSym = ($obj.symbol -split '\.')[-1]
            $filePart = if ($obj.file) { "$($obj.file):$($obj.line)" } else { "" }
            # sig は長い場合があるので 80 文字で切る
            $sigShort = if ($obj.sig -and $obj.sig.Length -gt 80) { $obj.sig.Substring(0, 77) + "..." } else { $obj.sig }
            $null = $rows.Add([PSCustomObject]@{
                Symbol  = $simpleSym
                Sig     = $sigShort
                File    = $filePart
            })
        } catch {
            # パース失敗は無視
        }
    }

    if ($rows.Count -eq 0) {
        Write-Warning "  All JSONL lines failed to parse, skip."
        continue
    }

    # マークダウンテーブル生成
    $tableLines = [System.Collections.ArrayList]::new()
    $null = $tableLines.Add("## 候補補題（extract-goal-context 事前抽出、$today）")
    $null = $tableLines.Add("")
    $null = $tableLines.Add("| 補題 | シグネチャ（先頭 80 文字） | ファイル:行 |")
    $null = $tableLines.Add("|---|---|---|")
    foreach ($r in $rows) {
        $null = $tableLines.Add("| ``$($r.Symbol)`` | ``$($r.Sig)`` | ``$($r.File)`` |")
    }
    $newSection = $tableLines -join "`n"

    # sorry-card を読み込み
    $cardContent = [System.IO.File]::ReadAllText($cardPath)

    # 既存の「候補補題」セクションがあれば置換、なければ「直接使う補題」セクションの直前に挿入
    $sectionHeader = "## 候補補題（extract-goal-context 事前抽出"
    if ($cardContent -match [regex]::Escape($sectionHeader)) {
        # 既存セクションを次の `## `, `### `, `---` (HR), `<details`, またはファイル末尾まで置換
        # 注意: `(?s)` のみを使用（`(?m)` を付けると `$` が行末にマッチして直後で停止してしまう）
        $pattern = '(?s)## 候補補題（extract-goal-context 事前抽出[^\n]*\n.*?(?=\n## |\n### |\n---\s*\n|\n<details|\z)'
        $cardContent = [regex]::Replace($cardContent, $pattern, $newSection)
        Write-Host "  Updated existing section."
    } elseif ($cardContent -match '### 直接使う補題') {
        # 「直接使う補題」の前に挿入
        $cardContent = $cardContent -replace '(### 直接使う補題)', "$newSection`n`n`$1"
        Write-Host "  Inserted before '直接使う補題' section."
    } elseif ($cardContent -match '---\s*\n\n<details') {
        # `<details>` 前の区切り直前に挿入
        $cardContent = $cardContent -replace '(---\s*\n\n<details)', "$newSection`n`n`$1"
        Write-Host "  Inserted before '<details>' section."
    } else {
        # ファイル末尾に追記
        $cardContent = $cardContent.TrimEnd() + "`n`n" + $newSection + "`n"
        Write-Host "  Appended at end."
    }

    if ($DryRun) {
        Write-Host "--- DryRun: would write to $cardPath ---"
        Write-Host $newSection
        Write-Host "---"
    } else {
        [System.IO.File]::WriteAllText($cardPath, $cardContent, [System.Text.Encoding]::UTF8)
        Write-Host "  Written: $cardPath"
    }
}

Write-Host "Done."
