#!/usr/bin/env pwsh
# lean-depgraph: 証明依存グラフの生成 (PowerShell 7)
# 使い方: ./depgraph.ps1 [-Private] [-Json] [-Namespace <name>] [-TheoremsOnly] [-Output <path>]
#                  [-Root <name>] [-RootReverse]
#
# 出力:
#   指定パスまたは .lake/depgraph.md (.json) - グラフ本体
#   stdout - 構造化サマリー (=== DEPGRAPH RESULT === ... === END DEPGRAPH ===)

param(
    [switch]$Private,
    [switch]$Json,
    [string]$Namespace,
    [switch]$TheoremsOnly,
    [string]$Output,
    [string]$Root,
    [switch]$RootReverse
)

[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

# lean-setup: PATH 解決
$SetupScript = Join-Path $PSScriptRoot "..\..\lean-setup\scripts\setup.ps1"
if (Test-Path $SetupScript) { & $SetupScript }

# depgraph ターゲットのビルド（S2IL も自動でビルドされる）
Write-Host "==> lake build depgraph --no-ansi"
$buildOutput = & lake build depgraph --no-ansi 2>&1 | ForEach-Object { $_.ToString() }
$buildExitCode = $LASTEXITCODE

if ($buildExitCode -ne 0) {
    Write-Host ""
    Write-Host "=== DEPGRAPH RESULT ==="
    Write-Host "status: failed"
    Write-Host "reason: build_failed"
    Write-Host "exit_code: $buildExitCode"
    foreach ($line in $buildOutput) { Write-Host $line }
    Write-Host "=== END DEPGRAPH ==="
    exit $buildExitCode
}

# .lake ディレクトリの確保
$lakeDir = Join-Path $PSScriptRoot "..\..\..\..\.lake"
$lakeDir = [System.IO.Path]::GetFullPath($lakeDir)
if (-not (Test-Path $lakeDir)) { New-Item -ItemType Directory -Path $lakeDir -Force | Out-Null }

# 出力先の決定
if ($Output) {
    $outputPath = $Output
} elseif ($Json) {
    $outputPath = Join-Path $lakeDir "depgraph.json"
} else {
    $outputPath = Join-Path $lakeDir "depgraph.md"
}

# lake exe 引数の組み立て
$depArgs = @()
if ($Private) { $depArgs += "--private" }
if ($Json) { $depArgs += "--json" }
if ($Namespace) { $depArgs += "--ns"; $depArgs += $Namespace }
if ($TheoremsOnly) { $depArgs += "--theorems-only" }
if ($Root) { $depArgs += "--root"; $depArgs += $Root }
if ($RootReverse) { $depArgs += "--root-reverse" }
$depArgs += "--output"
$depArgs += $outputPath

# 実行
Write-Host "==> lake exe depgraph $($depArgs -join ' ')"
$runOutput = & lake exe depgraph @depArgs 2>&1 | ForEach-Object { $_.ToString() }
$runExitCode = $LASTEXITCODE

# --- 結果サマリー ---
Write-Host ""
Write-Host "=== DEPGRAPH RESULT ==="

if ($runExitCode -eq 0) {
    Write-Host "status: success"
} else {
    Write-Host "status: failed"
}
Write-Host "exit_code: $runExitCode"
Write-Host "output: $outputPath"

# 統計情報の表示（lake exe の stderr 出力から抽出）
$inStats = $false
foreach ($line in $runOutput) {
    if ($line -match "=== DEPGRAPH STATISTICS ===") { $inStats = $true }
    if ($inStats) { Write-Host $line }
    if ($line -match "=== END STATISTICS ===") { $inStats = $false }
}

Write-Host "=== END DEPGRAPH ==="

if ($runExitCode -ne 0) {
    exit $runExitCode
}
