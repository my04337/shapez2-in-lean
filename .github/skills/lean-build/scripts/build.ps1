#!/usr/bin/env pwsh
# lean-build: Lean プロジェクトのビルド (PowerShell 7)
# 使い方: ./build.ps1 [-Clean] [-Update] [-Target <name>]
#
# 出力:
#   stdout  - 構造化サマリー (=== BUILD DIAGNOSTICS === ... === END DIAGNOSTICS ===)
#   .lake/build-log.txt          - 全ビルドログ
#   .lake/build-diagnostics.jsonl - 診断メッセージ (1行1JSON)

param(
    [switch]$Clean,
    [switch]$Update,
    [string]$Target
)

[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

# lean-setup: PATH 解決
$SetupScript = Join-Path $PSScriptRoot "..\..\lean-setup\scripts\setup.ps1"
if (Test-Path $SetupScript) { & $SetupScript }

# クリーンビルド
if ($Clean) {
    Write-Host "==> lake clean"
    lake clean
}

# 依存更新
if ($Update) {
    Write-Host "==> lake update"
    lake update
}

# --- ビルド実行 & ログキャプチャ ---
$buildArgs = @("build", "--no-ansi")
if ($Target) { $buildArgs += $Target }

Write-Host "==> lake $($buildArgs -join ' ')"

# lake build を実行し、stdout/stderr を全てキャプチャ
$rawOutput = & lake @buildArgs 2>&1 | ForEach-Object { $_.ToString() }
$buildExitCode = $LASTEXITCODE

# .lake ディレクトリの確保
$lakeDir = Join-Path $PSScriptRoot "..\..\..\..\.lake"
$lakeDir = [System.IO.Path]::GetFullPath($lakeDir)
if (-not (Test-Path $lakeDir)) { New-Item -ItemType Directory -Path $lakeDir -Force | Out-Null }

# 全ログ保存
$logPath = Join-Path $lakeDir "build-log.txt"
$rawOutput | Out-File -FilePath $logPath -Encoding utf8

# --- 診断メッセージのパース ---
# Lake 出力形式: "severity: file:line:col: message"
$diagnostics = [System.Collections.ArrayList]::new()
$diagPattern = '^(error|warning|info):\s*(.+?):(\d+):(\d+):\s*(.+)$'
$sorryPattern = "declaration uses .sorry."

foreach ($line in $rawOutput) {
    if ($line -match $diagPattern) {
        $null = $diagnostics.Add([PSCustomObject]@{
            file     = $Matches[2]
            line     = [int]$Matches[3]
            col      = [int]$Matches[4]
            severity = $Matches[1]
            message  = $Matches[5]
            isSorry  = ($Matches[5] -match $sorryPattern)
        })
    }
}

# JSONL 保存
$jsonlPath = Join-Path $lakeDir "build-diagnostics.jsonl"
$diagnostics | ForEach-Object {
    @{
        file     = $_.file
        line     = $_.line
        col      = $_.col
        severity = $_.severity
        message  = $_.message
        isSorry  = $_.isSorry
    } | ConvertTo-Json -Compress
} | Out-File -FilePath $jsonlPath -Encoding utf8

# --- カウント ---
$errorCount   = @($diagnostics | Where-Object { $_.severity -eq "error" }).Count
$sorryCount   = @($diagnostics | Where-Object { $_.isSorry -eq $true }).Count
$warningCount = @($diagnostics | Where-Object { $_.severity -eq "warning" -and $_.isSorry -ne $true }).Count
$infoCount    = @($diagnostics | Where-Object { $_.severity -eq "info" }).Count

if ($buildExitCode -eq 0) { $status = "success" } else { $status = "failure" }

# --- 構造化サマリー出力 ---
# Write-Output でパイプライン / 変数キャプチャ可能にする
Write-Output ""
Write-Output "=== BUILD DIAGNOSTICS ==="
Write-Output "status: $status"
Write-Output "exit_code: $buildExitCode"
Write-Output "errors: $errorCount"
Write-Output "sorries: $sorryCount"
Write-Output "warnings: $warningCount"
Write-Output "info: $infoCount"
Write-Output "log: $logPath"
Write-Output "diagnostics: $jsonlPath"
Write-Output ""

# トリアージ順: error > sorry > warning > info (最大20件)
$shown = 0
$maxShow = 20

# errors
foreach ($d in ($diagnostics | Where-Object { $_.severity -eq "error" })) {
    if ($shown -ge $maxShow) { Write-Output "... (以降省略、全件は $jsonlPath を参照)"; break }
    Write-Output "[ERROR] $($d.file):$($d.line):$($d.col): $($d.message)"
    $shown++
}

# sorries (warning の中で sorry を含むもの)
foreach ($d in ($diagnostics | Where-Object { $_.isSorry -eq $true })) {
    if ($shown -ge $maxShow) { Write-Output "... (以降省略、全件は $jsonlPath を参照)"; break }
    Write-Output "[SORRY] $($d.file):$($d.line):$($d.col): $($d.message)"
    $shown++
}

# warnings (sorry 以外)
foreach ($d in ($diagnostics | Where-Object { $_.severity -eq "warning" -and $_.isSorry -ne $true })) {
    if ($shown -ge $maxShow) { Write-Output "... (以降省略、全件は $jsonlPath を参照)"; break }
    Write-Output "[WARNING] $($d.file):$($d.line):$($d.col): $($d.message)"
    $shown++
}

# info
foreach ($d in ($diagnostics | Where-Object { $_.severity -eq "info" })) {
    if ($shown -ge $maxShow) { Write-Output "... (以降省略、全件は $jsonlPath を参照)"; break }
    Write-Output "[INFO] $($d.file):$($d.line):$($d.col): $($d.message)"
    $shown++
}

Write-Output "=== END DIAGNOSTICS ==="

# ビルド失敗時は非ゼロで終了
if ($buildExitCode -ne 0) {
    exit $buildExitCode
}
