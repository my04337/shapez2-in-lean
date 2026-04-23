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

# 全ログ保存（BOM なし UTF-8）
$logPath = Join-Path $lakeDir "build-log.txt"
[System.IO.File]::WriteAllText($logPath, ($rawOutput -join "`n") + "`n",
    [System.Text.UTF8Encoding]::new($false))

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
# セッション ID を読み込んでセッション固有パスで出力する
$sessionIdFile = Join-Path $lakeDir "session-id.tmp"

$sessionJsonlPath = Join-Path $lakeDir "build-diagnostics.jsonl"  # デフォルトは固定名
if (Test-Path $sessionIdFile) {
    $sid = ([System.IO.File]::ReadAllText($sessionIdFile, [System.Text.Encoding]::UTF8)).Trim()
    if ($sid) {
        $sessionJsonlPath = Join-Path $lakeDir "build-diagnostics-$sid.jsonl"
    }
}

$jsonlContent = $diagnostics | ForEach-Object {
    @{
        file     = $_.file
        line     = $_.line
        col      = $_.col
        severity = $_.severity
        message  = $_.message
        isSorry  = $_.isSorry
    } | ConvertTo-Json -Compress
}
# BOM なし UTF-8 で書き出し（PowerShell 5/7 共通で安全）
$utf8NoBom = [System.Text.UTF8Encoding]::new($false)
$jsonlText = ($jsonlContent -join "`n") + "`n"
[System.IO.File]::WriteAllText($sessionJsonlPath, $jsonlText, $utf8NoBom)

# 固定名ファイルにもコピー（lake build 直接実行時の下位互換用）
$jsonlPath = Join-Path $lakeDir "build-diagnostics.jsonl"
if ($sessionJsonlPath -ne $jsonlPath) {
    [System.IO.File]::WriteAllText($jsonlPath, $jsonlText, $utf8NoBom)
}

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
Write-Output "diagnostics: $sessionJsonlPath"
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

# --- symbol-map 更新（ビルド成功時のみ） ---
if ($buildExitCode -eq 0) {
    $symbolMapScript = Join-Path $PSScriptRoot "update-symbol-map.ps1"
    if (Test-Path $symbolMapScript) {
        try {
            & $symbolMapScript -Root ([System.IO.Path]::GetFullPath((Join-Path $PSScriptRoot "..\..\..\..\")))
        } catch {
            Write-Host "[build] symbol-map update failed (non-fatal): $_"
        }
    }

    # sig-digest（案 1 + 案 4: per-file signature & landmark index）
    $sigDigestScript = Join-Path $PSScriptRoot "update-sig-digest.ps1"
    if (Test-Path $sigDigestScript) {
        try {
            & $sigDigestScript -Root ([System.IO.Path]::GetFullPath((Join-Path $PSScriptRoot "..\..\..\..\")))
        } catch {
            Write-Host "[build] sig-digest update failed (non-fatal): $_"
        }
    }

    # sorry-card context 事前埋込（案 J + 案 N: 2026-04-23 #52）
    # sorry-plan.json に登録された全 sorry-card に extract-goal-context の出力を
    # upsert する。案 J の受動 read モデルが sorry 移動で陳腐化しないよう、build
    # フックで自動更新する。
    $sorryCardCtxScript = Join-Path $PSScriptRoot "update-sorry-card-context.ps1"
    if (Test-Path $sorryCardCtxScript) {
        try {
            & $sorryCardCtxScript -Root ([System.IO.Path]::GetFullPath((Join-Path $PSScriptRoot "..\..\..\..\")))
        } catch {
            Write-Host "[build] sorry-card context update failed (non-fatal): $_"
        }
    }
}

# --- sorry-goals 更新（ビルド成功/部分失敗問わず、診断 JSONL があれば実行） ---
$sorryGoalsScript = Join-Path $PSScriptRoot "update-sorry-goals.ps1"
if (Test-Path $sorryGoalsScript) {
    try {
        & $sorryGoalsScript -Root ([System.IO.Path]::GetFullPath((Join-Path $PSScriptRoot "..\..\..\..\"))) -Diag $sessionJsonlPath
    } catch {
        Write-Host "[build] sorry-goals update failed (non-fatal): $_"
    }
}

# ビルド失敗時は非ゼロで終了
if ($buildExitCode -ne 0) {
    exit $buildExitCode
}
