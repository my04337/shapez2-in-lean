#!/usr/bin/env pwsh
# lean-run: Lean プロジェクトのビルド・実行・出力検証 (PowerShell 7)
# 使い方: ./run.ps1 [-Target <name>] [-Expected <string>]
#
# 出力:
#   stdout  - ビルド診断サマリー + 実行結果サマリー
#   .lake/build-log.txt          - 全ビルドログ (build.ps1 が生成)
#   .lake/build-diagnostics.jsonl - ビルド診断 (build.ps1 が生成)
#   .lake/run-log.txt            - 実行ログ

param(
    [string]$Target = "s2il",
    [string]$Expected
)

[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

# lean-build: 全デフォルトターゲットをビルド (Test ライブラリの #guard テストも含む)
$BuildScript = Join-Path $PSScriptRoot "..\..\lean-build\scripts\build.ps1"
$buildFailed = $false
if (Test-Path $BuildScript) {
    & $BuildScript
    if ($LASTEXITCODE -ne 0) { $buildFailed = $true }
} else {
    Write-Host "==> lake build"
    lake build
    if ($LASTEXITCODE -ne 0) { $buildFailed = $true }
}

# ビルド失敗時は実行をスキップ
if ($buildFailed) {
    Write-Output ""
    Write-Output "=== RUN RESULT ==="
    Write-Output "status: skipped"
    Write-Output "reason: build_failed"
    Write-Output "=== END RUN ==="
    exit 1
}

# --- 実行 ---
Write-Host "==> lake exe $Target"

$lakeDir = Join-Path $PSScriptRoot "..\..\..\..\.lake"
$lakeDir = [System.IO.Path]::GetFullPath($lakeDir)
if (-not (Test-Path $lakeDir)) { New-Item -ItemType Directory -Path $lakeDir -Force | Out-Null }
$runLogPath = Join-Path $lakeDir "run-log.txt"

$runOutput = & lake exe $Target 2>&1 | ForEach-Object { $_.ToString() }
$runExitCode = $LASTEXITCODE

# 実行ログ保存
$runOutput | Out-File -FilePath $runLogPath -Encoding utf8

# --- 実行結果サマリー ---
if ($runExitCode -eq 0) { $runStatus = "success" } else { $runStatus = "failure" }

Write-Output ""
Write-Output "=== RUN RESULT ==="
Write-Output "status: $runStatus"
Write-Output "exit_code: $runExitCode"
Write-Output "target: $Target"
Write-Output "log: $runLogPath"

# stdout 出力（最大50行に制限）
$outputLines = $runOutput
if ($outputLines.Count -gt 50) {
    Write-Output "output_lines: $($outputLines.Count) (先頭50行を表示)"
    Write-Output "---"
    $outputLines | Select-Object -First 50 | ForEach-Object { Write-Output $_ }
    Write-Output "... (以降省略、全件は $runLogPath を参照)"
} elseif ($outputLines.Count -gt 0) {
    Write-Output "output_lines: $($outputLines.Count)"
    Write-Output "---"
    $outputLines | ForEach-Object { Write-Output $_ }
} else {
    Write-Output "output_lines: 0"
}

# 出力検証 (期待値が指定された場合)
if ($Expected) {
    $actualJoined = ($runOutput -join "`n").Trim()
    if ($actualJoined -eq $Expected) {
        Write-Output "verification: pass"
    } else {
        Write-Output "verification: fail"
        Write-Output "expected: $Expected"
        Write-Output "actual: $actualJoined"
    }
}

Write-Output "=== END RUN ==="

# 実行失敗時は非ゼロで終了
if ($runExitCode -ne 0) {
    exit $runExitCode
}
