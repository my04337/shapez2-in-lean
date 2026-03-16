#!/usr/bin/env pwsh
# lean-run: Lean プロジェクトのビルド・実行・出力検証 (PowerShell 7)
# 使い方: ./run.ps1 [-Target <name>] [-Expected <string>]

param(
    [string]$Target = "s2il",
    [string]$Expected
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

# lean-build: ビルド (PATH 解決含む)
$BuildScript = Join-Path $PSScriptRoot "..\..\lean-build\scripts\build.ps1"
if (Test-Path $BuildScript) {
    & $BuildScript -Target $Target
} else {
    Write-Host "==> lake build $Target"
    lake build $Target
}

# 実行
Write-Host "==> lake exe $Target"
$output = lake exe $Target
Write-Host $output

# 出力検証 (期待値が指定された場合)
if ($Expected) {
    if ($output -eq $Expected) {
        Write-Host "検証OK: 出力が期待値と一致"
    } else {
        Write-Error "検証NG: 期待='$Expected' 実際='$output'"
        exit 1
    }
}
