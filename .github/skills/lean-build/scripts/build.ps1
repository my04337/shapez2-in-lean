#!/usr/bin/env pwsh
# lean-build: Lean プロジェクトのビルド (PowerShell 7)
# 使い方: ./build.ps1 [-Clean] [-Update] [-Target <name>]

param(
    [switch]$Clean,
    [switch]$Update,
    [string]$Target
)

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

# ビルド
if ($Target) {
    Write-Host "==> lake build $Target"
    lake build $Target
} else {
    Write-Host "==> lake build"
    lake build
}

Write-Host "ビルド完了"
