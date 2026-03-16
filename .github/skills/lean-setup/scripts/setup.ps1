#!/usr/bin/env pwsh
# lean-setup: elan ツールチェインの PATH 解決と動作確認 (PowerShell 7)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$ElanBin = Join-Path $env:USERPROFILE ".elan\bin"

# 1. elan の存在確認
if (-not (Test-Path $ElanBin)) {
    Write-Error "elan が見つかりません: $ElanBin`nインストール: https://github.com/leanprover/elan#installation"
    exit 1
}

# 2. PATH に追加
if ($env:PATH -notlike "*$ElanBin*") {
    $env:PATH = "$ElanBin;$env:PATH"
    Write-Host "PATH に追加: $ElanBin"
} else {
    Write-Host "PATH 設定済み: $ElanBin"
}

# 3. 動作確認
Write-Host "--- lake ---"
lake --version
Write-Host "--- lean ---"
lean --version
