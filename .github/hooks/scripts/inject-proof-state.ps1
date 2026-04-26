#!/usr/bin/env pwsh
# SessionStart Hook: コンテキスト注入の最小化
# セッション開始時にセッション情報と最小限の補助メッセージを注入する
#
# 入力 (stdin JSON): { "hookEventName": "SessionStart", "cwd": "...", ... }
# 出力 (stdout JSON): { "systemMessage": "..." }

[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

try {
    $rawInput = [Console]::In.ReadToEnd()
    $inputJson = $rawInput | ConvertFrom-Json
    $cwd = $inputJson.cwd
    if (-not $cwd) { $cwd = Get-Location }

    # --- セッション ID を生成して記録（セッション固有の診断ファイル名の決定に使用）---
    # build.ps1 はこの ID を読んで .lake/build-diagnostics-<id>.jsonl に書き出す
    # check-sorry-on-stop.ps1 はこの ID が存在する場合のみセッション内ビルドありと判定する
    $lakeDir = Join-Path $cwd ".lake"
    if (-not (Test-Path $lakeDir)) { New-Item -ItemType Directory -Path $lakeDir -Force | Out-Null }
    $sessionId = [System.Guid]::NewGuid().ToString("N").Substring(0, 8)
    $sessionIdFile = Join-Path $lakeDir "session-id.tmp"
    $sessionId | Set-Content -Path $sessionIdFile -Encoding UTF8

    # 前セッションの診断ファイルをクリーンアップ（.lake/ 直下の build-diagnostics-*.jsonl）
    if (Test-Path $lakeDir) {
        Get-ChildItem -Path $lakeDir -Filter "build-diagnostics-*.jsonl" -ErrorAction SilentlyContinue |
            Remove-Item -Force -ErrorAction SilentlyContinue
    }

    $messages = [System.Collections.ArrayList]::new()

    # --- 0. .gitignore の主要除外パスを通知 ---
    $gitignoreFile = Join-Path $cwd ".gitignore"
    if (Test-Path $gitignoreFile) {
        $ignoredDirs = @(Get-Content $gitignoreFile |
            Where-Object { $_ -match '^\s*[^#]' -and $_ -match '/' } |
            ForEach-Object { $_.Trim().TrimEnd('/') } |
            Where-Object { $_ -ne '' })
        if ($ignoredDirs.Count -gt 0) {
            $ignoreList = ($ignoredDirs | ForEach-Object { $_ }) -join ", "
            $null = $messages.Add("⚠ Gitignore excluded dirs: $ignoreList — Files placed here are not tracked by git. Use Verification/ or similar for files that need to persist.")
        }
    }

    # --- 出力 ---
    # セッション ID を systemMessage に含める（エージェントが REPL JSONL ファイル名に使用）
    $sidMsg = "Session ID: $sessionId (REPL JSONL template: Scratch/commands-${sessionId}-<topic>-<runId>.jsonl; use unique runId for parallel runs)"
    if ($messages.Count -gt 0) {
        $msg = $messages -join "`n"
        $result = @{
            systemMessage = "[SessionStart] $sidMsg`n$msg"
        }
    } else {
        $result = @{
            systemMessage = "[SessionStart] $sidMsg"
        }
    }

    $result | ConvertTo-Json -Compress
    exit 0
}
catch {
    Write-Error $_.Exception.Message
    @{} | ConvertTo-Json -Compress
    exit 1
}
