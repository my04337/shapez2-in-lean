#!/usr/bin/env pwsh
# PreCompact Hook: コンテキスト圧縮前のセッションメモリ保存促進
# コンテキスト圧縮（context compaction）が発生する直前に呼ばれ、
# エージェントに未保存の作業状態をセッションメモリに退避するよう促す。
#
# 入力 (stdin JSON): { "hookEventName": "PreCompact", "cwd": "...", ... }
# 出力 (stdout JSON): { "systemMessage": "..." }

[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

try {
    $rawInput = [Console]::In.ReadToEnd()
    $inputJson = $rawInput | ConvertFrom-Json
    $cwd = $inputJson.cwd
    if (-not $cwd) { $cwd = Get-Location }

    $messages = [System.Collections.ArrayList]::new()

    # Opus 4.7 は長いホックメッセージを無視しがちなため 3 行以内に絞る。
    # ポジティブ表現（「保存してから作業を続行する」）で next action を明示する。
    $null = $messages.Add("Save current focus to /memories/session/ (target file:line + next 1–3 actions + sorry/error counts), then resume the next task.")
    $null = $messages.Add("Use str_replace/insert to update existing memory; create only if no session memory exists yet.")

    # --- sorry 残数の補足情報 ---
    $diagFile = Join-Path $cwd ".lake/build-diagnostics.jsonl"
    if (Test-Path $diagFile) {
        $sorryCount = 0
        Get-Content $diagFile | ForEach-Object {
            $trimmed = $_.Trim()
            if ($trimmed) {
                try {
                    $entry = $trimmed | ConvertFrom-Json
                    if ($entry.PSObject.Properties["isSorry"] -and $entry.isSorry -eq $true) {
                        $sorryCount++
                    }
                } catch { }
            }
        }
        if ($sorryCount -gt 0) {
            $null = $messages.Add("Current sorry count (last build): $sorryCount.")
        }
    }

    $msg = $messages -join "`n"
    @{ systemMessage = "[PreCompact] $msg" } | ConvertTo-Json -Compress
    exit 0
}
catch {
    # フック失敗時はサイレントに通過
    '{}'; exit 0
}
