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

    $null = $messages.Add("⚠ Context compaction is about to occur. Please do the following:")
    $null = $messages.Add("")
    $null = $messages.Add("1. Save current work state to /memories/session/")
    $null = $messages.Add("   - Files being edited and line ranges")
    $null = $messages.Add("   - Proof strategy and unsolved goals")
    $null = $messages.Add("   - Next steps")
    $null = $messages.Add("2. Verify the todo list is up to date")
    $null = $messages.Add("3. After saving session memory, **continue working**.")
    $null = $messages.Add("   Proceed to the next task unless the user explicitly asks to stop.")
    $null = $messages.Add("   Context compaction is not a reason to pause work.")

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
            $null = $messages.Add("")
            $null = $messages.Add("Current sorry count: $sorryCount (as of the last build)")
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
