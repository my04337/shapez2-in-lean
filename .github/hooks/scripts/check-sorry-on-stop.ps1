#!/usr/bin/env pwsh
# Stop Hook: セッション終了前の warning チェック
# 非 sorry warning が残っている場合はエージェントをブロックする。
# sorry に起因する warning はブロック対象外とし、進捗記録を促すのみとする。
#
# 入力 (stdin JSON): { "hookEventName": "Stop", "cwd": "...", "stop_hook_active": false, ... }
# 出力 (stdout JSON):
#   ブロック時: { "hookSpecificOutput": { "hookEventName": "Stop", "decision": "block", "reason": "..." } }
#   通過時:     { "continue": true } または { "continue": true, "systemMessage": "..." }

[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

try {
    $rawInput = [Console]::In.ReadToEnd()
    $inputJson = $rawInput | ConvertFrom-Json
    $cwd = $inputJson.cwd
    if (-not $cwd) { $cwd = Get-Location }

    # 無限ループ防止: stop_hook_active が true なら何もしない
    if ($inputJson.PSObject.Properties["stop_hook_active"] -and $inputJson.stop_hook_active -eq $true) {
        @{ continue = $true } | ConvertTo-Json -Compress
        exit 0
    }

    # ======================================================================
    # 1. build-diagnostics.jsonl から非 sorry warning を検出してブロック判定
    # ======================================================================
    $diagFile = Join-Path $cwd ".lake/build-diagnostics.jsonl"
    $nonSorryWarnings = @()

    if (Test-Path $diagFile) {
        $lines = Get-Content $diagFile
        foreach ($line in $lines) {
            $trimmed = $line.Trim()
            if (-not $trimmed) { continue }
            try {
                $entry = $trimmed | ConvertFrom-Json
                # severity = warning かつ sorry 由来でない場合のみ対象
                if ($entry.severity -eq "warning") {
                    $isSorry = $entry.PSObject.Properties["isSorry"] -and $entry.isSorry -eq $true
                    if (-not $isSorry) {
                        $nonSorryWarnings += $entry
                    }
                }
            } catch { }  # 不正な JSON 行はスキップ
        }
    }

    if ($nonSorryWarnings.Count -gt 0) {
        $warnText = ($nonSorryWarnings | ForEach-Object {
            "  [$($_.file):$($_.line):$($_.col)] $($_.message)"
        }) -join "`n"
        $reason = @(
            "[Stop Hook] 前回ビルドで未解消の warning が $($nonSorryWarnings.Count) 件あります。",
            "sorry に起因する warning は除外済みです。",
            "以下の warning を解消してから終了してください。",
            "",
            $warnText
        ) -join "`n"

        @{
            hookSpecificOutput = @{
                hookEventName = "Stop"
                decision      = "block"
                reason        = $reason
            }
        } | ConvertTo-Json -Depth 5 -Compress
        exit 0
    }

    # ======================================================================
    # 2. sorry の残存チェック (情報通知のみ、ブロックしない)
    # ======================================================================
    $sorryFiles = @()
    $leanDirs = @("S2IL")
    foreach ($dir in $leanDirs) {
        $dirPath = Join-Path $cwd $dir
        if (Test-Path $dirPath) {
            $files = Get-ChildItem -Path $dirPath -Recurse -Filter "*.lean"
            foreach ($f in $files) {
                $sorryMatches = @(Select-String -Pattern '\bsorry\b' -Path $f.FullName |
                    Where-Object { $_.Line -notmatch '^\s*--' })
                if ($sorryMatches.Count -gt 0) {
                    $relativePath = $f.FullName.Substring($cwd.Length + 1)
                    $sorryFiles += [PSCustomObject]@{
                        Path  = $relativePath
                        Count = $sorryMatches.Count
                    }
                }
            }
        }
    }

    if ($sorryFiles.Count -gt 0) {
        $totalSorries = ($sorryFiles | Measure-Object -Property Count -Sum).Sum
        $fileList = ($sorryFiles | Sort-Object Count -Descending | ForEach-Object { "  - $($_.Path): $($_.Count) 件" }) -join "`n"
        $msg = @(
            "[Stop] sorry が $totalSorries 件残っています。"
            "セッション終了前に、証明の進捗状態をリポジトリメモリ (/memories/repo/) に記録することを推奨します。"
            ""
            "残存 sorry:"
            $fileList
        ) -join "`n"

        @{
            continue      = $true
            systemMessage = $msg
        } | ConvertTo-Json -Compress
    } else {
        @{ continue = $true } | ConvertTo-Json -Compress
    }
    exit 0
}
catch {
    Write-Error $_.Exception.Message
    @{ continue = $true } | ConvertTo-Json -Compress
    exit 1
}
