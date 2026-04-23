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

    # proof-suppressed.flag が存在する場合は全証明フック出力を抑止する
    # (session-efficiency スキル発動時やユーザが明示的に証明停止を指示した場合に作成される)
    $suppressFlag = Join-Path $cwd ".lake/proof-suppressed.flag"
    if (Test-Path $suppressFlag) {
        @{ continue = $true } | ConvertTo-Json -Compress
        exit 0
    }

    # ======================================================================
    # 0. セッション内にビルドが実行されたかチェック（前セッション診断の混入防止）
    # ======================================================================
    $diagFile = $null
    $sessionIdFile = Join-Path $cwd ".lake/session-id.tmp"
    if (Test-Path $sessionIdFile) {
        $sessionId = (Get-Content $sessionIdFile -Raw).Trim()
        if ($sessionId) {
            $candidate = Join-Path $cwd ".lake/build-diagnostics-$sessionId.jsonl"
            if (Test-Path $candidate) {
                $diagFile = $candidate
            }
        }
    }

    if (-not $diagFile) {
        @{ continue = $true } | ConvertTo-Json -Compress
        exit 0
    }

    # ======================================================================
    # 1. build-diagnostics-<sid>.jsonl から非 sorry warning を検出してブロック判定
    # ======================================================================
    $nonSorryWarnings = @()
    $sorryEntries = @()

    $lines = Get-Content $diagFile
    foreach ($line in $lines) {
        $trimmed = $line.Trim()
        if (-not $trimmed) { continue }
        try {
            $entry = $trimmed | ConvertFrom-Json
            $isSorry = $entry.PSObject.Properties["isSorry"] -and $entry.isSorry -eq $true
            if ($entry.severity -eq "warning") {
                if ($isSorry) {
                    $sorryEntries += $entry
                } else {
                    $nonSorryWarnings += $entry
                }
            }
        } catch { }  # 不正な JSON 行はスキップ
    }

    if ($nonSorryWarnings.Count -gt 0) {
        $warnText = ($nonSorryWarnings | ForEach-Object {
            "  [$($_.file):$($_.line):$($_.col)] $($_.message)"
        }) -join "`n"
        $reason = @(
            "[Stop Hook] $($nonSorryWarnings.Count) unresolved warning(s) found in the last build.",
            "Warnings originating from sorry have been excluded.",
            "Please resolve the following warnings before exiting.",
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
    # 2. untracked ファイルの警告（意図しない新規ファイルの検出）
    # ======================================================================
    $untrackedWarnings = @()
    try {
        Push-Location $cwd
        $untrackedFiles = @(git status --porcelain 2>$null |
            Where-Object { $_ -match '^\?\?' } |
            ForEach-Object { ($_ -replace '^\?\?\s*', '').Trim('"') })
        Pop-Location

        # プロジェクトルート直下の .lean / .md ファイルは意図しない可能性が高い
        foreach ($f in $untrackedFiles) {
            # トップレベルの .lean/.md（サブディレクトリでないもの）
            if ($f -notmatch '/' -and $f -match '\.(lean|md)$') {
                $untrackedWarnings += $f
            }
        }
    } catch {
        # git コマンド失敗時はスキップ
    }

    if ($untrackedWarnings.Count -gt 0) {
        $fileList = ($untrackedWarnings | ForEach-Object { "  - $_" }) -join "`n"
        $reason = @(
            "[Stop Hook] $($untrackedWarnings.Count) unexpected untracked file(s) found in the project root.",
            "Place temporary files in Scratch/ or delete them if unnecessary.",
            "",
            $fileList
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
    # 3. sorry の残存チェック (情報通知のみ、ブロックしない)
    #    ターン内に .lean ファイル編集があった場合のみ通知する
    #    build 診断の isSorry=true を唯一の情報源とする
    # ======================================================================
    # .lean 編集フラグの確認: count-sorry フックがこのターン中に作成する
    $leanEditedFlag = Join-Path $cwd ".lake/lean-edited-this-turn.flag"
    $leanWasEdited = Test-Path $leanEditedFlag
    # フラグを削除（次回のターンに引きずらないようリセット）
    if ($leanWasEdited) {
        Remove-Item $leanEditedFlag -Force -ErrorAction SilentlyContinue
    }
    $sorryFiles = @()
    if ($sorryEntries.Count -gt 0) {
        $sorryFiles = $sorryEntries |
            Group-Object -Property file |
            ForEach-Object {
                [PSCustomObject]@{
                    Path  = $_.Name
                    Count = $_.Count
                }
            }
    }

    if ($sorryFiles.Count -gt 0) {
        $totalSorries = ($sorryFiles | Measure-Object -Property Count -Sum).Sum
        $fileList = ($sorryFiles | Sort-Object Count -Descending | ForEach-Object { "  - $($_.Path): $($_.Count)" }) -join "`n"
        $msg = @(
            "[Stop] $totalSorries sorry(s) remain."
            "Recommended: record proof progress in repository memory (/memories/repo/) before ending the session."
            ""
            "Remaining sorrys:"
            $fileList
        ) -join "`n"

        if ($leanWasEdited) {
            @{
                continue      = $true
                systemMessage = $msg
            } | ConvertTo-Json -Compress
        } else {
            # .lean 編集なしターン: sorry 実証作業を行っていないため通知を抑止する
            @{ continue = $true } | ConvertTo-Json -Compress
        }
    }
    # ======================================================================
    # 4. 未完了タスクの残存チェック (情報通知のみ、ブロックしない)
    # ======================================================================
    elseif ($false) {
        # sorry がある場合は上のブロックで処理済み。このブロックは到達しない。
    }

    if ($sorryFiles.Count -eq 0) {
        @{ continue = $true } | ConvertTo-Json -Compress
    }
    exit 0
}
catch {
    Write-Error $_.Exception.Message
    @{ continue = $true } | ConvertTo-Json -Compress
    exit 1
}
