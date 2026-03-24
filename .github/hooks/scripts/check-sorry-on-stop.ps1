#!/usr/bin/env pwsh
# Stop Hook: セッション終了前の sorry 残存チェック
# sorry が残っている場合に警告メッセージを出し、進捗記録を促す
#
# 入力 (stdin JSON): { "hookEventName": "Stop", "cwd": "...", "stop_hook_active": false, ... }
# 出力 (stdout JSON): { "systemMessage": "...", "hookSpecificOutput": { ... } }

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

    # .lean ファイルの sorry を高速スキャン
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
