#!/usr/bin/env pwsh
# SessionStart Hook: 証明状態の自動注入
# セッション開始時に docs/knowledge/ と memories/repo/ から証明関連の状態を収集し、
# エージェントのコンテキストに注入する
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

    $messages = [System.Collections.ArrayList]::new()

    # --- 1. docs/knowledge/ から証明関連ファイルを収集 ---
    $knowledgeDir = Join-Path $cwd "docs/knowledge"
    if (Test-Path $knowledgeDir) {
        $proofFiles = Get-ChildItem -Path $knowledgeDir -Filter "*.md" |
            Where-Object {
                $_.Name -match 'proof|sorry|settle|gravity|bfs|equivariance'
            }
        if ($proofFiles.Count -gt 0) {
            $null = $messages.Add("証明関連ナレッジファイル:")
            foreach ($f in $proofFiles) {
                $null = $messages.Add("  - docs/knowledge/$($f.Name)")
            }
        }
    }

    # --- 2. .lean ファイル内の sorry 一覧（高速スキャン） ---
    $sorryFiles = @()
    $leanDirs = @("S2IL", "Test")
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
        $null = $messages.Add("")
        $null = $messages.Add("現在の sorry 状況 (合計: $totalSorries 件):")
        foreach ($sf in ($sorryFiles | Sort-Object Count -Descending)) {
            $null = $messages.Add("  - $($sf.Path): $($sf.Count) 件")
        }
    }

    # --- 出力 ---
    if ($messages.Count -gt 0) {
        $msg = $messages -join "`n"
        $result = @{
            systemMessage = "[SessionStart] プロジェクト証明状態:`n$msg"
        }
    } else {
        $result = @{
            systemMessage = "[SessionStart] sorry は検出されませんでした。"
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
