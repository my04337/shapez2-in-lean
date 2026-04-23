#!/usr/bin/env pwsh
# SessionStart Hook: 証明状態の自動注入
# セッション開始時に docs/s2il/ と memories/repo/ から証明関連の状態を収集し、
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

    # --- 1. docs/s2il/ から証明関連ファイルを収集 ---
    $knowledgeDir = Join-Path $cwd "docs/s2il"
    if (Test-Path $knowledgeDir) {
        $proofFiles = Get-ChildItem -Path $knowledgeDir -Filter "*.md" |
            Where-Object {
                $_.Name -match 'proof|sorry|settle|gravity|bfs|equivariance'
            }
        if ($proofFiles.Count -gt 0) {
            $null = $messages.Add("Proof-related knowledge files:")
            foreach ($f in $proofFiles) {
                $null = $messages.Add("  - docs/s2il/$($f.Name)")
            }
        }
    }

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

    # --- 2. .lean ファイル内の sorry 一覧（高速パス: 直近の診断ファイル → フォールバック: ファイルスキャン） ---
    # セッション開始時点では今セッションの診断ファイルはまだないため、
    # 固定名 build-diagnostics.jsonl（lake build が直接生成する場合）をフォールバックとして参照する
    $sorryFiles = @()
    $diagFile = Join-Path $cwd ".lake/build-diagnostics.jsonl"

    if (Test-Path $diagFile) {
        # 高速パス: 前回ビルドの診断結果から sorry を抽出（ファイルスキャン不要）
        $sorryMap = @{}
        Get-Content $diagFile | ForEach-Object {
            $trimmed = $_.Trim()
            if ($trimmed) {
                try {
                    $entry = $trimmed | ConvertFrom-Json
                    if ($entry.PSObject.Properties["isSorry"] -and $entry.isSorry -eq $true) {
                        $f = $entry.file
                        if (-not $sorryMap.ContainsKey($f)) { $sorryMap[$f] = 0 }
                        $sorryMap[$f]++
                    }
                } catch { }
            }
        }
        foreach ($kv in $sorryMap.GetEnumerator()) {
            $sorryFiles += [PSCustomObject]@{
                Path  = $kv.Key
                Count = $kv.Value
            }
        }
    } else {
        # フォールバック: ファイルスキャン
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
    }

    if ($sorryFiles.Count -gt 0) {
        $totalSorries = ($sorryFiles | Measure-Object -Property Count -Sum).Sum
        $null = $messages.Add("")
        $null = $messages.Add("Current sorry status (total: $totalSorries):")
        foreach ($sf in ($sorryFiles | Sort-Object Count -Descending)) {
            $null = $messages.Add("  - $($sf.Path): $($sf.Count)")
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
            systemMessage = "[SessionStart] $sidMsg`nNo sorrys detected."
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
