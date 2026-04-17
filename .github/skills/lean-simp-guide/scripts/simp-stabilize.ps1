#!/usr/bin/env pwsh
# SPDX-FileCopyrightText: 2026 my04337
# SPDX-License-Identifier: MIT
#
# simp-stabilize.ps1 — bare simp → simp only 一括安定化パイプライン
#
# 使い方:
#   .github/skills/lean-simp-guide/scripts/simp-stabilize.ps1 -File S2IL/Behavior/Gravity.lean
#   .github/skills/lean-simp-guide/scripts/simp-stabilize.ps1 -File S2IL/Behavior/Gravity.lean -DryRun
#
# 処理フロー:
#   1. 対象ファイルをバックアップ (.bak)
#   2. bare simp/simp_all → simp?/simp_all? に一括変換
#   3. lake env lean --json で位置付き提案を取得（.NET ProcessStartInfo 使用）
#   4. 提案を行番号でマッピングし、ソースに適用
#   5. バックアップを削除（-KeepBackup で保持可能）
#
# 注意:
#   - 対象ファイルが lake build でエラー 0 の状態から実行すること
#   - ネスト括弧パターン (simp [show ... from by ...]) は手動修正が必要
#   - 実行後は必ず lake build で検証すること

[CmdletBinding()]
param(
    [Parameter(Mandatory)]
    [string]$File,

    [switch]$DryRun,

    [switch]$KeepBackup
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"
[Console]::OutputEncoding = [System.Text.Encoding]::UTF8

# --- ヘルパー関数 ---

function Write-Info($msg) { Write-Host "[INFO] $msg" -ForegroundColor Cyan }
function Write-Warn($msg) { Write-Host "[WARN] $msg" -ForegroundColor Yellow }
function Write-Ok($msg)   { Write-Host "[ OK ] $msg" -ForegroundColor Green }
function Write-Err($msg)  { Write-Host "[ERR ] $msg" -ForegroundColor Red }

# --- バリデーション ---

if (-not (Test-Path $File)) {
    Write-Err "ファイルが見つかりません: $File"
    exit 1
}

$absFile = Resolve-Path $File

# --- Step 1: バックアップ ---

$bakFile = "$absFile.bak"
Copy-Item $absFile $bakFile -Force
Write-Info "バックアップ作成: $bakFile"

# --- Step 2: bare simp → simp? 変換 ---

$content = [System.IO.File]::ReadAllText($absFile, [System.Text.Encoding]::UTF8)
$lines = $content -split "`n"

$convertCount = 0
$newLines = [System.Collections.ArrayList]::new()

foreach ($line in $lines) {
    $original = $line

    # simp only / simp_all only は既に安定化済み → スキップ
    if ($line -match '\bsimp\s+only\b' -or $line -match '\bsimp_all\s+only\b') {
        $null = $newLines.Add($line)
        continue
    }

    # simp_all (config := ...) only は安定化済み → スキップ
    if ($line -match '\bsimp_all\s*\(config\s*:=.*?\)\s*only\b') {
        $null = $newLines.Add($line)
        continue
    }

    # simp? / simp_all? は既にクエリ形式 → スキップ
    if ($line -match '\bsimp(_all)?\?\b') {
        $null = $newLines.Add($line)
        continue
    }

    # コメント行はスキップ
    if ($line -match '^\s*--') {
        $null = $newLines.Add($line)
        continue
    }

    # simp_all → simp_all?
    $newLine = $line -replace '\bsimp_all\b', 'simp_all?'

    # simp → simp? (simp_all? の中の simp を二重変換しないよう注意)
    if ($newLine -eq $line) {
        $newLine = $line -replace '\bsimp\b', 'simp?'
    }

    if ($newLine -ne $original) {
        $convertCount++
    }

    $null = $newLines.Add($newLine)
}

Write-Info "bare simp → simp? 変換: $convertCount 件"

if ($convertCount -eq 0) {
    Write-Ok "安定化対象なし。終了します。"
    Remove-Item $bakFile -ErrorAction SilentlyContinue
    exit 0
}

# simp? 版を書き出し
$newContent = $newLines -join "`n"
[System.IO.File]::WriteAllText($absFile, $newContent, (New-Object System.Text.UTF8Encoding $false))

if ($DryRun) {
    Write-Warn "DryRun: simp? 変換のみ実行。lean --json は実行しません。"
    # 復元
    Copy-Item $bakFile $absFile -Force
    Remove-Item $bakFile -ErrorAction SilentlyContinue
    exit 0
}

# --- Step 3: lean --json で提案取得 ---

Write-Info "lean --json 実行中... (数分かかる場合があります)"

$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"

$psi = New-Object System.Diagnostics.ProcessStartInfo
$psi.FileName = "lake"
$psi.Arguments = "env lean --json $File"
$psi.RedirectStandardOutput = $true
$psi.RedirectStandardError = $true
$psi.UseShellExecute = $false
$psi.StandardOutputEncoding = [System.Text.Encoding]::UTF8
$p = [System.Diagnostics.Process]::Start($psi)
$stdout = $p.StandardOutput.ReadToEnd()
$p.WaitForExit()

if ($p.ExitCode -ne 0) {
    Write-Err "lean --json が失敗しました (exit code: $($p.ExitCode))"
    Write-Warn "バックアップから復元します"
    Copy-Item $bakFile $absFile -Force
    exit 1
}

# --- Step 4: 提案をパース ---

$jsonLines = $stdout -split "`n" | Where-Object { $_.Trim() }
$suggestions = @{}  # line -> list of suggestion texts
$totalSuggestions = 0

foreach ($jl in $jsonLines) {
    try {
        $obj = $jl | ConvertFrom-Json -ErrorAction SilentlyContinue
        if (-not $obj) { continue }
        if ($obj.severity -ne "info") { continue }
        if ($obj.data -notmatch "Try this:") { continue }

        $line = $obj.pos.line
        # (?s) で複数行の提案にも対応
        if ($obj.data -match '(?s)Try this:\s*(?:\[apply\]\s*)?(.+)') {
            $suggestion = $Matches[1].Trim()
            if (-not $suggestions.ContainsKey($line)) {
                $suggestions[$line] = [System.Collections.ArrayList]::new()
            }
            $null = $suggestions[$line].Add($suggestion)
            $totalSuggestions++
        }
    } catch { }
}

Write-Info "提案取得: $totalSuggestions 件 ($($suggestions.Count) ユニーク行)"

# --- Step 5: 提案をソースに適用 ---

# バックアップから元のソースを読み直し
$originalContent = [System.IO.File]::ReadAllText($bakFile, [System.Text.Encoding]::UTF8)
$originalLines = $originalContent -split "`n"

$appliedCount = 0
$skippedCount = 0
$skippedLines = [System.Collections.ArrayList]::new()

foreach ($lineNum in ($suggestions.Keys | Sort-Object { [int]$_ })) {
    $idx = [int]$lineNum - 1
    if ($idx -lt 0 -or $idx -ge $originalLines.Count) { continue }

    $origLine = $originalLines[$idx]
    $suggList = $suggestions[$lineNum]

    # 既に simp only なら飛ばす
    if ($origLine -match '\bsimp(_all)?\s+only\b') { continue }

    # チェーン行: 複数提案の補題を和集合でマージ
    if ($suggList.Count -gt 1) {
        $allLemmas = [System.Collections.Generic.HashSet[string]]::new()
        $baseCmd = ""
        foreach ($sugg in $suggList) {
            if ($sugg -match '(simp(?:_all)?\s+only)\s*\[([^\]]*)\]') {
                if (-not $baseCmd) { $baseCmd = $Matches[1] }
                $lemmas = $Matches[2] -split ',' | ForEach-Object { $_.Trim() } | Where-Object { $_ }
                foreach ($l in $lemmas) { $null = $allLemmas.Add($l) }
            }
        }
        if ($baseCmd -and $allLemmas.Count -gt 0) {
            $merged = $allLemmas -join ", "
            $replacement = "$baseCmd [$merged]"

            # at ターゲットの保持
            if ($origLine -match '\bat\s+(\w[\w''_]*)') {
                $replacement += " at $($Matches[1])"
            }

            # インデント保持
            $indent = ""
            if ($origLine -match '^(\s+)') { $indent = $Matches[1] }

            # <;> プレフィックスの保持
            $prefix = ""
            if ($origLine -match '(<;>\s*)') { $prefix = $Matches[1] }

            $originalLines[$idx] = "$indent$prefix$replacement"
            $appliedCount++
            continue
        }
    }

    # 単一提案
    $sugg = $suggList[0]

    # ネスト括弧のチェック（手動修正が必要）
    if ($origLine -match 'simp\s*\[.*show\s.*from\s.*by\b') {
        $null = $skippedLines.Add("L${lineNum}: ネスト括弧パターン")
        $skippedCount++
        continue
    }

    # at ターゲットの保持
    if ($origLine -match '\bat\s+(\w[\w''_]*)' -and $sugg -notmatch '\bat\s') {
        $sugg += " at $($Matches[1])"
    }

    # インデント保持
    $indent = ""
    if ($origLine -match '^(\s+)') { $indent = $Matches[1] }

    # <;> プレフィックスの保持
    $prefix = ""
    if ($origLine -match '(<;>\s*)') { $prefix = $Matches[1] }

    $originalLines[$idx] = "$indent$prefix$sugg"
    $appliedCount++
}

Write-Info "適用: $appliedCount 件, スキップ: $skippedCount 件"

if ($skippedLines.Count -gt 0) {
    Write-Warn "以下の行は手動修正が必要です:"
    foreach ($sl in $skippedLines) {
        Write-Warn "  $sl"
    }
}

# --- Step 6: 結果書き出し ---

$resultContent = $originalLines -join "`n"
[System.IO.File]::WriteAllText($absFile, $resultContent, (New-Object System.Text.UTF8Encoding $false))

Write-Ok "安定化完了: $appliedCount / $convertCount 件"

# --- Step 7: クリーンアップ ---

if (-not $KeepBackup) {
    Remove-Item $bakFile -ErrorAction SilentlyContinue
    Write-Info "バックアップ削除"
} else {
    Write-Info "バックアップ保持: $bakFile"
}

Write-Info "次のステップ: lake build で検証してください"
Write-Info "unused simp argument 警告がある場合は手動で除去してください"
