#!/usr/bin/env pwsh
# Stop Hook: セッション終了時のインデックス自動再生成（M7）
#
# S2IL のビルドが成功している場合に限り、以下のインデックスを自動再生成する:
#   - S2IL/_agent/symbol-map.jsonl（シンボル位置 DB）
#   - S2IL/_agent/dep-graph-baseline.json（依存グラフベースライン）
#
# 入力 (stdin JSON): { "hookEventName": "Stop", "cwd": "...", ... }
# 出力 (stdout JSON): { "continue": true } or { "continue": true, "systemMessage": "..." }

[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

try {
    $rawInput = [Console]::In.ReadToEnd()
    $inputJson = $rawInput | ConvertFrom-Json
    $cwd = $inputJson.cwd
    if (-not $cwd) { $cwd = Get-Location }

    # stop_hook_active ガード
    if ($inputJson.PSObject.Properties["stop_hook_active"] -and $inputJson.stop_hook_active -eq $true) {
        @{ continue = $true } | ConvertTo-Json -Compress
        exit 0
    }

    Push-Location $cwd

    # ======================================================================
    # 0. ビルド成功チェック（errors = 0 のセッション内ビルドが必要）
    # ======================================================================
    $diagFile = $null
    $sessionIdFile = Join-Path $cwd ".lake/session-id.tmp"
    if (Test-Path $sessionIdFile) {
        $sessionId = (Get-Content $sessionIdFile -Raw).Trim()
        if ($sessionId) {
            $candidate = Join-Path $cwd ".lake/build-diagnostics-$sessionId.jsonl"
            if (Test-Path $candidate) { $diagFile = $candidate }
        }
    }

    if (-not $diagFile) {
        # このセッションでビルドが実行されていない → スキップ
        @{ continue = $true } | ConvertTo-Json -Compress
        exit 0
    }

    # エラーがあればスキップ（toolkit のビルドも失敗する可能性大）
    $hasErrors = Get-Content $diagFile |
        Where-Object { $_.Trim() } |
        ForEach-Object { ($_ | ConvertFrom-Json -ErrorAction SilentlyContinue) } |
        Where-Object { $_.severity -eq "error" } |
        Measure-Object
    if ($hasErrors.Count -gt 0) {
        @{ continue = $true } | ConvertTo-Json -Compress
        exit 0
    }

    # ======================================================================
    # 1. .lean ファイルの変更検出（git diff でチェック）
    # ======================================================================
    $leanChanged = $false
    try {
        # staged + unstaged + untracked の .lean ファイル変更を検出
        $diffFiles = @(git diff --name-only HEAD 2>$null) +
                     @(git diff --name-only --cached 2>$null) +
                     @(git ls-files --others --exclude-standard '*.lean' 2>$null)
        $leanChanged = ($diffFiles | Where-Object { $_ -match '\.lean$' } | Measure-Object).Count -gt 0
    } catch {
        # git コマンド失敗時はスキップ
    }

    # コミット済み変更の検出: symbol-map.jsonl より新しい .lean ファイルがあれば再生成
    # （セッション中に git commit した場合、git diff HEAD は空になるため上記では検出できない）
    if (-not $leanChanged) {
        try {
            $symbolMapPath = Join-Path $cwd "S2IL/_agent/symbol-map.jsonl"
            $symbolMapTime = if (Test-Path $symbolMapPath) {
                (Get-Item $symbolMapPath).LastWriteTimeUtc
            } else {
                [datetime]::MinValue
            }
            $newerLean = Get-ChildItem (Join-Path $cwd "S2IL") -Recurse -Filter "*.lean" -ErrorAction SilentlyContinue |
                Where-Object { $_.LastWriteTimeUtc -gt $symbolMapTime }
            $leanChanged = ($newerLean | Measure-Object).Count -gt 0
        } catch { }
    }

    if (-not $leanChanged) {
        @{ continue = $true } | ConvertTo-Json -Compress
        exit 0
    }

    # ======================================================================
    # 2. インデックス再生成
    # ======================================================================
    $env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
    $regenerated = @()
    $errors = @()

    # symbol-map.jsonl（update-symbol-map.ps1 を使用して line/sig を含む PS1 フォーマットで生成）
    try {
        $updateScript = Join-Path $cwd ".github/skills/lean-build/scripts/update-symbol-map.ps1"
        & $updateScript -Root $cwd
        if ($LASTEXITCODE -eq 0) {
            $regenerated += "symbol-map.jsonl"
        } else {
            $errors += "symbol-map: exit $LASTEXITCODE"
        }
    } catch {
        $errors += "symbol-map: $($_.Exception.Message)"
    }

    # dep-graph-baseline.json
    $depGraphPath = Join-Path $cwd "S2IL/_agent/dep-graph-baseline.json"
    try {
        $result = lake exe s2il-toolkit depgraph --json --output $depGraphPath 2>&1
        if ($LASTEXITCODE -eq 0) {
            $regenerated += "dep-graph-baseline.json"
        } else {
            $errors += "dep-graph: exit $LASTEXITCODE"
        }
    } catch {
        $errors += "dep-graph: $($_.Exception.Message)"
    }

    # ======================================================================
    # 3. 再生成されたファイルを git add
    # ======================================================================
    if ($regenerated.Count -gt 0) {
        try {
            if ($regenerated -contains "symbol-map.jsonl") {
                git add $symbolMapPath 2>$null
            }
            if ($regenerated -contains "dep-graph-baseline.json") {
                git add $depGraphPath 2>$null
            }
        } catch { }
    }

    Pop-Location

    # ======================================================================
    # 4. 結果を systemMessage で通知
    # ======================================================================
    if ($regenerated.Count -gt 0 -or $errors.Count -gt 0) {
        $parts = @()
        if ($regenerated.Count -gt 0) {
            $parts += "[M7] Regenerated: $($regenerated -join ', ')"
        }
        if ($errors.Count -gt 0) {
            $parts += "[M7] Failed: $($errors -join '; ')"
        }
        @{
            continue      = $true
            systemMessage = ($parts -join "`n")
        } | ConvertTo-Json -Compress
    } else {
        @{ continue = $true } | ConvertTo-Json -Compress
    }
    exit 0
}
catch {
    @{ continue = $true } | ConvertTo-Json -Compress
    exit 0
}
