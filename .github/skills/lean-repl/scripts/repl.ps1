# Lean REPL 起動スクリプト (Windows / PowerShell)
#
# 使い方:
#   .github/skills/lean-repl/scripts/repl.ps1 [-InputFile <path>] [-RebuildPickle] [-NoPickle]
#
# -InputFile モード（エージェント向け）:
#   stdout には REPL の JSON 応答行のみを出力する。
#   ステータスメッセージは Write-Host (stderr) に出力。
#   終了コード: 0=正常, 1=REPL応答にエラーあり, 2=REPLクラッシュ
#
# デフォルト動作: 'import S2IL' + 'import Mathlib.Tactic' を自動プレペンドし env:0 を提供する。
# これにより ring, linarith, exact?, simp?, funext 等すべての Mathlib タクティクが利用可能。
# 起動に約 16-20 秒かかる（Mathlib .olean 読み込みは初回のみ長め、以降はキャッシュ利用で高速化）。
#
# -NoPickle: 自動プレペンドを行わない。ユーザーが JSONL 内で import や unpickle を管理する。
# -RebuildPickle: pickle ファイルを再生成する（カスタムセッション保存用途）。
# pickle ファイルは .repl/s2il.olean に保存される。

param(
    [string]$InputFile = "",
    [switch]$RebuildPickle,
    [switch]$NoPickle
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

# --- パス解決 ---
$repoRoot = (git -C $PSScriptRoot rev-parse --show-toplevel 2>$null) ?? (Resolve-Path "$PSScriptRoot/../../../").Path
$replDir  = Join-Path $repoRoot ".repl"
$picklePath = Join-Path $replDir "s2il.olean"

# elan/lake を PATH に追加
$elanBin = Join-Path $env:USERPROFILE ".elan\bin"
if (Test-Path $elanBin) {
    $env:PATH = "$elanBin;$env:PATH"
}

Push-Location $repoRoot

# --- REPL バイナリの確認 ---
function Test-ReplBin {
    $bin = Join-Path $repoRoot ".lake\build\bin\repl.exe"
    return Test-Path $bin
}

# --- pickle の有効性チェック（JSON パースで確認）---
function Test-PickleValid([string]$path) {
    if (-not (Test-Path $path)) { return $false }
    # unpickle して env 番号が返ってくるか確認
    $testCmd = '{"unpickleEnvFrom": "' + ($path -replace '\\', '/') + '"}'
    try {
        $out = $testCmd | lake exe repl 2>&1
        $json = $out | Where-Object { $_ -match '^\{' } | Select-Object -First 1
        if ($null -eq $json) { return $false }
        $parsed = $json | ConvertFrom-Json -ErrorAction Stop
        return $null -ne $parsed.env
    } catch {
        return $false
    }
}

# --- pickle 生成 ---
function Build-Pickle {
    param([string]$path)

    Write-Host "=== Lean REPL: pickle を生成中... ===" -ForegroundColor Cyan
    New-Item -ItemType Directory -Force -Path (Split-Path $path) | Out-Null

    # S2IL + Mathlib.Tactic をインポートして pickle を保存
    $importCmd  = '{"cmd": "import S2IL\nimport Mathlib.Tactic"}'
    $pickleCmd  = '{"pickleTo": "' + ($path -replace '\\', '/') + '", "env": 0}'
    $commands   = "$importCmd`n`n$pickleCmd"

    try {
        $out = $commands | lake exe repl 2>&1
        # エラーがないか確認
        # ※ pickleTo の応答は {"env": N} のみで messages フィールドを持たない。
        #   Set-StrictMode -Version Latest 環境では存在しないプロパティアクセスが例外になるため
        #   PSObject.Properties で存在確認してからアクセスする。
        $lines = $out | Where-Object { $_ -match '^\{' }
        foreach ($line in $lines) {
            $obj = $line | ConvertFrom-Json -ErrorAction SilentlyContinue
            $msgProp = $obj.PSObject.Properties['messages']
            if ($msgProp) {
                $errs = $msgProp.Value | Where-Object { $_.severity -eq "error" }
                if ($errs) {
                    Write-Error "pickle 生成中にエラーが発生しました:`n$($errs | ConvertTo-Json -Depth 5)"
                    return $false
                }
            }
        }
        if (Test-Path $path) {
            Write-Host "=== pickle 生成完了: $path ===" -ForegroundColor Green
            return $true
        } else {
            Write-Error "pickle ファイルが見つかりません: $path"
            return $false
        }
    } catch {
        Write-Error "pickle 生成に失敗しました: $_"
        return $false
    }
}

# --- デフォルト起動コマンド（import ベース）---
# S2IL + Mathlib.Tactic をインポートして env:0 を提供する。
# すべての Mathlib タクティク（ring, linarith, exact?, funext 等）が利用可能になる。
function Get-InitCmd {
    return '{"cmd": "import S2IL\nimport Mathlib.Tactic"}'
}

# --- メイン処理 ---

# REPL バイナリが未ビルドならビルド（初回・lake clean 後などに必要。正常フロー）
if (-not (Test-ReplBin)) {
    Write-Host "=== Lean REPL: バイナリをビルド中（初回・clean 後は自動ビルドします）... ===" -ForegroundColor Cyan
    lake build repl
    if ($LASTEXITCODE -ne 0) {
        Pop-Location
        exit 1
    }
}

# -RebuildPickle: pickle ファイルを再生成して終了（他フラグとの組み合わせ時は再生成後に継続）
if ($RebuildPickle) {
    $ok = Build-Pickle -path $picklePath
    if (-not $ok) {
        Pop-Location
        exit 1
    }
    if ($InputFile -eq "") {
        Write-Host "=== pickle 再生成完了 ===" -ForegroundColor Green
        Pop-Location
        exit 0
    }
    # InputFile が指定されている場合は pickle 再生成後に通常実行を続ける
}

# --- バッチ出力処理 ---
# REPL は JSON をプリティプリント（複数行）で出力する。
# 空行区切りで各 JSON 応答を結合し、1 行 JSON として stdout に出力する。
# 戻り値: @{ jsonCount: Int; hasError: Bool }
function Write-ReplOutput {
    param([object[]]$RawLines, [string]$Stderr)

    $jsonCount = 0
    $hasError = $false

    # 行配列を文字列に結合して空行区切りで分割
    $allText = ($RawLines | ForEach-Object { "$_" }) -join "`n"
    $chunks = $allText -split '\n\s*\n'

    foreach ($chunk in $chunks) {
        $trimmed = $chunk.Trim()
        if ($trimmed -eq "" -or $trimmed[0] -ne '{') { continue }

        # 1 行に圧縮して stdout に直接出力（Write-Output ではなく Console で関数戻り値と分離）
        try {
            $parsed = $trimmed | ConvertFrom-Json -ErrorAction Stop
            $oneLine = $parsed | ConvertTo-Json -Compress -Depth 20
            [Console]::WriteLine($oneLine)
            $jsonCount++

            # エラー検出
            $msgProp = $parsed.PSObject.Properties['messages']
            if ($msgProp) {
                $errs = @($msgProp.Value | Where-Object { $_.severity -eq "error" })
                if ($errs.Count -gt 0) { $hasError = $true }
            }
        } catch {
            # JSON パース失敗 → そのまま通す（デバッグ用）
            [Console]::WriteLine($trimmed)
            $jsonCount++
        }
    }

    return @{ jsonCount = $jsonCount; hasError = $hasError }
}

# --- 入力の準備 ---
# 注意: パラメータ名を $InputFile にしている。$Input/$input は PowerShell 自動変数と衝突するため使用禁止。
$userInput = $null
if ($InputFile -ne "" -and (Test-Path $InputFile)) {
    $userInput = Get-Content $InputFile -Raw
}

# --- REPL 実行 ---
# クラッシュ検出共通処理
function Invoke-ReplWithCrashDetect {
    param([string]$FullInput)

    $inputCmdCount = ($FullInput -split '\r?\n' | Where-Object { $_ -match '^\s*\{' }).Count

    $stderrFile = [System.IO.Path]::GetTempFileName()
    try {
        $rawOutput = $FullInput | lake exe repl 2>$stderrFile
    } catch {
        $rawOutput = @()
    }
    $stderrContent = if (Test-Path $stderrFile) {
        Get-Content $stderrFile -Raw -ErrorAction SilentlyContinue
    } else { "" }
    Remove-Item $stderrFile -Force -ErrorAction SilentlyContinue

    $result = Write-ReplOutput -RawLines $rawOutput -Stderr $stderrContent

    # クラッシュ検出: 応答数 < 入力コマンド数
    if ($result.jsonCount -lt $inputCmdCount) {
        $missing = $inputCmdCount - $result.jsonCount
        $crashMsg = "REPL process terminated unexpectedly. $missing command(s) were not processed."
        if ($stderrContent) {
            $lastStderr = ($stderrContent -split '\r?\n' | Where-Object { $_.Trim() -ne "" } | Select-Object -Last 1)
            if ($lastStderr) { $crashMsg += " stderr: $lastStderr" }
        }
        $crashJson = @{ error = "repl_crashed"; message = $crashMsg; commands_sent = $inputCmdCount; responses_received = $result.jsonCount } | ConvertTo-Json -Compress
        [Console]::WriteLine($crashJson)
        Pop-Location
        exit 2
    }

    return $result
}

if (-not $NoPickle) {
    # --- デフォルトモード: import S2IL + Mathlib.Tactic を自動プレペンド ---
    # ring, linarith, exact?, funext 等すべての Mathlib タクティクが env:0 で利用可能。
    $initCmd = Get-InitCmd

    if ($null -ne $userInput) {
        # ユーザー JSONL がすでに `import` コマンドで始まっている場合は重複プレペンドしない
        $alreadyHasImport = $userInput -match '"cmd"\s*:\s*"import '
        $fullInput = if ($alreadyHasImport) { $userInput } else { "$initCmd`n`n$userInput" }

        $result = Invoke-ReplWithCrashDetect -FullInput $fullInput

        Pop-Location
        if ($result.hasError) { exit 1 } else { exit 0 }
    } else {
        # インタラクティブモード
        Write-Host "=== Lean REPL 起動（import S2IL + Mathlib.Tactic） ===" -ForegroundColor Cyan
        Write-Host "JSON Lines 形式でコマンドを入力（Ctrl+D で終了）" -ForegroundColor Gray
        Write-Host "起動後に import が完了するまで約 16-20 秒かかります。" -ForegroundColor Gray
        lake exe repl
        Pop-Location
    }
} else {
    # -NoPickle モード: 自動プレペンドなし（ユーザーが JSONL 内で import/unpickle を管理）
    if ($null -ne $userInput) {
        $result = Invoke-ReplWithCrashDetect -FullInput $userInput

        Pop-Location
        if ($result.hasError) { exit 1 } else { exit 0 }
    } else {
        Write-Host "=== Lean REPL 起動（NoPickle: 自動プレペンドなし） ===" -ForegroundColor Cyan
        lake exe repl
        Pop-Location
    }
}
