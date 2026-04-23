# Lean REPL 起動スクリプト (Windows / PowerShell)
#
# 使い方:
#   .github/skills/lean-repl/scripts/repl.ps1 [-InputFile <path>] [-RebuildPickle] [-NoPickle]
#
# Persistent mode（デーモン常駐）:
#   repl.ps1 -Start -SessionId <id>                     セッション開始（import 完了まで待機）
#   repl.ps1 -Send  -SessionId <id> -CmdFile <path>     コマンド送信（応答を stdout に出力）
#   repl.ps1 -Send  -SessionId <id> -Cmd '<json>'        単一コマンド送信
#   repl.ps1 -Stop  -SessionId <id>                     セッション停止
#
# -InputFile モード（エージェント向け）:
#   stdout には REPL の JSON 応答行のみを出力する。
#   ステータスメッセージは Write-Host (stderr) に出力。
#   終了コード: 0=正常, 1=REPL応答にエラーあり, 2=REPLクラッシュ
#
# デフォルト動作: 'import S2IL' + 'import Mathlib.Tactic' + 'import Plausible' + 'import Duper' を先頭に自動挿入し env:0 を提供する。
# これにより ring, linarith, exact?, simp?, funext 等すべての Mathlib タクティク、plausible、duper が利用可能。
# 起動に約 16-20 秒かかる（Mathlib .olean 読み込みは初回のみ長め、以降はキャッシュ利用で高速化）。
#
# -NoPickle: 先頭への自動挿入を行わない。ユーザーが JSONL 内で import や unpickle を管理する。
# -RebuildPickle: pickle ファイルを再生成する（カスタムセッション保存用途）。
# pickle ファイルは .repl/s2il.olean に保存される。

param(
    # Persistent mode
    [switch]$Start,
    [switch]$Send,
    [switch]$Stop,
    [string]$SessionId = "",
    [string]$Cmd = "",
    [string]$CmdFile = "",

    # Legacy batch mode
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

# ============================================================
#  関数定義
# ============================================================

# --- REPL バイナリの確認 ---
function Test-ReplBin {
    $bin = Join-Path $repoRoot ".lake\packages\repl\.lake\build\bin\repl.exe"
    return Test-Path $bin
}

# --- pickle 生成 ---
function Build-Pickle {
    param([string]$path)

    Write-Host "=== Lean REPL: pickle を生成中... ===" -ForegroundColor Cyan
    New-Item -ItemType Directory -Force -Path (Split-Path $path) | Out-Null

    # S2IL + Mathlib.Tactic + Plausible + Duper をインポートして pickle を保存
    $importCmd  = '{"cmd": "import S2IL\nimport Mathlib.Tactic\nimport Plausible\nimport Duper"}'
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
# S2IL + Mathlib.Tactic + Plausible + Duper をインポートして env:0 を提供する。
# すべての Mathlib タクティク（ring, linarith, exact?, funext 等）、plausible、duper が利用可能になる。
function Get-InitCmd {
    return '{"cmd": "import S2IL\nimport Mathlib.Tactic\nimport Plausible\nimport Duper"}'
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
            # タクティクモードエラー検出（"message" フィールド = tactic 失敗・Unknown proof state）
            $tacMsgProp = $parsed.PSObject.Properties['message']
            if ($tacMsgProp -and $tacMsgProp.Value) { $hasError = $true }
        } catch {
            # JSON パース失敗 → そのまま通す（デバッグ用）
            [Console]::WriteLine($trimmed)
            $jsonCount++
        }
    }

    return @{ jsonCount = $jsonCount; hasError = $hasError }
}

# --- REPL 実行 ---
# パイプ方式 + エンコーディング制御による UTF-8 安全な REPL 呼び出し
# $OutputEncoding: PowerShell → 外部プロセスの stdin パイプエンコーディング
# [Console]::OutputEncoding: 外部プロセスの stdout → PowerShell のデコードエンコーディング
function Invoke-ReplWithCrashDetect {
    param([string]$FullInput, [bool]$HasImport = $true)

    $inputCmdCount = @($FullInput -split '\r?\n' | Where-Object { $_ -match '^\s*\{' }).Count

    # lake の絶対パスを解決
    $lakeBin = Get-Command lake -ErrorAction SilentlyContinue | Select-Object -ExpandProperty Source
    if (-not $lakeBin) { $lakeBin = "lake" }

    if ($HasImport) {
        Write-Host "=== Lean REPL: import 処理中（~15s）... ===" -ForegroundColor Cyan
    } else {
        Write-Host "=== Lean REPL: 処理中... ===" -ForegroundColor Cyan
    }

    # UTF-8 BOM なしエンコーディングを設定（pipe/stdout 両方）
    $prevOutputEncoding = $OutputEncoding
    $prevConsoleOutputEncoding = [Console]::OutputEncoding
    $OutputEncoding = [System.Text.UTF8Encoding]::new($false)
    [Console]::OutputEncoding = [System.Text.UTF8Encoding]::new($false)

    # 並列実行安全: プロセス固有の一時ファイルに stderr をリダイレクト
    $stderrFile = [System.IO.Path]::GetTempFileName()

    try {
        $rawOutput = $FullInput | & $lakeBin exe repl 2>$stderrFile

        # stderr: BOM 自動検出で読み取り（PS5=UTF-16LE, PS7=UTF-8 いずれも対応）
        $stderrContent = if (Test-Path $stderrFile) {
            [System.IO.File]::ReadAllText($stderrFile)
        } else { "" }

        Remove-Item $stderrFile -Force -ErrorAction SilentlyContinue
        $stderrFile = $null

        Write-Host "=== Lean REPL: 完了 ===" -ForegroundColor Green

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
    } finally {
        $OutputEncoding = $prevOutputEncoding
        [Console]::OutputEncoding = $prevConsoleOutputEncoding
        if ($stderrFile) { Remove-Item $stderrFile -Force -ErrorAction SilentlyContinue }
    }
}

# --- olean ハッシュ（ビルド陳腐化検出）---
function Get-OleanHash {
    $oleanDir = Join-Path $repoRoot ".lake" "build" "lib" "lean" "S2IL"
    if (-not (Test-Path $oleanDir)) { return "none" }
    $files = Get-ChildItem $oleanDir -Recurse -Filter "*.olean"
    if (-not $files -or $files.Count -eq 0) { return "none" }
    $combined = ($files | Sort-Object FullName | ForEach-Object {
        "$($_.FullName):$($_.LastWriteTimeUtc.Ticks)"
    }) -join "|"
    $bytes = [System.Text.Encoding]::UTF8.GetBytes($combined)
    $hash = [System.Security.Cryptography.SHA256]::Create().ComputeHash($bytes)
    return ($hash | ForEach-Object { $_.ToString("x2") }) -join ""
}

# ============================================================
#  メイン処理
# ============================================================

# --- Persistent REPL mode ---
if ($Start -or $Send -or $Stop) {
    if ($SessionId -eq "") {
        Write-Host "Error: -SessionId is required for persistent mode" -ForegroundColor Red
        Pop-Location; exit 1
    }

    $sessionDir = Join-Path $replDir $SessionId

    # --- Start session ---
    function Start-ReplSession {
        if (Test-Path (Join-Path $sessionDir "ready")) {
            $pidFile = Join-Path $sessionDir "daemon.pid"
            if (Test-Path $pidFile) {
                $daemonPid = [int][IO.File]::ReadAllText($pidFile).Trim()
                $proc = Get-Process -Id $daemonPid -ErrorAction SilentlyContinue
                if ($proc) {
                    Write-Host "Session '$SessionId' is already running (PID: $daemonPid)" -ForegroundColor Yellow
                    return $true
                }
            }
            # ステートが古い → クリーンアップ
            Remove-Item $sessionDir -Recurse -Force -ErrorAction SilentlyContinue
        }

        # REPL バイナリ確認
        if (-not (Test-ReplBin)) {
            Write-Host "REPL binary not found, building..." -ForegroundColor Cyan
            lake build repl
            if ($LASTEXITCODE -ne 0) { return $false }
        }

        # セッションディレクトリ作成
        New-Item -ItemType Directory -Force -Path $sessionDir | Out-Null

        # olean ハッシュ保存
        $hash = Get-OleanHash
        [IO.File]::WriteAllText((Join-Path $sessionDir "olean.hash"), $hash)

        # デーモンプロセス起動
        $daemonScript = Join-Path $PSScriptRoot "repl-daemon.ps1"
        $pwshPath = (Get-Process -Id $PID).Path
        $psi = [System.Diagnostics.ProcessStartInfo]::new()
        $psi.FileName = $pwshPath
        $psi.Arguments = "-NoProfile -ExecutionPolicy Bypass -File `"$daemonScript`" -SessionId `"$SessionId`" -RepoRoot `"$repoRoot`""
        $psi.CreateNoWindow = $true
        $psi.UseShellExecute = $false
        $daemonProc = [System.Diagnostics.Process]::Start($psi)

        Write-Host "=== Persistent REPL: デーモン起動中 (PID: $($daemonProc.Id))... ===" -ForegroundColor Cyan

        # ready シグナル待機（import 完了まで最大 120s）
        $sw = [System.Diagnostics.Stopwatch]::StartNew()
        $readyFile = Join-Path $sessionDir "ready"
        $errorFile = Join-Path $sessionDir "error"
        while ($sw.ElapsedMilliseconds -lt 120000) {
            if (Test-Path $readyFile) {
                Write-Host "=== Persistent REPL: セッション '$SessionId' 準備完了 ===" -ForegroundColor Green
                return $true
            }
            if (Test-Path $errorFile) {
                $errMsg = [IO.File]::ReadAllText($errorFile).Trim()
                Write-Host "Error: Daemon failed: $errMsg" -ForegroundColor Red
                Remove-Item $sessionDir -Recurse -Force -ErrorAction SilentlyContinue
                return $false
            }
            if ($daemonProc.HasExited) {
                Write-Host "Error: Daemon exited unexpectedly (code: $($daemonProc.ExitCode))" -ForegroundColor Red
                Remove-Item $sessionDir -Recurse -Force -ErrorAction SilentlyContinue
                return $false
            }
            [System.Threading.Thread]::Sleep(500)
        }

        Write-Host "Error: Daemon startup timed out (120s)" -ForegroundColor Red
        if (-not $daemonProc.HasExited) { try { $daemonProc.Kill() } catch {} }
        Remove-Item $sessionDir -Recurse -Force -ErrorAction SilentlyContinue
        return $false
    }

    # --- Stop session ---
    function Stop-ReplSession {
        if (-not (Test-Path $sessionDir)) { return $false }

        # Shutdown シグナル
        [IO.File]::WriteAllText((Join-Path $sessionDir "shutdown"), "stop")

        # デーモン終了待機（最大 5s）
        $pidFile = Join-Path $sessionDir "daemon.pid"
        if (Test-Path $pidFile) {
            $daemonPid = [int][IO.File]::ReadAllText($pidFile).Trim()
            $sw = [System.Diagnostics.Stopwatch]::StartNew()
            while ($sw.ElapsedMilliseconds -lt 5000) {
                $proc = Get-Process -Id $daemonPid -ErrorAction SilentlyContinue
                if (-not $proc) { break }
                [System.Threading.Thread]::Sleep(200)
            }
            $proc = Get-Process -Id $daemonPid -ErrorAction SilentlyContinue
            if ($proc) { try { $proc.Kill() } catch {} }
        }

        # REPL プロセスも確実に停止
        $replPidFile = Join-Path $sessionDir "repl.pid"
        if (Test-Path $replPidFile) {
            $replPid = [int][IO.File]::ReadAllText($replPidFile).Trim()
            $proc = Get-Process -Id $replPid -ErrorAction SilentlyContinue
            if ($proc) { try { $proc.Kill() } catch {} }
        }

        Remove-Item $sessionDir -Recurse -Force -ErrorAction SilentlyContinue
        return $true
    }

    # --- Daemon alive check ---
    function Test-DaemonAlive {
        $pidFile = Join-Path $sessionDir "daemon.pid"
        if (-not (Test-Path $pidFile)) { return $false }
        $daemonPid = [int][IO.File]::ReadAllText($pidFile).Trim()
        $proc = Get-Process -Id $daemonPid -ErrorAction SilentlyContinue
        return ($null -ne $proc)
    }

    # --- Olean staleness check ---
    function Test-OleanStale {
        $hashFile = Join-Path $sessionDir "olean.hash"
        if (-not (Test-Path $hashFile)) { return $true }
        $savedHash = [IO.File]::ReadAllText($hashFile).Trim()
        $currentHash = Get-OleanHash
        return ($savedHash -ne $currentHash)
    }

    # === Mode dispatch ===
    if ($Start) {
        $ok = Start-ReplSession
        Pop-Location
        if ($ok) { exit 0 } else { exit 1 }
    }
    elseif ($Stop) {
        $wasStopped = Stop-ReplSession
        if ($wasStopped) {
            Write-Host "=== Persistent REPL: セッション '$SessionId' を停止しました ===" -ForegroundColor Green
        } else {
            Write-Host "=== Persistent REPL: セッション '$SessionId' は起動されていません ===" -ForegroundColor Yellow
        }
        Pop-Location; exit 0
    }
    elseif ($Send) {
        if ($Cmd -eq "" -and $CmdFile -eq "") {
            Write-Host "Error: -Cmd or -CmdFile is required for -Send" -ForegroundColor Red
            Pop-Location; exit 1
        }

        # -Cmd と -CmdFile の同時指定時に警告
        if ($Cmd -ne "" -and $CmdFile -ne "") {
            Write-Host "警告: -Cmd と -CmdFile が同時に指定されました。-CmdFile が優先されます。" -ForegroundColor Yellow
        }

        # コマンド内容の準備（Lazy Start の前にバリデーションして無駄な起動を回避）
        $cmdContent = ""
        if ($CmdFile -ne "") {
            if (-not (Test-Path $CmdFile)) {
                Write-Host "Error: CmdFile not found: $CmdFile" -ForegroundColor Red
                Pop-Location; exit 1
            }
            $cmdContent = [IO.File]::ReadAllText(
                [IO.Path]::GetFullPath($CmdFile),
                [System.Text.Encoding]::UTF8).Trim()
        } else {
            $cmdContent = $Cmd.Trim()
            # -Cmd の JSON 構文チェック（不正 JSON による REPL クラッシュを防ぐ）
            # ConvertFrom-Json は無効 JSON に対して terminating error を投げるため try/catch で捕捉する
            if ($cmdContent -ne "") {
                $cmdLines = @($cmdContent -split '\r?\n' | Where-Object { $_.Trim() -ne '' })
                $invalidLines = @($cmdLines | Where-Object {
                    $l = $_.Trim()
                    if ($l -notmatch '^\{') { return $true }
                    try { $null = $l | ConvertFrom-Json -ErrorAction Stop; return $false }
                    catch { return $true }
                })
                if ($invalidLines.Count -gt 0) {
                    Write-Host "Error: -Cmd の内容が有効な JSON ではありません:" -ForegroundColor Red
                    $invalidLines | ForEach-Object { Write-Host "  $_" -ForegroundColor Red }
                    Pop-Location; exit 1
                }
            }
        }

        if ($cmdContent -eq "") {
            Write-Host "Error: Empty command" -ForegroundColor Red
            Pop-Location; exit 1
        }

        # Lazy start: デーモンが起動していなければ自動起動
        if (-not (Test-DaemonAlive)) {
            Write-Host "Daemon not running, starting..." -ForegroundColor Yellow
            $ok = Start-ReplSession
            if (-not $ok) { Pop-Location; exit 1 }
        }

        # Olean staleness: ビルド後は再起動
        if (Test-OleanStale) {
            Write-Host "olean files changed, restarting session..." -ForegroundColor Yellow
            Stop-ReplSession
            $ok = Start-ReplSession
            if (-not $ok) { Pop-Location; exit 1 }
        }

        # 古い応答シグナルをクリーンアップ
        $responseDone = Join-Path $sessionDir "response.ready"
        $responseFile = Join-Path $sessionDir "response.json"
        Remove-Item $responseDone -Force -ErrorAction SilentlyContinue
        Remove-Item $responseFile -Force -ErrorAction SilentlyContinue

        # リクエスト送信（アトミック書き込み: tmp → move）
        $requestFile = Join-Path $sessionDir "request.json"
        $tempFile = "$requestFile.tmp"
        [IO.File]::WriteAllText($tempFile, $cmdContent, [System.Text.Encoding]::UTF8)
        [IO.File]::Move($tempFile, $requestFile)

        # 応答待機
        $sw = [System.Diagnostics.Stopwatch]::StartNew()
        $timeoutMs = 180000  # 3 分（重いタクティク対応）
        while ($sw.ElapsedMilliseconds -lt $timeoutMs) {
            if (Test-Path $responseDone) {
                if (Test-Path $responseFile) {
                    $response = [IO.File]::ReadAllText($responseFile, [System.Text.Encoding]::UTF8).Trim()

                    # UTF-8 BOM なしエンコーディングを設定（出力時の文字化け防止）
                    $prevConsoleEnc = [Console]::OutputEncoding
                    [Console]::OutputEncoding = [System.Text.UTF8Encoding]::new($false)

                    # 各行を stdout に出力
                    $hasError = $false
                    foreach ($line in ($response -split '\r?\n')) {
                        if ($line.Trim() -eq "") { continue }
                        [Console]::WriteLine($line)
                        try {
                            $parsed = $line | ConvertFrom-Json -ErrorAction Stop
                            $msgProp = $parsed.PSObject.Properties['messages']
                            if ($msgProp) {
                                $errs = @($msgProp.Value | Where-Object { $_.severity -eq "error" })
                                if ($errs.Count -gt 0) { $hasError = $true }
                            }
                            $errProp = $parsed.PSObject.Properties['error']
                            if ($errProp) { $hasError = $true }
                            # タクティクモードエラー検出（"message" フィールド = tactic 失敗・Unknown proof state）
                            $tacMsgProp = $parsed.PSObject.Properties['message']
                            if ($tacMsgProp -and $tacMsgProp.Value) { $hasError = $true }
                        } catch {}
                    }

                    Remove-Item $responseDone -Force -ErrorAction SilentlyContinue
                    Remove-Item $responseFile -Force -ErrorAction SilentlyContinue

                    [Console]::OutputEncoding = $prevConsoleEnc
                    Pop-Location
                    if ($hasError) { exit 1 } else { exit 0 }
                }
            }

            # デーモン生存確認
            if (-not (Test-DaemonAlive)) {
                Write-Host "Error: Daemon died while waiting for response" -ForegroundColor Red
                Pop-Location; exit 2
            }

            [System.Threading.Thread]::Sleep(30)
        }

        Write-Host "Error: Response timed out (${timeoutMs}ms)" -ForegroundColor Red
        Pop-Location; exit 2
    }
}

# --- Legacy batch mode ---

# REPL バイナリが未ビルドならビルド（初回・lake clean 後などに必要。正常フロー）
if (-not (Test-ReplBin)) {
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

# --- 入力の準備 ---
# 注意: パラメータ名を $InputFile にしている。$Input/$input は PowerShell 自動変数と衝突するため使用禁止。
$userInput = $null
if ($InputFile -ne "" -and -not (Test-Path $InputFile)) {
    Write-Host "エラー: InputFile が見つかりません: $InputFile" -ForegroundColor Red
    Pop-Location
    exit 1
}
if ($InputFile -ne "" -and (Test-Path $InputFile)) {
    # .NET API で UTF-8 読み取り（BOM 有無に関わらず安全）
    $rawText = [System.IO.File]::ReadAllText(
        [System.IO.Path]::GetFullPath($InputFile),
        [System.Text.Encoding]::UTF8)
    # JSONL → 空行区切りに正規化
    # leanprover-community/repl は空行区切り JSON を期待する（JSONL 形式ではない）。
    # CR を除去し、各 JSON 行を空行（LF LF）で区切る。
    # JSON オブジェクト以外の行（コメント・空白行以外）は警告してスキップする。
    $allLines = ($rawText -replace '\r', '') -split '\n' | Where-Object { $_.Trim() -ne '' }
    $lines = @($allLines | Where-Object { $_.Trim() -match '^\{' })
    $skippedLines = @($allLines | Where-Object { $_.Trim() -notmatch '^\{' })
    if ($skippedLines.Count -gt 0) {
        Write-Host "警告: JSONL に JSON オブジェクト以外の行が含まれています（スキップされます）:" -ForegroundColor Yellow
        $skippedLines | ForEach-Object { Write-Host "  $_" -ForegroundColor Yellow }
    }
    if ($lines.Count -eq 0) {
        Write-Host "エラー: InputFile に有効な JSON コマンドが含まれていません: $InputFile" -ForegroundColor Red
        Pop-Location
        exit 1
    }
    $userInput = ($lines -join "`n`n") + "`n"
}

if (-not $NoPickle) {
    # --- デフォルトモード: import S2IL + Mathlib.Tactic + Plausible + Duper を自動先頭挿入 ---
    # ring, linarith, exact?, funext 等すべての Mathlib タクティクが env:0 で利用可能。
    $initCmd = Get-InitCmd

    if ($null -ne $userInput) {
        # ユーザー JSONL のインポート状況をチェック（S2IL と Mathlib.Tactic を個別に確認）
        $hasS2IL = $userInput -match 'import\s+S2IL'
        $hasMathlib = $userInput -match 'Mathlib\.Tactic'

        if ($hasS2IL -and $hasMathlib) {
            # 両方のインポートが存在する場合、自動先頭挿入をスキップ
            # ユーザーの import コマンドから "env": N を除去（env 0 はまだ存在しないため）
            $fullInput = $userInput -creplace '("cmd"\s*:\s*"import [^"]+")\s*,\s*"env"\s*:\s*\d+', '$1'
        } else {
            # インポートが不足している場合は自動先頭挿入（ユーザーの部分的 import は冗長だが無害）
            $fullInput = "$initCmd`n`n$userInput"
        }

        $result = Invoke-ReplWithCrashDetect -FullInput $fullInput -HasImport $true

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
    # -NoPickle モード: 自動先頭挿入なし（ユーザーが JSONL 内で import/unpickle を管理）
    if ($null -ne $userInput) {
        $result = Invoke-ReplWithCrashDetect -FullInput $userInput -HasImport $false

        Pop-Location
        if ($result.hasError) { exit 1 } else { exit 0 }
    } else {
        Write-Host "=== Lean REPL 起動（NoPickle: 自動先頭挿入なし） ===" -ForegroundColor Cyan
        lake exe repl
        Pop-Location
    }
}
