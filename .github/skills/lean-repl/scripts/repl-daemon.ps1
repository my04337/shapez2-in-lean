# Lean REPL デーモンプロセス (Windows / PowerShell)
#
# repl.ps1 -Start から背景プロセスとして起動される。
# lake exe repl を管理し、ファイルベース IPC でコマンドを受け付ける。
#
# IPC プロトコル:
#   request.json  ← クライアントが書き込み → デーモンが読み取り・削除
#   response.json ← デーモンが書き込み
#   response.ready ← デーモンがシグナル作成 → クライアントが検知・削除
#   shutdown      ← クライアントが作成 → デーモンが検知して終了

param(
    [Parameter(Mandatory)][string]$SessionId,
    [Parameter(Mandatory)][string]$RepoRoot
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$sessionDir = Join-Path $RepoRoot ".repl" $SessionId
$logIn  = Join-Path $sessionDir "_session-in.jsonl"
$logOut = Join-Path $sessionDir "_session-out.jsonl"

# --- パス設定 ---
$elanBin = Join-Path $env:USERPROFILE ".elan\bin"
if (Test-Path $elanBin) { $env:PATH = "$elanBin;$env:PATH" }
$lakeBin = (Get-Command lake -ErrorAction SilentlyContinue).Source
if (-not $lakeBin) {
    [IO.File]::WriteAllText((Join-Path $sessionDir "error"), "lake not found in PATH")
    exit 1
}

# --- REPL プロセス起動 ---
$psi = [System.Diagnostics.ProcessStartInfo]::new()
$psi.FileName = $lakeBin
$psi.Arguments = "exe repl"
$psi.WorkingDirectory = $RepoRoot
$psi.UseShellExecute = $false
$psi.RedirectStandardInput = $true
$psi.RedirectStandardOutput = $true
$psi.RedirectStandardError = $true
$psi.StandardInputEncoding  = [System.Text.UTF8Encoding]::new($false)
$psi.StandardOutputEncoding = [System.Text.UTF8Encoding]::new($false)
$psi.StandardErrorEncoding  = [System.Text.UTF8Encoding]::new($false)

$script:repl = [System.Diagnostics.Process]::new()
$script:repl.StartInfo = $psi

try {
    $script:repl.Start() | Out-Null
} catch {
    [IO.File]::WriteAllText((Join-Path $sessionDir "error"), "Failed to start REPL: $_")
    exit 1
}

# stderr はバックグラウンドで排出（バッファ溢れ防止）
$script:stderrTask = $script:repl.StandardError.ReadToEndAsync()

# PID 記録
[IO.File]::WriteAllText((Join-Path $sessionDir "daemon.pid"), "$PID")
[IO.File]::WriteAllText((Join-Path $sessionDir "repl.pid"), "$($script:repl.Id)")

# --- stdout 読み取り: ReadLineAsync + タイムアウト ---
# ReadLineAsync を使い、前回の未完了タスクを追跡して concurrent read を防止する。
$script:pendingReadTask = $null

function Read-Line-With-Timeout {
    param([int]$TimeoutMs)

    if (-not $script:pendingReadTask) {
        $script:pendingReadTask = $script:repl.StandardOutput.ReadLineAsync()
    }

    $delayTask = [System.Threading.Tasks.Task]::Delay($TimeoutMs)
    $winner = [System.Threading.Tasks.Task]::WhenAny($script:pendingReadTask, $delayTask).GetAwaiter().GetResult()

    if ($winner -eq $script:pendingReadTask) {
        $line = $script:pendingReadTask.GetAwaiter().GetResult()
        $script:pendingReadTask = $null
        return @{ Value = $line; TimedOut = $false }
    }

    return @{ Value = $null; TimedOut = $true }
}

# --- REPL 応答読み取り ---
# REPL は各応答を pretty-printed JSON で出力し、IO.println により末尾に空行が付く。
# 空行検出をメイン判定とし、500ms 静寂期間をフォールバックとする。
function Read-ReplResponse {
    param([int]$TimeoutMs = 120000)

    $lines = [System.Collections.Generic.List[string]]::new()
    $sw = [System.Diagnostics.Stopwatch]::StartNew()
    $hasContent = $false

    while ($sw.ElapsedMilliseconds -lt $TimeoutMs -and -not $script:repl.HasExited) {
        $remaining = [math]::Max(100, $TimeoutMs - [int]$sw.ElapsedMilliseconds)
        # 1回の ReadLine 待機は最大 500ms（静寂検出用）
        $waitMs = [math]::Min(500, $remaining)
        $result = Read-Line-With-Timeout -TimeoutMs $waitMs

        if ($result.TimedOut) {
            # 応答中のデータがあれば静寂期間として完了
            if ($hasContent) { break }
            continue  # まだ応答待ち
        }

        $line = $result.Value
        if ($null -eq $line) { break }  # EOF (REPL 終了)

        if ($line -eq "" -and $hasContent) {
            break  # 空行検出 → 応答完了
        }
        if ($line.Trim() -ne "") {
            $lines.Add($line)
            $hasContent = $true
        }
    }

    if ($lines.Count -eq 0) { return $null }
    return ($lines -join "`n").Trim()
}

# --- Import 実行 ---
$importCmd = '{"cmd": "import S2IL\nimport Mathlib.Tactic\nimport Plausible\nimport Duper"}'
$script:repl.StandardInput.WriteLine($importCmd)
$script:repl.StandardInput.WriteLine("")
$script:repl.StandardInput.Flush()

[IO.File]::AppendAllText($logIn, "$importCmd`n", [System.Text.UTF8Encoding]::new($false))
$importResp = Read-ReplResponse -TimeoutMs 120000
if ($importResp) {
    try {
        $parsed = $importResp | ConvertFrom-Json -ErrorAction Stop
        $oneLine = $parsed | ConvertTo-Json -Compress -Depth 20
        [IO.File]::AppendAllText($logOut, "$oneLine`n", [System.Text.UTF8Encoding]::new($false))
    } catch {
        [IO.File]::AppendAllText($logOut, "$importResp`n", [System.Text.UTF8Encoding]::new($false))
    }
}

# --- env/proofState リベース ---
# Persistent モードでは env/proofState がセッション全体で単調増加する。
# 各 Send バッチ内で相対的な番号付けを可能にするため、
# バッチ開始時のオフセットを記録し、env (> 0) と proofState を自動リベースする。
# env 0 は常に import 環境を指す（リベース対象外）。
$script:envBase = 0
$script:psBase = 0

function Update-Bases-From-Response {
    param([object]$ParsedResponse)

    # env の追跡
    $envProp = $ParsedResponse.PSObject.Properties['env']
    if ($envProp) {
        $val = [int]$envProp.Value
        if ($val -gt $script:envBase) { $script:envBase = $val }
    }

    # proofState の追跡（tactic mode 応答）
    $psProp = $ParsedResponse.PSObject.Properties['proofState']
    if ($psProp) {
        $val = [int]$psProp.Value
        if ($val -ge $script:psBase) { $script:psBase = $val + 1 }
    }

    # sorries[].proofState の追跡（command mode 応答）
    $sorriesProp = $ParsedResponse.PSObject.Properties['sorries']
    if ($sorriesProp -and $sorriesProp.Value) {
        foreach ($s in $sorriesProp.Value) {
            $spProp = $s.PSObject.Properties['proofState']
            if ($spProp) {
                $val = [int]$spProp.Value
                if ($val -ge $script:psBase) { $script:psBase = $val + 1 }
            }
        }
    }
}

# --- 応答の env/proofState デリベース ---
# 各バッチの応答値をバッチ内相対値に変換する。
# これにより応答の env/proofState がバッチモードと同じ番号付けになる。
function DeRebase-Response {
    param([object]$ParsedResponse, [int]$EnvBase, [int]$PsBase)

    $envProp = $ParsedResponse.PSObject.Properties['env']
    if ($envProp) {
        $envProp.Value = [int]$envProp.Value - $EnvBase
    }

    $psProp = $ParsedResponse.PSObject.Properties['proofState']
    if ($psProp) {
        $psProp.Value = [int]$psProp.Value - $PsBase
    }

    $sorriesProp = $ParsedResponse.PSObject.Properties['sorries']
    if ($sorriesProp -and $sorriesProp.Value) {
        foreach ($s in $sorriesProp.Value) {
            $spProp = $s.PSObject.Properties['proofState']
            if ($spProp) {
                $spProp.Value = [int]$spProp.Value - $PsBase
            }
        }
    }
}

# --- メインループ ---
$requestFile  = Join-Path $sessionDir "request.json"
$responseFile = Join-Path $sessionDir "response.json"
$responseDone = Join-Path $sessionDir "response.ready"
$shutdownFile = Join-Path $sessionDir "shutdown"

try {
    # Ready シグナル: メインループ開始後（コマンド受付確定状態）で発行し、競合タイミングを防ぐ
    [IO.File]::WriteAllText((Join-Path $sessionDir "ready"), "ok")
    while (-not $script:repl.HasExited) {
        if (Test-Path $shutdownFile) { break }

        if (Test-Path $requestFile) {
            try {
                # リクエスト読み取り
                $content = [IO.File]::ReadAllText($requestFile, [System.Text.Encoding]::UTF8).Trim()
                Remove-Item $requestFile -Force -ErrorAction SilentlyContinue

                [IO.File]::AppendAllText($logIn, "$content`n", [System.Text.UTF8Encoding]::new($false))

                # コマンド分割（JSONL: 各行が1つの JSON コマンド）
                $cmds = @($content -split '\r?\n' | Where-Object { $_.Trim() -ne '' })
                $responses = [System.Collections.Generic.List[string]]::new()

                # バッチ開始時のオフセットをスナップショット（バッチ内で一貫したリベースを保証）
                $batchEnvBase = $script:envBase
                $batchPsBase = $script:psBase

                foreach ($c in $cmds) {
                    # env/proofState リベース
                    $cmdToSend = $c
                    $obj = $c | ConvertFrom-Json -ErrorAction SilentlyContinue
                    if ($obj) {
                        $modified = $false
                        # env > 0 のリベース（env 0 = import 環境は常に固定）
                        $envProp = $obj.PSObject.Properties['env']
                        if ($envProp -and [int]$envProp.Value -gt 0) {
                            $envProp.Value = [int]$envProp.Value + $batchEnvBase
                            $modified = $true
                        }
                        # proofState のリベース（全値をオフセット）
                        $psProp = $obj.PSObject.Properties['proofState']
                        if ($psProp) {
                            $psProp.Value = [int]$psProp.Value + $batchPsBase
                            $modified = $true
                        }
                        if ($modified) {
                            $cmdToSend = $obj | ConvertTo-Json -Compress -Depth 10
                        }
                    }

                    $script:repl.StandardInput.WriteLine($cmdToSend)
                    $script:repl.StandardInput.WriteLine("")
                    $script:repl.StandardInput.Flush()

                    $resp = Read-ReplResponse -TimeoutMs 120000
                    if ($resp) {
                        try {
                            $parsed = $resp | ConvertFrom-Json -ErrorAction Stop
                            Update-Bases-From-Response -ParsedResponse $parsed
                            DeRebase-Response -ParsedResponse $parsed -EnvBase $batchEnvBase -PsBase $batchPsBase
                            $responses.Add(($parsed | ConvertTo-Json -Compress -Depth 20))
                        } catch {
                            $responses.Add($resp)
                        }
                    } else {
                        $responses.Add('{"error":"response_timeout","message":"No response from REPL within timeout"}')
                    }
                }

                $allResp = $responses -join "`n"
                [IO.File]::WriteAllText($responseFile, $allResp, [System.Text.UTF8Encoding]::new($false))
                [IO.File]::AppendAllText($logOut, "$allResp`n", [System.Text.UTF8Encoding]::new($false))
                [IO.File]::WriteAllText($responseDone, "ok")
            } catch {
                $errJson = (@{ error = "daemon_error"; message = $_.ToString() } | ConvertTo-Json -Compress)
                [IO.File]::WriteAllText($responseFile, $errJson, [System.Text.UTF8Encoding]::new($false))
                [IO.File]::WriteAllText($responseDone, "ok")
            }
        }

        [System.Threading.Thread]::Sleep(30)
    }
} finally {
    # クリーンアップ
    if ($script:repl -and -not $script:repl.HasExited) {
        try { $script:repl.Kill() } catch {}
    }
    if ($script:repl) { $script:repl.Dispose() }
    Remove-Item (Join-Path $sessionDir "daemon.pid") -Force -ErrorAction SilentlyContinue
    Remove-Item (Join-Path $sessionDir "repl.pid") -Force -ErrorAction SilentlyContinue
    Remove-Item (Join-Path $sessionDir "ready") -Force -ErrorAction SilentlyContinue
}
