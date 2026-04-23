#!/usr/bin/env pwsh
# PostToolUse Hook: .lean ファイル編集後の sorry カウント
# stdin から JSON を読み、対象ファイルが .lean の場合に sorry 数を systemMessage として返す
#
# 入力 (stdin JSON): { "tool_name": "...", "tool_input": { "filePath": "..." }, ... }
# 出力 (stdout JSON): { "systemMessage": "..." } or {}
#
# 注意: VS Code は hooks の matcher を無視するため、すべてのツール呼び出しでこのスクリプトが起動される。
# そのため、できるだけ早期に終了する最速パスを実装している。

[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

try {
    $rawInput = [Console]::In.ReadToEnd()

    # 最速パス: JSON パース前に文字列レベルでツール名を確認
    # 編集ツールでなければ即座に終了（ConvertFrom-Json のオーバーヘッドを回避）
    if ($rawInput -notmatch '"tool_name"\s*:\s*"(replace_string_in_file|multi_replace_string_in_file|create_file)"') {
        '{}'; exit 0
    }

    # 最速パス: .lean ファイルへの言及がなければ即座に終了
    if ($rawInput -notmatch '\.lean') {
        '{}'; exit 0
    }

    # proof-suppressed.flag が存在する場合は証明フック出力を抑止する
    # (session-efficiency スキル発動時 / 明示的な証明停止時に作成される)
    #
    # NOTE: ConvertFrom-Json は tool_input.content / newString / oldString 等が
    # 不正な JSON エスケープ (例: "\" の後に有効なエスケープ文字がない) を含む場合に
    # 失敗するため、cwd と filePath は正規表現で raw 文字列から直接抽出する。

    # cwd を正規表現で抽出（失敗時は現在ディレクトリを使用）
    $cwdForFlag = (Get-Location).Path
    if ($rawInput -match '"cwd"\s*:\s*"((?:[^"\\]|\\.)*)"') {
        $cwdForFlag = $Matches[1] -replace '\\\\', '\' -replace '\\/', '/'
    }
    $suppressFlag = Join-Path $cwdForFlag ".lake/proof-suppressed.flag"
    if (Test-Path $suppressFlag) {
        '{}'; exit 0
    }

    # filePath を正規表現で抽出（filePath / replacements 両対応: 最初の .lean ファイルを選択）
    $filePath = $null
    if ($rawInput -match '"filePath"\s*:\s*"((?:[^"\\]|\\.)*\.lean)"') {
        $filePath = $Matches[1] -replace '\\\\', '\' -replace '\\/', '/'
    }

    # .lean ファイルでなければスキップ
    if (-not $filePath -or $filePath -notmatch '\.lean$') {
        '{}'; exit 0
    }

    # ファイルが存在しなければスキップ
    if (-not (Test-Path $filePath)) {
        '{}'; exit 0
    }

    # sorry カウント（コメント行を除外）
    $sorryLines = @(Select-String -Pattern '\bsorry\b' -Path $filePath |
        Where-Object { $_.Line -notmatch '^\s*--' })
    $sorryCount = $sorryLines.Count

    # 裸 simp 検知: simp/simp_all が only なしで使われている場合に警告
    # 除外: simp only, simp_all only, simp?, simp_all?, コメント行
    $bareSimpLines = @(Select-String -Pattern '\bsimp(_all)?\b' -Path $filePath |
        Where-Object {
            $_.Line -notmatch '^\s*--' -and         # コメント行を除外
            $_.Line -notmatch '\bsimp(_all)?\s+only\b' -and  # simp only を除外
            $_.Line -notmatch '\bsimp(_all)?\?' -and          # simp? を除外
            $_.Line -notmatch '\bsimp(_all)?\s*\(config' -and # simp (config:=...) only を除外（only は前のルールで）
            $_.Line -notmatch 'simpa\b' -and                  # simpa は別タクティク
            $_.Line -notmatch 'dsimp\b'                       # dsimp は別タクティク
        })
    $bareSimpCount = $bareSimpLines.Count

    $messages = [System.Collections.ArrayList]::new()
    $fileName = Split-Path $filePath -Leaf

    if ($sorryCount -gt 0) {
        $null = $messages.Add("sorry count: $sorryCount")
    }

    if ($bareSimpCount -gt 0) {
        $lineNums = ($bareSimpLines | ForEach-Object { $_.LineNumber }) -join ", "
        $null = $messages.Add("⚠ bare simp detected: $bareSimpCount (L$lineNums). Please stabilize with simp only [...]")
    }

    # .lean ファイルが編集されたことをフラグで記録（Stop フックが sorry 通知要否を判断するために使用）
    $lakeDir = Join-Path $cwdForFlag ".lake"
    if (Test-Path $lakeDir) {
        $leanEditedFlag = Join-Path $lakeDir "lean-edited-this-turn.flag"
        [System.IO.File]::WriteAllText($leanEditedFlag, "")
    }

    if ($messages.Count -gt 0) {
        $result = @{
            systemMessage = "[Hook] $fileName — $($messages -join '. ')"
        }
    } else {
        $result = @{}
    }

    $result | ConvertTo-Json -Compress
    exit 0
}
catch {
    # エラー時は警告を出すが処理を止めない
    Write-Error $_.Exception.Message
    @{} | ConvertTo-Json -Compress
    exit 1
}
