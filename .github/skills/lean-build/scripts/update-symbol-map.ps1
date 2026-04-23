#!/usr/bin/env pwsh
# update-symbol-map.ps1
# S2IL/_agent/symbol-map.jsonl を Lean ソースファイルから再生成する。
# lean-build/scripts/build.ps1 からビルド成功後に自動呼び出しされる。
#
# 使い方: ./update-symbol-map.ps1 [-Root <workspace-root>]

param(
    [string]$Root
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

# ワークスペースルート解決
if (-not $Root) {
    $Root = (Resolve-Path (Join-Path $PSScriptRoot "..\..\..\..")).Path
}
# 末尾のディレクトリ区切り文字を除去（呼び出し元が付与した場合の相対パス崩れ防止）
$Root = $Root.TrimEnd('\', '/')

$s2ilDir  = Join-Path $Root "S2IL"
$outFile  = Join-Path $Root "S2IL" "_agent" "symbol-map.jsonl"

if (-not (Test-Path $s2ilDir)) {
    Write-Host "[update-symbol-map] S2IL directory not found: $s2ilDir"
    exit 1
}

# 出力先ディレクトリ確保
$outDir = Split-Path $outFile -Parent
if (-not (Test-Path $outDir)) { New-Item -ItemType Directory -Path $outDir -Force | Out-Null }

# 宣言キーワードの正規表現（行頭、修飾子対応）
# 修飾子の private を捕捉するため個別キャプチャに分離
$declPattern = '^\s*(?<mods>(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*)(?:@\[.*?\]\s+)*(?<kind>def|theorem|lemma|instance|abbrev|structure|inductive|class|axiom|opaque)\s+(?<name>\S+)'

$entries = [System.Collections.ArrayList]::new()
$leanFiles = Get-ChildItem -Path $s2ilDir -Filter "*.lean" -Recurse

# 型シグネチャを 1 行に整形（最大 200 文字）
function Get-SigPreview {
    param([string[]]$Lines, [int]$StartIdx)
    $maxLookahead = 20
    $end = [Math]::Min($StartIdx + $maxLookahead, $Lines.Count - 1)
    $collected = @()
    for ($i = $StartIdx; $i -le $end; $i++) {
        $l = $Lines[$i]
        # 行内の行コメント `--` 以降を削除
        $idx = $l.IndexOf('--')
        if ($idx -ge 0) { $l = $l.Substring(0, $idx) }
        $collected += $l
        if ($l -match ':=|\bwhere\b') { break }
    }
    $joined = ($collected -join ' ')
    # `:=` 以降は証明本体なので切り落とす
    $cutIdx = $joined.IndexOf(':=')
    if ($cutIdx -ge 0) { $joined = $joined.Substring(0, $cutIdx) }
    # 連続空白を 1 個に圧縮
    $joined = ($joined -creplace '\s+', ' ').Trim()
    # 先頭の宣言修飾子は残す（kind までは含む）
    if ($joined.Length -gt 200) { $joined = $joined.Substring(0, 197) + '...' }
    return $joined
}

foreach ($file in $leanFiles) {
    $relPath = $file.FullName.Substring($Root.Length + 1) -creplace '\\', '/'
    $lines = [System.IO.File]::ReadAllLines($file.FullName)
    $totalLines = $lines.Count
    $nsStack = [System.Collections.Generic.Stack[string]]::new()

    # ファイル単位で一時エントリを貯めて、後で endLine を計算してから出力する
    $fileEntries = [System.Collections.ArrayList]::new()

    # sig-digest パスを算出（S2IL/Operations/Gravity/ProcessWave.lean → S2IL/_agent/sig-digest/S2IL.Operations.Gravity.ProcessWave.md）
    $dotted = ($relPath -creplace '\.lean$', '') -creplace '/', '.'
    $digestPath = "S2IL/_agent/sig-digest/$dotted.md"

    for ($idx = 0; $idx -lt $lines.Count; $idx++) {
        $line = $lines[$idx]
        $lineNo = $idx + 1
        # --- コメント行をスキップ ---
        if ($line -match '^\s*--') { continue }

        # --- namespace 追跡 ---
        if ($line -match '^\s*namespace\s+(\S+)') {
            $nsStack.Push($Matches[1])
            continue
        }
        if ($line -match '^\s*end\s+(\S+)') {
            if ($nsStack.Count -gt 0) { $nsStack.Pop() | Out-Null }
            continue
        }
        if ($line -match '^\s*end\s*$') {
            if ($nsStack.Count -gt 0) { $nsStack.Pop() | Out-Null }
            continue
        }

        # --- 宣言抽出 ---
        if ($line -match $declPattern) {
            $kind = $Matches['kind']
            $rawName = $Matches['name']
            $mods = $Matches['mods']
            $isPrivate = ($mods -match '\bprivate\b')

            # 末尾の記号を除去
            $rawName = $rawName -creplace '[:\s\{\(\[].*', ''
            if (-not $rawName -or $rawName -eq '') { continue }

            # namespace による修飾
            if ($nsStack.Count -gt 0) {
                $arr = $nsStack.ToArray()
                [Array]::Reverse($arr)
                $currentNs = $arr -join '.'
                if (-not $rawName.Contains('.')) {
                    $symbol = "$currentNs.$rawName"
                } else {
                    $symbol = $rawName
                }
            } else {
                $symbol = $rawName
            }

            # シグネチャプレビュー
            $sig = Get-SigPreview -Lines $lines -StartIdx $idx

            # sig フィールドから先頭の「修飾子+kind+shortname」を除去する
            # （sig と symbol の両フィールドに同名が含まれると grep_search で各行が2回ヒットするため）
            $sigPrefixRx = "^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*" +
                [regex]::Escape($kind) + "\s+" + [regex]::Escape($rawName) + "\s*"
            $sig = [regex]::Replace($sig, $sigPrefixRx, '')

            # JSON エスケープ
            $escapedSymbol = $symbol -creplace '\\', '\\\\' -creplace '"', '\"'
            $escapedFile   = $relPath -creplace '\\', '\\\\' -creplace '"', '\"'
            $escapedKind   = $kind    -creplace '\\', '\\\\' -creplace '"', '\"'
            $escapedSig    = $sig     -creplace '\\', '\\\\' -creplace '"', '\"'
            $escapedDigest = $digestPath -creplace '\\', '\\\\' -creplace '"', '\"'

            $scopeField = if ($isPrivate) { ',"scope":"private"' } else { '' }
            # endLine は後続エントリ確定後に埋めるため placeholder を入れる
            $null = $fileEntries.Add([PSCustomObject]@{
                line          = $lineNo
                escapedFile   = $escapedFile
                escapedKind   = $escapedKind
                escapedSymbol = $escapedSymbol
                scopeField    = $scopeField
                escapedSig    = $escapedSig
                escapedDigest = $escapedDigest
            })
        }
    }

    # ファイル内の各エントリに endLine を付与 (= 次エントリの line - 1、最後は totalLines)
    for ($i = 0; $i -lt $fileEntries.Count; $i++) {
        $e = $fileEntries[$i]
        if ($i + 1 -lt $fileEntries.Count) {
            $endLine = $fileEntries[$i + 1].line - 1
        } else {
            $endLine = $totalLines
        }
        if ($endLine -lt $e.line) { $endLine = $e.line }
        $jsonLine = "{`"file`":`"$($e.escapedFile)`",`"line`":$($e.line),`"endLine`":$endLine,`"kind`":`"$($e.escapedKind)`",`"symbol`":`"$($e.escapedSymbol)`"$($e.scopeField),`"sig`":`"$($e.escapedSig)`",`"digest`":`"$($e.escapedDigest)`"}"
        $null = $entries.Add($jsonLine)
    }
}

# BOM なし UTF-8 で書き出し
$utf8NoBom = [System.Text.UTF8Encoding]::new($false)
$content = ($entries -join "`n") + "`n"
[System.IO.File]::WriteAllText($outFile, $content, $utf8NoBom)

Write-Host "[update-symbol-map] $($entries.Count) symbols -> $outFile"
