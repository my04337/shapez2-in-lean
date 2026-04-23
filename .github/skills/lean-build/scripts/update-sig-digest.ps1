#!/usr/bin/env pwsh
# update-sig-digest.ps1
# S2IL/_agent/sig-digest/<dotted-module>.md を Lean ソースから再生成する。
# 案 1 (per-file signature digest) + 案 4 (landmark index) を統合した成果物。
#
# エージェントはこのファイルを 1 枚読むだけで以下を把握できる:
#   - ファイル全体の宣言一覧（シグネチャ付き）
#   - namespace / section / 見出しコメントの位置（landmark）
#   - private/sorry 分布の統計
#
# build.ps1 から自動呼び出しされる。
#
# 使い方: ./update-sig-digest.ps1 [-Root <workspace-root>]

param(
    [string]$Root
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

if (-not $Root) {
    $Root = (Resolve-Path (Join-Path $PSScriptRoot "..\..\..\..")).Path
}
$Root = $Root.TrimEnd('\', '/')

$s2ilDir = Join-Path $Root "S2IL"
$outDir  = Join-Path $Root "S2IL" "_agent" "sig-digest"

if (-not (Test-Path $s2ilDir)) {
    Write-Host "[update-sig-digest] S2IL directory not found: $s2ilDir"
    exit 1
}

# 出力先を再作成（削除されたファイルの残骸を防ぐ）
if (Test-Path $outDir) { Remove-Item $outDir -Recurse -Force }
New-Item -ItemType Directory -Path $outDir -Force | Out-Null

# update-symbol-map.ps1 と同一の正規表現 + ヘルパを内蔵（単独実行可能に）
$declPattern = '^\s*(?<mods>(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*)(?:@\[.*?\]\s+)*(?<kind>def|theorem|lemma|instance|abbrev|structure|inductive|class|axiom|opaque)\s+(?<name>\S+)'

function Get-SigPreview {
    param([string[]]$Lines, [int]$StartIdx)
    $maxLookahead = 20
    $end = [Math]::Min($StartIdx + $maxLookahead, $Lines.Count - 1)
    $collected = @()
    for ($i = $StartIdx; $i -le $end; $i++) {
        $l = $Lines[$i]
        $idx = $l.IndexOf('--')
        if ($idx -ge 0) { $l = $l.Substring(0, $idx) }
        $collected += $l
        if ($l -match ':=|\bwhere\b') { break }
    }
    $joined = ($collected -join ' ')
    $cutIdx = $joined.IndexOf(':=')
    if ($cutIdx -ge 0) { $joined = $joined.Substring(0, $cutIdx) }
    $joined = ($joined -creplace '\s+', ' ').Trim()
    if ($joined.Length -gt 200) { $joined = $joined.Substring(0, 197) + '...' }
    return $joined
}

$leanFiles = Get-ChildItem -Path $s2ilDir -Filter "*.lean" -Recurse
$fileCount = 0
$totalDecls = 0

foreach ($file in $leanFiles) {
    $relPath = $file.FullName.Substring($Root.Length + 1) -creplace '\\', '/'
    $lines = [System.IO.File]::ReadAllLines($file.FullName)
    $lineCount = $lines.Count

    # モジュール名: S2IL/Operations/Gravity/Defs.lean -> S2IL.Operations.Gravity.Defs
    $modName = ($relPath -replace '\.lean$', '') -replace '/', '.'
    $outFile = Join-Path $outDir "$modName.md"

    $landmarks = [System.Collections.ArrayList]::new()
    $decls     = [System.Collections.ArrayList]::new()
    $nsStack   = [System.Collections.Generic.Stack[string]]::new()

    $privateCount = 0
    $sorryCount   = 0
    $theoremCount = 0
    $defCount     = 0

    for ($idx = 0; $idx -lt $lines.Count; $idx++) {
        $line = $lines[$idx]
        $lineNo = $idx + 1

        if ($line -match '^\s*--') { continue }

        # --- Landmark: /-! ... -/ ヘッダコメント（1 行目のみ抽出）---
        if ($line -match '^\s*/-!') {
            # 次の非空行から見出しを取る
            $title = ''
            for ($k = $idx; $k -lt [Math]::Min($idx + 5, $lines.Count); $k++) {
                $t = ($lines[$k] -replace '/-!', '' -replace '-/', '').Trim()
                if ($t -and $t -notmatch '^#?\s*$') { $title = $t; break }
            }
            if ($title) {
                $null = $landmarks.Add([PSCustomObject]@{ Line = $lineNo; Type = 'header'; Title = $title })
            }
        }

        # --- namespace 追跡（landmark にも記録）---
        if ($line -match '^\s*namespace\s+(\S+)') {
            $nsName = $Matches[1]
            $nsStack.Push($nsName)
            $null = $landmarks.Add([PSCustomObject]@{ Line = $lineNo; Type = 'namespace'; Title = $nsName })
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
        if ($line -match '^\s*section(?:\s+(\S+))?') {
            $sectName = if ($Matches.Count -gt 1) { $Matches[1] } else { '(anonymous)' }
            $null = $landmarks.Add([PSCustomObject]@{ Line = $lineNo; Type = 'section'; Title = $sectName })
            continue
        }

        # --- 宣言抽出 ---
        if ($line -match $declPattern) {
            $kind = $Matches['kind']
            $rawName = $Matches['name']
            $mods = $Matches['mods']
            $isPrivate = ($mods -match '\bprivate\b')
            $rawName = $rawName -creplace '[:\s\{\(\[].*', ''
            if (-not $rawName -or $rawName -eq '') { continue }

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

            $sig = Get-SigPreview -Lines $lines -StartIdx $idx
            $sigPrefixRx = "^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*" +
                [regex]::Escape($kind) + "\s+" + [regex]::Escape($rawName) + "\s*"
            $sig = [regex]::Replace($sig, $sigPrefixRx, '')

            # sorry 検出（次の ~30 行に sorry 単語があれば）
            $bodyEnd = [Math]::Min($idx + 30, $lines.Count - 1)
            $hasSorry = $false
            for ($k = $idx; $k -le $bodyEnd; $k++) {
                if ($lines[$k] -match '\bsorry\b' -and $lines[$k] -notmatch '--.*sorry') {
                    $hasSorry = $true; break
                }
            }

            if ($isPrivate) { $privateCount++ }
            if ($hasSorry)  { $sorryCount++ }
            if ($kind -eq 'theorem' -or $kind -eq 'lemma') { $theoremCount++ }
            elseif ($kind -eq 'def' -or $kind -eq 'abbrev') { $defCount++ }

            $null = $decls.Add([PSCustomObject]@{
                Line    = $lineNo
                Kind    = $kind
                Symbol  = $symbol
                Sig     = $sig
                Private = $isPrivate
                Sorry   = $hasSorry
            })
        }
    }

    # --- Markdown 組み立て ---
    $sb = [System.Text.StringBuilder]::new()
    $null = $sb.AppendLine("# $relPath")
    $null = $sb.AppendLine()
    $null = $sb.AppendLine("- Lines: $lineCount")
    $null = $sb.AppendLine("- Declarations: $($decls.Count) (theorems/lemmas: $theoremCount, defs/abbrev: $defCount, private: $privateCount, sorry: $sorryCount)")
    $null = $sb.AppendLine()

    if ($landmarks.Count -gt 0) {
        $null = $sb.AppendLine("## Landmarks")
        $null = $sb.AppendLine()
        foreach ($lm in $landmarks) {
            $prefix = switch ($lm.Type) {
                'namespace' { 'namespace' }
                'section'   { 'section' }
                'header'    { 'header' }
                default     { $lm.Type }
            }
            $null = $sb.AppendLine(("L{0,-5} {1,-9} {2}" -f $lm.Line, $prefix, $lm.Title))
        }
        $null = $sb.AppendLine()
    }

    if ($decls.Count -gt 0) {
        $null = $sb.AppendLine("## Declarations")
        $null = $sb.AppendLine()
        $null = $sb.AppendLine('```')
        foreach ($d in $decls) {
            $flags = ''
            if ($d.Private) { $flags += '[priv]' }
            if ($d.Sorry)   { $flags += '[sorry]' }
            $null = $sb.AppendLine(("L{0,-5} {1,-10} {2}{3} : {4}" -f $d.Line, $d.Kind, $d.Symbol, $flags, $d.Sig))
        }
        $null = $sb.AppendLine('```')
    }

    $utf8NoBom = [System.Text.UTF8Encoding]::new($false)
    [System.IO.File]::WriteAllText($outFile, $sb.ToString(), $utf8NoBom)
    $fileCount++
    $totalDecls += $decls.Count
}

Write-Host "[update-sig-digest] $fileCount digests ($totalDecls declarations) -> $outDir"
