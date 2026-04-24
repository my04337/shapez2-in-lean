#!/usr/bin/env pwsh
# update-sorry-goals.ps1
# S2IL/_agent/sorry-goals.md を `.lean` ソースを直接スキャンして生成する。
#
# build-diagnostics.jsonl はビルドがキャッシュヒットすると更新されず stale に
# なるため、本スクリプトはソースを一次ソースとし、diagnostics は任意補助とする。

param(
    [string]$Root,
    [string]$Diag,
    [string[]]$ScanRoots = @('S2IL')
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

if (-not $Root) {
    $Root = (Resolve-Path (Join-Path $PSScriptRoot "..\..\..\..")).Path
}
$Root = $Root.TrimEnd('\', '/')

$outFile = Join-Path $Root "S2IL" "_agent" "sorry-goals.md"

$leanFiles = @()
foreach ($sub in $ScanRoots) {
    $dir = Join-Path $Root $sub
    if (Test-Path $dir) {
        $leanFiles += Get-ChildItem -Path $dir -Recurse -Filter '*.lean' -File |
            Where-Object { $_.FullName -notmatch '[\\/]_archive[\\/]' }
    }
}

$sorryPattern = '(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])'
$sorries = [System.Collections.ArrayList]::new()

foreach ($f in $leanFiles) {
    $lines = [System.IO.File]::ReadAllLines($f.FullName)
    $inBlockComment = $false
    for ($i = 0; $i -lt $lines.Count; $i++) {
        $raw = $lines[$i]
        $scan = $raw
        if ($inBlockComment) {
            $endIdx = $scan.IndexOf('-/')
            if ($endIdx -lt 0) { continue }
            $scan = $scan.Substring($endIdx + 2)
            $inBlockComment = $false
        }
        while ($true) {
            $openIdx = $scan.IndexOf('/-')
            if ($openIdx -lt 0) { break }
            $closeIdx = $scan.IndexOf('-/', $openIdx + 2)
            if ($closeIdx -lt 0) {
                $scan = $scan.Substring(0, $openIdx)
                $inBlockComment = $true
                break
            }
            $scan = $scan.Substring(0, $openIdx) + $scan.Substring($closeIdx + 2)
        }
        $commentIdx = $scan.IndexOf('--')
        if ($commentIdx -ge 0) { $scan = $scan.Substring(0, $commentIdx) }
        if (-not ($scan -match $sorryPattern)) { continue }

        $rel = $f.FullName.Substring($Root.Length + 1) -replace '\\', '/'
        $null = $sorries.Add([PSCustomObject]@{
            file    = $rel
            line    = $i + 1
            absPath = $f.FullName
            snippet = $raw.Trim()
        })
    }
}

$sorries = @($sorries | Sort-Object file, line)

if (-not $Diag) {
    $lakeDir = Join-Path $Root ".lake"
    $sessionIdFile = Join-Path $lakeDir "session-id.tmp"
    $Diag = Join-Path $lakeDir "build-diagnostics.jsonl"
    if (Test-Path $sessionIdFile) {
        $sid = ([System.IO.File]::ReadAllText($sessionIdFile, [System.Text.Encoding]::UTF8)).Trim()
        if ($sid) {
            $cand = Join-Path $lakeDir "build-diagnostics-$sid.jsonl"
            if (Test-Path $cand) { $Diag = $cand }
        }
    }
}
$diagMap = @{}
if (Test-Path $Diag) {
    foreach ($line in [System.IO.File]::ReadAllLines($Diag)) {
        if (-not $line) { continue }
        try { $j = $line | ConvertFrom-Json } catch { continue }
        if ($j.PSObject.Properties.Name -contains 'isSorry' -and $j.isSorry) {
            $key = "$($j.file):$($j.line)"
            $diagMap[$key] = $j.message
        }
    }
}

$declPattern = '^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(?:@\[.*?\]\s+)*(?<kind>def|theorem|lemma|instance|abbrev|structure|inductive|class|axiom|opaque)\s+(?<name>\S+)'

function Get-EnclosingDecl {
    param([string]$FilePath, [int]$SorryLine)
    if (-not (Test-Path $FilePath)) { return $null }
    $lines = [System.IO.File]::ReadAllLines($FilePath)
    $end = [Math]::Min($SorryLine - 1, $lines.Count - 1)
    $start = -1
    $declKind = ''
    $declName = ''
    $minLine = [Math]::Max(0, $end - 400)
    for ($i = $end; $i -ge $minLine; $i--) {
        if ($lines[$i] -match $declPattern) {
            $start = $i
            $declKind = $Matches['kind']
            $declName = $Matches['name'] -creplace '[:\s\{\(\[].*', ''
            break
        }
    }
    if ($start -lt 0) { return $null }
    $sigEnd = [Math]::Min($start + 30, $lines.Count - 1)
    $sigLines = @()
    for ($i = $start; $i -le $sigEnd; $i++) {
        $sigLines += $lines[$i]
        if ($lines[$i] -match ':=|\bwhere\b') { break }
    }
    [PSCustomObject]@{
        declLine  = $start + 1
        kind      = $declKind
        name      = $declName
        signature = ($sigLines -join "`n")
    }
}

$now = Get-Date -Format 'yyyy-MM-dd HH:mm:ss'
$md = [System.Collections.ArrayList]::new()
$null = $md.Add("# Sorry Goals Snapshot")
$null = $md.Add("")
$null = $md.Add("> 自動生成: $now")
$null = $md.Add("> ソース: ``.lean`` ファイル直接スキャン (build diagnostics に非依存)")
$null = $md.Add("> スキャン対象: $($ScanRoots -join ', ')")
$null = $md.Add("> 用途: sorry 位置の含む宣言シグネチャを REPL 起動なしで取得する")
$null = $md.Add("")
$null = $md.Add("sorry 件数: **$($sorries.Count)**")
$null = $md.Add("")

if ($sorries.Count -eq 0) {
    $null = $md.Add("sorry なし。")
} else {
    $i = 0
    foreach ($s in $sorries) {
        $i++
        $info = Get-EnclosingDecl -FilePath $s.absPath -SorryLine ([int]$s.line)
        $null = $md.Add("## $i. $($s.file):$($s.line)")
        $null = $md.Add("")
        if ($info) {
            $null = $md.Add("- 宣言: ``$($info.name)`` (*$($info.kind)* at L$($info.declLine))")
            $null = $md.Add("")
            $null = $md.Add('```lean')
            $null = $md.Add($info.signature)
            $null = $md.Add('```')
        } else {
            $null = $md.Add("- 宣言: (未検出)")
        }
        $null = $md.Add("")
        $null = $md.Add("sorry 行: ``$($s.snippet)``")
        $null = $md.Add("")
        $key = "$($s.file):$($s.line)"
        if ($diagMap.ContainsKey($key)) {
            $msg = ($diagMap[$key] -split "`n")[0]
            if ($msg.Length -gt 200) { $msg = $msg.Substring(0, 200) + '...' }
            $null = $md.Add("ビルド診断: $msg")
            $null = $md.Add("")
        }
    }
}

$outDir = Split-Path $outFile -Parent
if (-not (Test-Path $outDir)) { New-Item -ItemType Directory -Path $outDir -Force | Out-Null }

$utf8NoBom = [System.Text.UTF8Encoding]::new($false)
[System.IO.File]::WriteAllText($outFile, ($md -join "`n") + "`n", $utf8NoBom)

Write-Host "[update-sorry-goals] $($sorries.Count) sorries -> $outFile"
