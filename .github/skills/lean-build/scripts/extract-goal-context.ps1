#!/usr/bin/env pwsh
# extract-goal-context.ps1
# sorry / 証明中の特定行の「周辺識別子」を symbol-map.jsonl から一括解決する。
#
# 使用例:
#   ./extract-goal-context.ps1 -File S2IL/Operations/Gravity/Defs.lean -Line 1843
#   ./extract-goal-context.ps1 -File S2IL/Operations/Gravity/Defs.lean -Line 1843 -Radius 15 -MaxHits 10
#
# 出力: 周辺 ±Radius 行に登場する識別子について、symbol-map.jsonl の該当 JSONL 行を列挙する。
# エージェントはこの結果だけ見れば、当該 sorry 周辺で参照されうる補題シグネチャを
# 追加の read_file なしで把握できる（案 8: goal-sig auto-extraction）。

param(
    [Parameter(Mandatory=$true)][string]$File,
    [Parameter(Mandatory=$true)][int]$Line,
    [int]$Radius = 20,
    [int]$MaxHits = 20,
    [string]$Root
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

if (-not $Root) {
    $Root = (Resolve-Path (Join-Path $PSScriptRoot "..\..\..\..")).Path
}
$Root = $Root.TrimEnd('\', '/')

$symbolMap = Join-Path $Root "S2IL" "_agent" "symbol-map.jsonl"
if (-not (Test-Path $symbolMap)) {
    Write-Error "symbol-map.jsonl not found: $symbolMap"
    exit 1
}

$targetFile = if ([System.IO.Path]::IsPathRooted($File)) { $File } else { Join-Path $Root $File }
if (-not (Test-Path $targetFile)) {
    Write-Error "target file not found: $targetFile"
    exit 1
}

$all = [System.IO.File]::ReadAllLines($targetFile)
$startLine = [Math]::Max(1, $Line - $Radius)
$endLine   = [Math]::Min($all.Count, $Line + $Radius)
$window = $all[($startLine - 1)..($endLine - 1)] -join "`n"

# Lean 識別子の抽出: ドット区切り / アンダースコア許容、先頭は英字、長さ ≥ 3
# 小文字始まりと大文字始まりの両方を拾う
$idPattern = '[A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*'
$matches = [regex]::Matches($window, $idPattern)
$idSet = [System.Collections.Generic.HashSet[string]]::new()
foreach ($m in $matches) {
    $id = $m.Value
    if ($id.Length -lt 3) { continue }
    # Lean 予約語を除去（代表的なもののみ）
    if ($id -in @('theorem','lemma','def','let','fun','match','with','where','have','show','from','this','exact','apply','refine','intro','rintro','simp','cases','rcases','rfl','sorry','True','False','and','or','not','if','then','else','namespace','section','end','open','import','example','admit','done')) { continue }
    $null = $idSet.Add($id)
}

# symbol-map.jsonl を読み込んで識別子に対応する行を拾う
$map = [System.IO.File]::ReadAllLines($symbolMap)
# symbol から最後のドット以降（simple name）を取り出して index を作る
$simpleIdx = @{}
$fullIdx   = @{}
foreach ($l in $map) {
    if ($l -match '"symbol":"([^"]+)"') {
        $sym = $Matches[1]
        $simple = ($sym -split '\.')[-1]
        $fullIdx[$sym] = $l
        if (-not $simpleIdx.ContainsKey($simple)) {
            $simpleIdx[$simple] = [System.Collections.ArrayList]::new()
        }
        $null = $simpleIdx[$simple].Add($l)
    }
}

$hits = [System.Collections.ArrayList]::new()
$seen = [System.Collections.Generic.HashSet[string]]::new()
foreach ($id in $idSet) {
    # full-qualified 一致優先
    if ($fullIdx.ContainsKey($id)) {
        if ($seen.Add($fullIdx[$id])) { $null = $hits.Add([PSCustomObject]@{ Id = $id; Line = $fullIdx[$id]; Exact = $true }) }
        continue
    }
    # simple name 一致
    $simple = ($id -split '\.')[-1]
    if ($simpleIdx.ContainsKey($simple)) {
        foreach ($ln in $simpleIdx[$simple]) {
            if ($seen.Add($ln)) {
                $null = $hits.Add([PSCustomObject]@{ Id = $id; Line = $ln; Exact = $false })
            }
        }
    }
}

# 出力: Exact match 優先、上限 MaxHits
$ordered = $hits | Sort-Object -Property @{Expression={-not $_.Exact}} | Select-Object -First $MaxHits

Write-Host ("=== GOAL CONTEXT: {0}:{1} (+-{2} lines, {3} unique ids, {4} hits shown {5}) ===" -f $File, $Line, $Radius, $idSet.Count, $hits.Count, [Math]::Min($hits.Count,$MaxHits))
foreach ($h in $ordered) {
    $marker = if ($h.Exact) { '*' } else { ' ' }
    Write-Host "$marker $($h.Line)"
}
Write-Host "=== END GOAL CONTEXT ==="
