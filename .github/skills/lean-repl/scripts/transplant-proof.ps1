#!/usr/bin/env pwsh
# SPDX-FileCopyrightText: 2026 my04337
# SPDX-License-Identifier: MIT
#
# transplant-proof.ps1 — REPL で完成した証明を .lean ファイルの sorry 行に移植する
#
# 使い方:
#   # -ProofFile で証明テキストをファイルから渡す（推奨：エスケープ問題を回避）
#   .github/skills/lean-repl/scripts/transplant-proof.ps1 -File S2IL/Foo.lean -Line 42 -ProofFile Scratch/proof.lean
#
#   # -Proof で証明テキストを直接渡す（1行の場合）
#   .github/skills/lean-repl/scripts/transplant-proof.ps1 -File S2IL/Foo.lean -Line 42 -Proof "by omega"
#
#   # -SimpStabilize で移植後に bare simp → simp only 一括変換を chain 実行
#   .github/skills/lean-repl/scripts/transplant-proof.ps1 -File S2IL/Foo.lean -Line 42 -ProofFile Scratch/proof.lean -SimpStabilize
#
#   # -DryRun でファイルを変更せず、置換結果をプレビュー
#   .github/skills/lean-repl/scripts/transplant-proof.ps1 -File S2IL/Foo.lean -Line 42 -ProofFile Scratch/proof.lean -DryRun
#
# 処理フロー:
#   1. 対象ファイルの指定行から sorry を検出
#   2. sorry 行のインデント深さを自動検出
#   3. 証明テキストの各行にインデントを適用
#   4. sorry を証明テキストで置換
#   5. UTF-8 BOM なしでファイルに書き込み
#   6. -SimpStabilize 指定時: simp-stabilize.ps1 を chain 実行

[CmdletBinding()]
param(
    [Parameter(Mandatory)]
    [string]$File,

    [Parameter(Mandatory)]
    [int]$Line,

    [string]$Proof,

    [string]$ProofFile,

    [switch]$SimpStabilize,

    [switch]$DryRun
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

if (-not $Proof -and -not $ProofFile) {
    Write-Err "-Proof または -ProofFile のいずれかを指定してください"
    exit 1
}

if ($Proof -and $ProofFile) {
    Write-Warn "-Proof と -ProofFile の両方が指定されました。-ProofFile を優先します"
}

if (-not (Test-Path $File)) {
    Write-Err "ファイルが見つかりません: $File"
    exit 1
}

# --- 証明テキストの取得 ---

$proofText = ""
if ($ProofFile) {
    if (-not (Test-Path $ProofFile)) {
        Write-Err "証明ファイルが見つかりません: $ProofFile"
        exit 1
    }
    $proofText = [System.IO.File]::ReadAllText((Resolve-Path $ProofFile), [System.Text.Encoding]::UTF8).TrimEnd()
} else {
    $proofText = $Proof
}

if (-not $proofText.Trim()) {
    Write-Err "証明テキストが空です"
    exit 1
}

Write-Info "証明テキスト: $($proofText.Split("`n").Count) 行"

# --- ファイル読み込み ---

$absFile = Resolve-Path $File
$content = [System.IO.File]::ReadAllText($absFile, [System.Text.Encoding]::UTF8)
# 改行コードを LF に正規化して処理し、書き込み時もそのまま維持
$lines = $content -split "`n"

# --- sorry 行の検出 ---

$lineIdx = $Line - 1  # 0-based index

if ($lineIdx -lt 0 -or $lineIdx -ge $lines.Count) {
    Write-Err "行番号 $Line はファイルの範囲外です (1-$($lines.Count))"
    exit 1
}

$targetLine = $lines[$lineIdx]

if ($targetLine -notmatch '\bsorry\b') {
    Write-Err "行 $Line に sorry が見つかりません: '$($targetLine.Trim())'"
    exit 1
}

Write-Info "対象行 L${Line}: $($targetLine.TrimEnd())"

# --- インデント検出 ---

# sorry の位置のインデントを基準にする
# パターン: "    sorry" → インデント = "    "
# パターン: "    exact sorry" → sorry だけを置換し、インデントは sorry の列位置
# パターン: ":= by sorry" → sorry だけを置換

$sorryMatch = [regex]::Match($targetLine, '\bsorry\b')
$sorryCol = $sorryMatch.Index

# sorry が行の主要コンテンツ（行頭の空白 + sorry だけ）かどうか判定
$isSorryOnly = $targetLine.Trim() -eq "sorry"

if ($isSorryOnly) {
    # sorry が行単独: 行のインデントを基準にして全体を置換
    $baseIndent = ""
    if ($targetLine -match '^(\s+)') {
        $baseIndent = $Matches[1]
    }
} else {
    # sorry がインラインにある場合: sorry 部分だけを置換
    # インデントは sorry の列位置（複数行の場合の 2 行目以降用）
    $baseIndent = " " * $sorryCol
}

Write-Info "ベースインデント: $($baseIndent.Length) 文字 (sorry-only: $isSorryOnly)"

# --- 証明テキストのインデント適用 ---

$proofLines = $proofText -split "`n"

# 証明テキストの既存インデントを検出して正規化
# 最小インデント（空でない行）を求める
$minIndent = [int]::MaxValue
foreach ($pl in $proofLines) {
    if ($pl.Trim().Length -gt 0) {
        $leadingSpaces = 0
        foreach ($ch in $pl.ToCharArray()) {
            if ($ch -eq ' ') { $leadingSpaces++ }
            elseif ($ch -eq "`t") { $leadingSpaces += 2 }  # tab → 2 spaces
            else { break }
        }
        $minIndent = [Math]::Min($minIndent, $leadingSpaces)
    }
}
if ($minIndent -eq [int]::MaxValue) { $minIndent = 0 }

# 証明テキストにインデントを適用
$indentedProofLines = [System.Collections.ArrayList]::new()
for ($i = 0; $i -lt $proofLines.Count; $i++) {
    $pl = $proofLines[$i]
    if ($pl.Trim().Length -eq 0) {
        $null = $indentedProofLines.Add("")
        continue
    }

    # 元のインデントを除去
    $stripped = $pl.Substring([Math]::Min($minIndent, $pl.Length))
    # タブをスペースに変換
    $stripped = $stripped -replace "`t", "  "

    if ($i -eq 0 -and -not $isSorryOnly) {
        # 最初の行: sorry の位置にインラインで挿入するので追加インデントなし
        $null = $indentedProofLines.Add($stripped)
    } else {
        $null = $indentedProofLines.Add("$baseIndent$stripped")
    }
}

$indentedProof = $indentedProofLines -join "`n"

# --- sorry 置換 ---

if ($isSorryOnly) {
    # sorry 単独行: 行全体を置換
    if ($proofLines.Count -eq 1) {
        $lines[$lineIdx] = $indentedProof
    } else {
        # 複数行証明: 元の 1 行を複数行で置き換え
        $newLines = [System.Collections.ArrayList]::new()
        for ($i = 0; $i -lt $lines.Count; $i++) {
            if ($i -eq $lineIdx) {
                foreach ($ipl in $indentedProofLines) {
                    $null = $newLines.Add($ipl)
                }
            } else {
                $null = $newLines.Add($lines[$i])
            }
        }
        $lines = $newLines.ToArray()
    }
} else {
    # インライン sorry: sorry 部分だけを置換
    $beforeSorry = $targetLine.Substring(0, $sorryCol)
    $afterSorry = $targetLine.Substring($sorryCol + "sorry".Length)

    if ($proofLines.Count -eq 1) {
        # 1 行証明: インラインで置換
        $lines[$lineIdx] = "$beforeSorry$($indentedProofLines[0])$afterSorry"
    } else {
        # 複数行証明: 最初の行はインライン、残りは後続行として挿入
        $firstLine = "$beforeSorry$($indentedProofLines[0])"
        $remainingLines = $indentedProofLines[1..($indentedProofLines.Count - 1)]

        # afterSorry が空白のみでなければ最後の行に追加
        $trimmedAfter = $afterSorry.TrimEnd()
        if ($trimmedAfter) {
            $lastIdx = $remainingLines.Count - 1
            $remainingLines[$lastIdx] = "$($remainingLines[$lastIdx])$afterSorry"
        }

        # 元の行を置換 + 後続行を挿入
        $newLines = [System.Collections.ArrayList]::new()
        for ($i = 0; $i -lt $lines.Count; $i++) {
            if ($i -eq $lineIdx) {
                $null = $newLines.Add($firstLine)
                foreach ($rl in $remainingLines) {
                    $null = $newLines.Add($rl)
                }
            } else {
                $null = $newLines.Add($lines[$i])
            }
        }
        $lines = $newLines.ToArray()
    }
}

# --- プレビュー ---

$resultContent = $lines -join "`n"

# 変更部分の前後 3 行を表示
$startPreview = [Math]::Max(0, $lineIdx - 2)
$endPreview = [Math]::Min($lines.Count - 1, $lineIdx + $proofLines.Count + 1)
Write-Info "--- 置換結果プレビュー (L$($startPreview + 1)-L$($endPreview + 1)) ---"
for ($i = $startPreview; $i -le $endPreview; $i++) {
    $marker = if ($i -ge $lineIdx -and $i -lt $lineIdx + $proofLines.Count) { ">" } else { " " }
    Write-Host "$marker L$($i + 1): $($lines[$i])"
}
Write-Info "--- プレビュー終了 ---"

# --- ファイル書き込み ---

if ($DryRun) {
    Write-Warn "DryRun: ファイルは変更しません"
} else {
    [System.IO.File]::WriteAllText($absFile, $resultContent, (New-Object System.Text.UTF8Encoding $false))
    Write-Ok "移植完了: $File L$Line の sorry を置換しました ($($proofLines.Count) 行)"
}

# --- simp 安定化 ---

if ($SimpStabilize -and -not $DryRun) {
    $simpScript = Join-Path $PSScriptRoot "../../lean-simp-guide/scripts/simp-stabilize.ps1"
    if (Test-Path $simpScript) {
        Write-Info "simp-stabilize.ps1 を chain 実行します..."
        & $simpScript -File $File
        if ($LASTEXITCODE -ne 0) {
            Write-Warn "simp-stabilize.ps1 が失敗しました (exit code: $LASTEXITCODE)"
            Write-Warn "手動で bare simp を確認してください"
        }
    } else {
        Write-Warn "simp-stabilize.ps1 が見つかりません: $simpScript"
        Write-Warn "手動で bare simp → simp only を実行してください"
    }
} elseif ($SimpStabilize -and $DryRun) {
    Write-Warn "DryRun: simp-stabilize.ps1 はスキップします"
}
