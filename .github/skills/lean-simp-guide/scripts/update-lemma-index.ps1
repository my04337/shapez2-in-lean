#!/usr/bin/env pwsh
# SPDX-FileCopyrightText: 2026 my04337
# SPDX-License-Identifier: MIT
#
# update-lemma-index.ps1 — s2il-lemma-index.md の行番号を自動更新する
#
# 使い方:
#   .github/skills/lean-simp-guide/scripts/update-lemma-index.ps1
#   .github/skills/lean-simp-guide/scripts/update-lemma-index.ps1 -DryRun
#
# 処理:
#   - Gravity.lean 内の主要定義・定理の行番号を grep で取得
#   - s2il-lemma-index.md のファイル構造マップと主要定理一覧の行番号を更新
#   - ファイル行数と sorry/warning 数も更新

[CmdletBinding()]
param(
    [switch]$DryRun
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"
[Console]::OutputEncoding = [System.Text.Encoding]::UTF8

$gravityFile = "S2IL/Behavior/Gravity.lean"
$indexFile   = "docs/s2il/s2il-lemma-index.md"

if (-not (Test-Path $gravityFile)) {
    Write-Error "Gravity.lean が見つかりません: $gravityFile"
    exit 1
}

if (-not (Test-Path $indexFile)) {
    Write-Error "補題インデックスが見つかりません: $indexFile"
    exit 1
}

# --- Gravity.lean の解析 ---

$gravityContent = Get-Content $gravityFile
$totalLines = $gravityContent.Count

# 定理・定義の行番号を取得
function Find-Line([string]$pattern) {
    $result = Select-String -Path $gravityFile -Pattern $pattern | Select-Object -First 1
    if ($result) { return $result.LineNumber }
    return $null
}

# ファイル構造マップのアンカー定義（セクション先頭のキーワード）
$anchors = @(
    @{ pattern = '^def isStructurallyBonded\b';           name = "構造結合" }
    @{ pattern = '^def structuralBfs\b';                   name = "構造クラスタの算出" }
    @{ pattern = '^def allIsolatedPins\b';                 name = "孤立ピンの列挙" }
    @{ pattern = '^def isGroundingContact\b';              name = "接地接触・接地 BFS" }
    @{ pattern = '^structure FallingUnit\b';               name = "落下単位" }
    @{ pattern = '^def shouldProcessBefore\b';             name = "ソート" }
    @{ pattern = '^def landingDistance\b';                  name = "着地位置の算出" }
    @{ pattern = '^def placeFallingUnit\b';                name = "障害物シェイプへの配置" }
    @{ pattern = '^def settle\b';                          name = "落下処理" }
    @{ pattern = '^private theorem isStructurallyBonded_rotate180\b'; name = "rotate180 基盤補題" }
    @{ pattern = '^private theorem dir_beq_rotate180''\b'; name = "BFS 等変性ヘルパー" }
    @{ pattern = '^private theorem structuralBfs_rotate180\b'; name = "structuralBfs" }
    @{ pattern = '^private theorem groundingBfs_rotate180\b'; name = "groundingBfs" }
    @{ pattern = 'structuralClusterList_rotate180_mapped'; name = "clusterList" }
    @{ pattern = '^private theorem ofLayers_rotate180\b';  name = "ofLayers" }
    @{ pattern = 'positions_rotate180';                    name = "FallingUnit r180" }
    @{ pattern = 'shouldProcessBefore_rotate180';          name = "spb / sortFU r180" }
    @{ pattern = '^private theorem insertSorted_perm\b';   name = "sortFU Perm" }
    @{ pattern = 'insertSorted_any_positions';             name = "sortFU 位置集合保存" }
    @{ pattern = '^private theorem structuralBfs_eq_generic\b'; name = "汎用 BFS" }
    @{ pattern = 'allValid_any_iff_layer''';               name = "BFS 健全性" }
    @{ pattern = 'groundedPositionsList_sound';            name = "groundedPositionsList 健全性" }
    @{ pattern = '^private theorem any_beq_iff_mem\b';     name = "any_beq_iff_mem" }
    @{ pattern = 'structuralCluster_rotate180';            name = "structuralCluster r180" }
    @{ pattern = 'mem_groundedPositions_rotate180';        name = "Finset メンバーシップ" }
    @{ pattern = 'ungrounded_nonempty_implies';            name = "floatingUnits 非空性" }
    @{ pattern = 'isGroundingContact_rotateCW';            name = "rotateCW 等変性" }
    @{ pattern = 'isOccupied_rotate180';                   name = "isOccupied r180" }
    @{ pattern = 'placeFallingUnit_rotate180';             name = "foldl_place r180" }
    @{ pattern = 'falling_positions_any_rotate180';        name = ".any メンバーシップ r180" }
    @{ pattern = 'settleStep_comm_ne_dir';                 name = "settleStep_comm_ne_dir" }
    @{ pattern = 'placeFallingUnit_ext\b';                 name = "placeFallingUnit_ext" }
    @{ pattern = 'tied_no_shared_dir';                     name = "tied 方角非共有" }
    @{ pattern = 'sortFU_pointwise_ext';                   name = "positions .any ext" }
    @{ pattern = 'foldl_eq_of_perm_tied_adj_comm';         name = "バブルソート帰納法" }
    @{ pattern = 'shouldProcessBefore_no_mutual';          name = "S-1" }
    @{ pattern = 'sortFU_output_inversion_dir_disjoint_r180'; name = "sortFU r180 反転" }
    @{ pattern = '^private theorem settle_foldl_eq\b';     name = "settle_foldl_eq 統合" }
    @{ pattern = '^theorem process_rotate180\b';           name = "process_rotate180" }
)

# 主要定理の行番号
$theorems = @(
    @{ pattern = 'theorem isStructurallyBonded_symm\b';   name = "isStructurallyBonded_symm" }
    @{ pattern = 'theorem isStructurallyBonded_rotate180\b'; name = "isStructurallyBonded_rotate180" }
    @{ pattern = 'theorem isGroundingContact_rotate180\b'; name = "isGroundingContact_rotate180" }
    @{ pattern = 'theorem structuralBfs_eq_generic\b';     name = "structuralBfs_eq_generic" }
    @{ pattern = 'theorem groundingBfs_eq_generic\b';      name = "groundingBfs_eq_generic" }
    @{ pattern = 'theorem allValid_any_iff_layer''';       name = "allValid_any_iff_layer'" }
    @{ pattern = 'theorem isGroundingContact_valid\b';     name = "isGroundingContact_valid" }
    @{ pattern = 'theorem isGroundingContact_valid_fst\b'; name = "isGroundingContact_valid_fst" }
    @{ pattern = 'theorem groundedPositionsList_sound\b';  name = "groundedPositionsList_sound" }
    @{ pattern = 'theorem groundedPositionsList_complete\b'; name = "groundedPositionsList_complete" }
    @{ pattern = 'theorem any_beq_iff_mem\b';              name = "any_beq_iff_mem" }
    @{ pattern = 'theorem structuralCluster_rotate180\b';  name = "structuralCluster_rotate180" }
    @{ pattern = 'theorem groundedPositions_rotate180\b';  name = "groundedPositions_rotate180" }
    @{ pattern = 'theorem ungrounded_nonempty_implies_floatingUnits_nonempty\b'; name = "ungrounded_nonempty_implies_floatingUnits_nonempty" }
    @{ pattern = 'theorem floatingUnits_nonempty_implies_exists_ungrounded\b'; name = "floatingUnits_nonempty_implies_exists_ungrounded" }
    @{ pattern = 'theorem floatingUnits_isEmpty_rotate180\b'; name = "floatingUnits_isEmpty_rotate180" }
    @{ pattern = 'theorem isGroundingContact_rotateCW\b';  name = "isGroundingContact_rotateCW" }
    @{ pattern = 'theorem groundedPositions_rotateCW\b';   name = "groundedPositions_rotateCW" }
    @{ pattern = 'theorem floatingUnits_isEmpty_rotateCW\b'; name = "floatingUnits_isEmpty_rotateCW" }
    @{ pattern = 'theorem falling_positions_any_rotate180\b'; name = "falling_positions_any_rotate180" }
    @{ pattern = 'theorem any_map_rotate180_beq\b';        name = "any_map_rotate180_beq" }
    @{ pattern = 'theorem process_rotate180\b';            name = "process_rotate180" }
    @{ pattern = 'theorem gravity_rotate180_comm\b';       name = "gravity_rotate180_comm" }
    @{ pattern = 'IsSettled_iff_isSettled\b';              name = "IsSettled_iff_isSettled" }
    @{ pattern = 'theorem IsSettled_rotate180\b';          name = "IsSettled_rotate180" }
    @{ pattern = 'theorem shouldProcessBefore_rotate180\b'; name = "shouldProcessBefore_rotate180" }
    @{ pattern = 'theorem sortFallingUnits_rotate180\b';   name = "sortFallingUnits_rotate180" }
    @{ pattern = 'theorem mem_groundedPositions_rotate180\b'; name = "mem_groundedPositions_rotate180" }
    @{ pattern = 'theorem mem_groundedPositions_rotateCW\b'; name = "mem_groundedPositions_rotateCW" }
    @{ pattern = 'theorem settleStep_comm_ne_dir\b';       name = "settleStep_comm_ne_dir" }
    @{ pattern = 'theorem foldl_eq_of_perm_tied_adj_comm\b'; name = "foldl_eq_of_perm_tied_adj_comm" }
    @{ pattern = 'theorem shouldProcessBefore_no_mutual\b'; name = "shouldProcessBefore_no_mutual" }
    @{ pattern = 'theorem sortFU_output_inversion_dir_disjoint_r180\b'; name = "sortFU_output_inversion_dir_disjoint_r180" }
)

Write-Host "Gravity.lean: $totalLines 行" -ForegroundColor Cyan

# 行番号の検出
$anchorLines = @{}
foreach ($a in $anchors) {
    $line = Find-Line $a.pattern
    if ($line) {
        $anchorLines[$a.name] = $line
        Write-Host "  $($a.name): L$line" -ForegroundColor DarkGray
    } else {
        Write-Host "  $($a.name): 未検出" -ForegroundColor Yellow
    }
}

$theoremLines = @{}
foreach ($t in $theorems) {
    $line = Find-Line $t.pattern
    if ($line) {
        $theoremLines[$t.name] = $line
    }
}

# sorry 数のカウント
$sorryCount = @(Select-String -Path $gravityFile -Pattern '\bsorry\b' |
    Where-Object { $_.Line -notmatch '^\s*--' }).Count

Write-Host "  sorry: $sorryCount 件" -ForegroundColor $(if ($sorryCount -gt 0) { "Yellow" } else { "Green" })

# --- s2il-lemma-index.md の更新 ---

$indexContent = [System.IO.File]::ReadAllText($indexFile, [System.Text.Encoding]::UTF8)

# ファイル行数の更新
$indexContent = $indexContent -replace '~[\d,]+\s*行', "~$($totalLines.ToString('N0')) 行"

# sorry/warning 数の更新（ビルド状態行）
$indexContent = $indexContent -replace 'sorries\s*=\s*\d+', "sorries = $sorryCount"

# 主要定理一覧の行番号更新
foreach ($name in $theoremLines.Keys) {
    $lineNum = $theoremLines[$name]
    # | 定理名 | L<old> | の形式で行番号を更新
    $escapedName = [regex]::Escape($name)
    $indexContent = $indexContent -replace "(\|\s*``$escapedName``\s*\|\s*)L\d+", "`${1}L$lineNum"
}

if ($DryRun) {
    Write-Host "`n[DryRun] 以下の変更が適用されます:" -ForegroundColor Yellow
    Write-Host "  ファイル行数: ~$($totalLines.ToString('N0')) 行"
    Write-Host "  sorry 数: $sorryCount"
    Write-Host "  定理行番号: $($theoremLines.Count) 件更新対象"
} else {
    [System.IO.File]::WriteAllText($indexFile, $indexContent, (New-Object System.Text.UTF8Encoding $false))
    Write-Host "`n補題インデックスを更新しました: $indexFile" -ForegroundColor Green
}
