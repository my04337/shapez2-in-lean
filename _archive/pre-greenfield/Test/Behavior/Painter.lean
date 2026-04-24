-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- Painter (着色機) のユニットテスト
import S2IL.Operations.Painter.Painter

-- ============================================================
-- テストヘルパー
-- ============================================================

/-- シェイプコードから着色し、結果を文字列比較するヘルパー -/
private def paintTest (inputCode : String) (color : Color) (expected : String) : Bool :=
    match Shape.ofString? inputCode with
    | some s => (s.paint color).toString == expected
    | none => false

-- ============================================================
-- paintQuarter: 象限単位の着色
-- ============================================================

-- colored → 色が置換される
#guard Painter.paintQuarter (.colored .circle .uncolored) .red == Quarter.colored .circle .red
#guard Painter.paintQuarter (.colored .rectangle .green) .blue == Quarter.colored .rectangle .blue
#guard Painter.paintQuarter (.colored .star .red) .yellow == Quarter.colored .star .yellow
#guard Painter.paintQuarter (.colored .windmill .white) .cyan == Quarter.colored .windmill .cyan

-- 同じ色で上書き → 変化なし
#guard Painter.paintQuarter (.colored .circle .red) .red == Quarter.colored .circle .red

-- 空 → 変化なし
#guard Painter.paintQuarter .empty .red == Quarter.empty

-- ピン → 変化なし
#guard Painter.paintQuarter .pin .red == Quarter.pin

-- 結晶 → 変化なし
#guard Painter.paintQuarter (.crystal .red) .blue == Quarter.crystal .red
#guard Painter.paintQuarter (.crystal .green) .red == Quarter.crystal .green

-- ============================================================
-- 基本テスト: 1レイヤシェイプ
-- ============================================================

-- 全象限着色
-- CuCuCuCu + 赤 → CrCrCrCr
#guard paintTest "CuCuCuCu" .red "CrCrCrCr"

-- 部分着色（空象限は対象外）
-- CuCu---- + 赤 → CrCr----
#guard paintTest "CuCu----" .red "CrCr----"

-- 既存色の上書き
-- CrRgSbWu + 青 → CbRbSbWb
#guard paintTest "CrRgSbWu" .blue "CbRbSbWb"

-- ピン混在 → ピンは着色されない
-- CuP-Cu-- + 緑 → CgP-Cg--
#guard paintTest "CuP-Cu--" .green "CgP-Cg--"

-- 結晶混在 → 結晶は着色されない
-- CucrcuCu + 青 → CbcrCbCb

-- 全空 → 変化なし（直接構築）
private def emptyLayer : Layer := Layer.mk .empty .empty .empty .empty
#guard (Shape.single emptyLayer).paint .red == Shape.single emptyLayer

-- 全ピン → 変化なし
#guard paintTest "P-P-P-P-" .red "P-P-P-P-"

-- 全結晶 → 変化なし
#guard paintTest "crcrcrcr" .blue "crcrcrcr"

-- ============================================================
-- 2レイヤシェイプ（最上位レイヤのみ着色）
-- ============================================================

-- 最上位レイヤ（L2）のみ着色される
-- CuCu----:Ru------ + 赤 → CuCu----:Rr------
#guard paintTest "CuCu----:Ru------" .red "CuCu----:Rr------"

-- 下層は変更されない
-- CrCrCrCr:RgRgRgRg + 青 → CrCrCrCr:RbRbRbRb
#guard paintTest "CrCrCrCr:RgRgRgRg" .blue "CrCrCrCr:RbRbRbRb"

-- 最上位レイヤに空・ピンがある場合
-- CrCrCrCr:Ru--P--- + 緑 → CrCrCrCr:Rg--P---
#guard paintTest "CrCrCrCr:Ru--P---" .green "CrCrCrCr:Rg--P---"

-- ============================================================
-- 3レイヤ・4レイヤ
-- ============================================================

-- 3レイヤ: L3 のみ着色
-- CrCrCrCr:RgRgRgRg:SbSbSbSb + 黄 → CrCrCrCr:RgRgRgRg:SySySySy
#guard paintTest "CrCrCrCr:RgRgRgRg:SbSbSbSb" .yellow "CrCrCrCr:RgRgRgRg:SySySySy"

-- 4レイヤ: L4 のみ着色
-- CrCrCrCr:RgRgRgRg:SbSbSbSb:WuWuWuWu + マゼンタ → CrCrCrCr:RgRgRgRg:SbSbSbSb:WmWmWmWm
#guard paintTest "CrCrCrCr:RgRgRgRg:SbSbSbSb:WuWuWuWu" .magenta
    "CrCrCrCr:RgRgRgRg:SbSbSbSb:WmWmWmWm"

-- ============================================================
-- 連続着色（上書き）
-- ============================================================

-- 赤で着色 → 青で着色 → 最終的に青
private def doublePaint : Shape :=
    match Shape.ofString? "CuCuCuCu" with
    | some s => (s.paint .red).paint .blue
    | none => Shape.single emptyLayer

#guard doublePaint.toString == "CbCbCbCb"

-- ============================================================
-- 異なる色の液剤
-- ============================================================

#guard paintTest "CuCuCuCu" .red "CrCrCrCr"
#guard paintTest "CuCuCuCu" .green "CgCgCgCg"
#guard paintTest "CuCuCuCu" .blue "CbCbCbCb"
#guard paintTest "CuCuCuCu" .yellow "CyCyCyCy"
#guard paintTest "CuCuCuCu" .cyan "CcCcCcCc"
#guard paintTest "CuCuCuCu" .magenta "CmCmCmCm"
#guard paintTest "CuCuCuCu" .white "CwCwCwCw"
#guard paintTest "CuCuCuCu" .uncolored "CuCuCuCu"
