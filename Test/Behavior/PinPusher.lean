-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- PinPusher (ピン押し機) のユニットテスト
import S2IL.Operations.PinPusher.PinPusher

-- ============================================================
-- テストヘルパー
-- ============================================================

/-- シェイプコードからピン押しし、結果を文字列比較するヘルパー（vanilla4）-/
private def pinPushTest (inputCode expected : String) : Bool :=
    match Shape.ofString? inputCode with
    | some s =>
        match s.pinPush GameConfig.vanilla4 with
        | some result => result.toString == expected
        | none => false
    | none => false

/-- ピン押し結果が none になることを検証するヘルパー（vanilla4）-/
private def pinPushNone (inputCode : String) : Bool :=
    match Shape.ofString? inputCode with
    | some s =>
        (s.pinPush GameConfig.vanilla4).isNone
    | none => false

-- ============================================================
-- liftUp: レイヤ持ち上げ
-- ============================================================

-- 1レイヤ → 2レイヤ
#guard (PinPusher.liftUp (Shape.single (Layer.mk (.colored .circle .red) .empty .empty .empty))).layerCount == 2

-- 4レイヤ → 5レイヤ
#guard (PinPusher.liftUp (Shape.quadruple
    (Layer.mk (.colored .circle .red) (.colored .circle .red) (.colored .circle .red) (.colored .circle .red))
    (Layer.mk (.colored .rectangle .green) (.colored .rectangle .green) (.colored .rectangle .green) (.colored .rectangle .green))
    (Layer.mk (.colored .star .blue) (.colored .star .blue) (.colored .star .blue) (.colored .star .blue))
    (Layer.mk (.colored .windmill .uncolored) (.colored .windmill .uncolored) (.colored .windmill .uncolored) (.colored .windmill .uncolored))
)).layerCount == 5

-- ============================================================
-- 基本テスト: 1レイヤシェイプ
-- ============================================================

-- 全4象限非空 → 全象限にピン生成
-- CrCrCrCr → P-P-P-P-:CrCrCrCr
#guard pinPushTest "CrCrCrCr" "P-P-P-P-:CrCrCrCr"

-- 部分的に非空 → 非空象限のみにピン生成
-- CrRg---- → P-P-----:CrRg----
#guard pinPushTest "CrRg----" "P-P-----:CrRg----"

-- 1象限のみ非空
-- Cr------ → P-------:Cr------
#guard pinPushTest "Cr------" "P-------:Cr------"

-- 西側のみ非空
-- ----CrCr → ----P-P-:----CrCr
#guard pinPushTest "----CrCr" "----P-P-:----CrCr"

-- ============================================================
-- ピンを含むシェイプ
-- ============================================================

-- ピンは非空なので下にもピンが生成される
-- P------- → P-------:P-------
#guard pinPushTest "P-------" "P-------:P-------"

-- 全象限ピン → 全象限にピン生成
-- P-P-P-P- → P-P-P-P-:P-P-P-P-
#guard pinPushTest "P-P-P-P-" "P-P-P-P-:P-P-P-P-"

-- ============================================================
-- 結晶を含むシェイプ
-- ============================================================

-- 結晶は非空なので下にピンが生成される
-- crcr---- → P-P-----:crcr----
#guard pinPushTest "crcr----" "P-P-----:crcr----"

-- 全結晶 → 全象限にピン生成
-- crcrcrcr → P-P-P-P-:crcrcrcr
#guard pinPushTest "crcrcrcr" "P-P-P-P-:crcrcrcr"

-- ============================================================
-- 2レイヤシェイプ (上限内)
-- ============================================================

-- CrRg----:SbWu---- → P-P-----:CrRg----:SbWu----
#guard pinPushTest "CrRg----:SbWu----" "P-P-----:CrRg----:SbWu----"

-- CrCrCrCr:RgRgRgRg → P-P-P-P-:CrCrCrCr:RgRgRgRg
#guard pinPushTest "CrCrCrCr:RgRgRgRg" "P-P-P-P-:CrCrCrCr:RgRgRgRg"

-- ============================================================
-- 3レイヤシェイプ (上限内、4レイヤに収まる)
-- ============================================================

-- CrCrCrCr:RgRgRgRg:SbSbSbSb → P-P-P-P-:CrCrCrCr:RgRgRgRg:SbSbSbSb
#guard pinPushTest "CrCrCrCr:RgRgRgRg:SbSbSbSb" "P-P-P-P-:CrCrCrCr:RgRgRgRg:SbSbSbSb"

-- ============================================================
-- 4レイヤシェイプ (上限超過: truncation)
-- ============================================================

-- 全4レイヤ非結晶 → L5(最上位)が廃棄される
-- CrCrCrCr:RgRgRgRg:SbSbSbSb:WuWuWuWu → P-P-P-P-:CrCrCrCr:RgRgRgRg:SbSbSbSb
#guard pinPushTest "CrCrCrCr:RgRgRgRg:SbSbSbSb:WuWuWuWu" "P-P-P-P-:CrCrCrCr:RgRgRgRg:SbSbSbSb"

-- 最上位が結晶 → 砕け散り後にtruncate
-- CrCrCrCr:RgRgRgRg:SbSbSbSb:crcrcrcr → P-P-P-P-:CrCrCrCr:RgRgRgRg:SbSbSbSb
#guard pinPushTest "CrCrCrCr:RgRgRgRg:SbSbSbSb:crcrcrcr" "P-P-P-P-:CrCrCrCr:RgRgRgRg:SbSbSbSb"

-- 全4レイヤ結晶 → ピン押し後に全て砕け散る → ピンのみの1レイヤに → P-P-P-P-
-- crcrcrcr:cgcgcgcg:cbcbcbcb:cwcwcwcw → P-P-P-P-
#guard pinPushTest "crcrcrcr:cgcgcgcg:cbcbcbcb:cwcwcwcw" "P-P-P-P-"

-- ============================================================
-- 結晶のクロスレイヤ結合 + truncation
-- ============================================================

-- L3:cgcgcgcg と L4:crcrcrcr が上下レイヤ間で結合
-- → ピン押し後、L4(index 3)とL5(index 4)が1クラスタとして砕け散る
-- CrCrCrCr:CrCrCrCr:cgcgcgcg:crcrcrcr → P-P-P-P-:CrCrCrCr:CrCrCrCr
#guard pinPushTest "CrCrCrCr:CrCrCrCr:cgcgcgcg:crcrcrcr" "P-P-P-P-:CrCrCrCr:CrCrCrCr"

-- ============================================================
-- truncation + 落下
-- ============================================================

-- 結晶砕け散りにより支えを失った塊が落下するケース
-- CrCr----:----SbSb:cgcg----:crcrcrcr
-- L3:NE(cg),SE(cg) と L4:全(cr) → 上下結合で1クラスタ → L4超過で砕け散る
-- L3(index 2)のSbSbが浮遊して落下 → L1(index 0)に着地
-- 結果: P-P-SbSb:CrCr----
#guard pinPushTest "CrCr----:----SbSb:cgcg----:crcrcrcr" "P-P-SbSb:CrCr----"

-- ============================================================
-- ゲーム実機検証テスト (結晶結合色不問修正の検証)
-- ============================================================

-- テストG: 異色結晶の連鎖 shatter
-- L0:CrCr, L1:cr(NE)cg(SE), L2:cr(NE), L3:cr(NE)
-- PinPush 後 5L → shatterOnTruncate で L4(超過) の cr が砕け散り
-- 色不問のため (2,SE)=cg も (2,NE)=cr と同クラスタ → 連鎖消滅
-- ゲーム結果: P-P-----:CrCr----
#guard pinPushTest "CrCr----:crcg----:cr------:cr------" "P-P-----:CrCr----"

-- ============================================================
-- 5レイヤモードのテスト
-- ============================================================

private def pinPushV5 (inputCode : String) : Option String :=
    match Shape.ofString? inputCode with
    | some s =>
        (s.pinPush GameConfig.vanilla5).map Shape.toString
    | none => none

-- 4レイヤ → 5レイヤに収まる（vanilla5 なら truncate 不要）
#guard pinPushV5 "CrCrCrCr:RgRgRgRg:SbSbSbSb:WuWuWuWu"
    == some "P-P-P-P-:CrCrCrCr:RgRgRgRg:SbSbSbSb:WuWuWuWu"

-- ============================================================
-- エッジケース
-- ============================================================

-- 空の最下層を持つシェイプ → ピンは生成されない
-- --------:CrRg---- → --------:--------:CrRg----
#guard pinPushTest "--------:CrRg----" "--------:--------:CrRg----"

-- 部分的に空の最下層
-- Cr--Rg-- → P---P---:Cr--Rg--
#guard pinPushTest "Cr--Rg--" "P---P---:Cr--Rg--"
