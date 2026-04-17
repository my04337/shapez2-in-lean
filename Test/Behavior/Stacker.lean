-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- Stacker (積層機) のユニットテスト
import S2IL.Behavior.Stacker

-- ============================================================
-- テストヘルパー
-- ============================================================

private def emptyLayer : Layer := Layer.mk .empty .empty .empty .empty

/-- シェイプコードから積層し、結果を文字列比較するヘルパー（vanilla4）-/
private def stackTest (bottomCode topCode expected : String) : Bool :=
    match Shape.ofString? bottomCode, Shape.ofString? topCode with
    | some b, some t =>
        match Shape.stack b t GameConfig.vanilla4 with
        | some result => result.toString == expected
        | none => false
    | _, _ => false

/-- 積層結果が none になることを検証するヘルパー（vanilla4）-/
private def stackNone (bottomCode topCode : String) : Bool :=
    match Shape.ofString? bottomCode, Shape.ofString? topCode with
    | some b, some t =>
        (Shape.stack b t GameConfig.vanilla4).isNone
    | _, _ => false

-- ============================================================
-- placeAbove: 単純配置
-- ============================================================

-- 1レイヤ + 1レイヤ = 2レイヤ
#guard (Stacker.placeAbove
    (Shape.single (Layer.mk (.crystal .red) (.crystal .red) .empty .empty))
    (Shape.single (Layer.mk (.colored .rectangle .green) (.colored .rectangle .green) .empty .empty))
).layerCount == 2

-- 2レイヤ + 2レイヤ = 4レイヤ
#guard (Stacker.placeAbove
    (Shape.double
        (Layer.mk (.crystal .red) .empty .empty .empty)
        (Layer.mk (.crystal .blue) .empty .empty .empty))
    (Shape.double
        (Layer.mk (.colored .rectangle .green) .empty .empty .empty)
        (Layer.mk (.colored .star .blue) .empty .empty .empty))
).layerCount == 4

-- ============================================================
-- 基本積層: 結晶なし、上限内
-- ============================================================

-- 1レイヤ full + 1レイヤ full → 2レイヤ（落下なし）
#guard stackTest "CrCrCrCr" "RgRgRgRg" "CrCrCrCr:RgRgRgRg"

-- 1レイヤ partial + 1レイヤ partial → 落下して1レイヤになるケース
-- Cr--Cr-- + --Rg--Rg → 上側が落下して CrRgCrRg
#guard stackTest "Cr--Cr--" "--Rg--Rg" "CrRgCrRg"

-- 2レイヤ full + 1レイヤ full → 3レイヤ
#guard stackTest "CrCrCrCr:RgRgRgRg" "SbSbSbSb" "CrCrCrCr:RgRgRgRg:SbSbSbSb"

-- 1レイヤ + 1レイヤ同じ → 2レイヤ
#guard stackTest "Cr------" "Rg------" "Cr------:Rg------"

-- ============================================================
-- 上側結晶の砕け散り
-- ============================================================

-- 上側が全結晶 → 全消滅 → 下側のみ残る
#guard stackTest "CrCrCrCr" "crcrcrcr" "CrCrCrCr"

-- 上側の一部が結晶 → 結晶部分のみ消滅、残りが落下
-- Cr------ + crRg---- → 結晶消滅後 --Rg---- が落下 → CrRg----
-- ※ crは消えて--になり、Rgは(1,SE)にある。L0:SE は空なので落下して CrRg-----
#guard stackTest "Cr------" "--Rg----" "CrRg----"

-- 下側の結晶は影響されないことの確認
-- 下側が結晶でも砕けない
#guard stackTest "crcr----" "RgRg----" "crcr----:RgRg----"

-- 上側が全結晶で下側も全結晶 → 上だけ消滅、下は残る
#guard stackTest "crcrcrcr" "crcrcrcr" "crcrcrcr"

-- 上側のシェイプが砕けたことで分断された2クラスタがそれぞれ独立して落下すること
-- CuRucwcw:----SuWu の結晶(cw)消滅後 → {L2:NE(Cu),L2:SE(Ru)} は底側L1:NE(Cr)に接地
-- {L3:SW(Su),L3:NW(Wu)} は直下が全空 → L1 まで落下
#guard stackTest "Cr------" "CuRucwcw:----SuWu" "Cr--SuWu:CuRu----"

-- ============================================================
-- 落下連携: gravity との連携
-- ============================================================

-- 上側パーツが空象限を通り抜けて落下
-- -------- という空レイヤの下側 + Rg------ → Rg が layer 0 に落下
-- 注: ofString? は空レイヤを正規化して除去するため、直接構築する
private def emptyShape : Shape := Shape.single emptyLayer
-- ↑ ただし全空は ofString? で none になるので、少なくとも1つ非空が必要
-- 下側に空きがある場合: Cr------:-------- (L2空)
-- → ofString? では正規化されて 1レイヤになるので直接構築
private def bottomWithGap : Shape :=
    Shape.double (Layer.mk (.colored .circle .red) .empty .empty .empty) emptyLayer

-- L1:Cr, L2:空 + top:Rg → combined: Cr,空,Rg → 結晶なし → gravity
-- Rg は L3 にあり、L2 が空 → L1:NE(Cr)の直上 L2:NE は空 → Rg(NE)はL1に着地できない
-- L3:NE の直下 L2:NE は空 → さらに L1:NE(Cr) → L2 に着地
-- 結局: Cr------:Rg------
#guard (Shape.stack bottomWithGap (Shape.single (Layer.mk (.colored .rectangle .green) .empty .empty .empty)) GameConfig.vanilla4
    ).map Shape.toString
    == some "Cr------:Rg------"

-- 部分的な落下: 下側に穴があり上側パーツが部分的に落下
-- Cr------ + RgRg---- → L1:NE(Cr), L2:{NE(Rg),SE(Rg)}
-- Rg はクラスタ{L2:NE,L2:SE} → L2:NE の直下L1:NE(Cr) → 接地 → 落下しない
#guard stackTest "Cr------" "RgRg----" "Cr------:RgRg----"

-- 垂直構造結合が落下を防ぐケース（ゲーム内検証済み 2026-04-11）
-- B1: L1:SE(Cr)↔L2:SE(Rg) 垂直ボンド + L2:SW(Rg)↔L2:SE(Rg) 水平接地 → クラスタ全体接地→落下なし
#guard stackTest "CrCr----" "--RgRg--" "CrCr----:--RgRg--"

-- 垂直構造結合がないケース（ゲーム内検証済み 2026-04-11）
-- B2: L2:{SW(Rg),NW(Rg)} は L1:SW,NW ともに空 → 非接地→落下して L1 に合流
#guard stackTest "CrCr----" "----RgRg" "CrCrRgRg"

-- ============================================================
-- truncate: レイヤ上限超過（vanilla4 = 4レイヤ）
-- ============================================================

-- 3レイヤ + 2レイヤ = 5レイヤ → 4レイヤに切り詰め
#guard stackTest "CrCrCrCr:RgRgRgRg:SbSbSbSb" "WuWuWuWu:CyCyCyCy"
    "CrCrCrCr:RgRgRgRg:SbSbSbSb:WuWuWuWu"
-- ↑ L5(Cy) が truncate で廃棄され、4レイヤになるはず

-- 4レイヤ full + 1レイヤ → top は truncate で廃棄
#guard stackTest "CrCrCrCr:RgRgRgRg:SbSbSbSb:WuWuWuWu" "CyCyCyCy"
    "CrCrCrCr:RgRgRgRg:SbSbSbSb:WuWuWuWu"

-- ============================================================
-- truncate + 落下: 切り詰め後に落下が発生するケース
-- ============================================================

-- 下側3レイヤ（L3が部分空き） + 上側2レイヤ → 5レイヤになり truncate
-- L4 が残り、L5 が廃棄。L4 のパーツが落下する可能性
-- 直接構築で確認
private def bottom3partial : Shape :=
    Shape.triple
        (Layer.mk (.colored .circle .red) (.colored .circle .red)
                   (.colored .circle .red) (.colored .circle .red))
        (Layer.mk (.colored .rectangle .green) (.colored .rectangle .green)
                   (.colored .rectangle .green) (.colored .rectangle .green))
        (Layer.mk (.colored .star .blue) (.colored .star .blue) .empty .empty)

private def top2full : Shape :=
    Shape.double
        (Layer.mk (.colored .windmill .uncolored) (.colored .windmill .uncolored)
                   (.colored .windmill .uncolored) (.colored .windmill .uncolored))
        (Layer.mk (.colored .circle .yellow) (.colored .circle .yellow)
                   (.colored .circle .yellow) (.colored .circle .yellow))

-- combined = 5レイヤ: L1(Cr), L2(Rg), L3(Sb--), L4(Wu), L5(Cy)
-- 結晶なし → afterShatter = combined
-- gravity: L3 は SE,SW が Sb で NE,NW空 → L4 の Wu は:
--   L4:{NE,SE,SW,NW} → L3:NE 空, L3:SE(Sb) → 構造クラスタ全体が接地 → 落下しない
-- afterGravity = combined (5レイヤ)
-- truncate: maxLayers=4 → L5(Cy) 廃棄
-- truncated = 4レイヤ: L1(Cr), L2(Rg), L3(Sb--), L4(Wu)
-- 再gravity: 全て接地 → 変化なし
#guard (Shape.stack bottom3partial top2full GameConfig.vanilla4).map Shape.toString
    == some "CrCrCrCr:RgRgRgRg:SbSb----:WuWuWuWu"

-- ============================================================
-- ピンを含む積層
-- ============================================================

-- ピンは砕け散らない
#guard stackTest "Cr------" "P-------" "Cr------:P-------"

-- ピンは水平接地接触を伝播しないため、Rg は非接地で落下する
#guard stackTest "Cr------" "P-Rg----" "CrRg----:P-------"

-- ピンが部分的に落下：底面の空き象限（SW, NW）に落下（ゲーム内検証済み 2026-04-11）
-- bottom=CrCr----: NE,SE が Cr で SW,NW 空。top=P-P-P-P-: 全ピン
-- L2:NE(Pin)→L1:NE(Cr)垂直→接地。L2:SE(Pin)→L1:SE(Cr)垂直→接地
-- L2:SW(Pin) は L1:SW 空 → 非接地→落下。L2:NW(Pin) は L1:NW 空 → 非接地→落下
#guard stackTest "CrCr----" "P-P-P-P-" "CrCrP-P-:P-P-----"

-- ============================================================
-- エッジケース
-- ============================================================

-- 上側が全結晶の場合（全消滅後、下側のみ残る）
#guard stackTest "RgRgRgRg" "crcrcrcr" "RgRgRgRg"

-- L1:{ne:-,se:-,sw:Rg,nw:-} + L2:{ne:-,se:Sb,sw:-,nw:-}
-- L2:SE(Sb) の直下 L1:SE は空 → 非接地 → 落下して L1 に合流
#guard stackTest "----Rg--" "--Sb----" "--SbRg--"

-- 上側の一部が落下して下側に合流するケース
-- Cr------ + ----Rg-- → combined: L1(Cr------), L2(----Rg--)
-- gravity: L2:SW(Rg) → L1:SW 空 → 非接地 → 落下
-- d=1 で layer 0 到達 → Cr--Rg--
#guard stackTest "Cr------" "----Rg--" "Cr--Rg--"

-- 5レイヤモードのテスト（vanilla5）
-- テスト用に直接 vanilla5 を使用
private def stackV5 (bottomCode topCode : String) : Option String :=
    match Shape.ofString? bottomCode, Shape.ofString? topCode with
    | some b, some t =>
        (Shape.stack b t GameConfig.vanilla5).map Shape.toString
    | _, _ => none

-- 4レイヤ + 1レイヤ → 5レイヤに収まる（vanilla5 なら truncate 不要）
#guard stackV5 "CrCrCrCr:RgRgRgRg:SbSbSbSb:WuWuWuWu" "CyCyCyCy"
    == some "CrCrCrCr:RgRgRgRg:SbSbSbSb:WuWuWuWu:CyCyCyCy"

-- ============================================================
-- rotate180 等変性の検証（ゲーム内検証済み 2026-04-11）
-- stack(b, t).rotate180 = stack(b.rotate180, t.rotate180) を検証する
-- ============================================================

/-- stack(b, t).rotate180 = stack(b.rotate180, t.rotate180) を検証するヘルパー（vanilla4）-/
private def stackR180Test (bottomCode topCode : String) : Bool :=
    match Shape.ofString? bottomCode, Shape.ofString? topCode with
    | some b, some t =>
        match Shape.stack b t GameConfig.vanilla4,
              Shape.stack b.rotate180 t.rotate180 GameConfig.vanilla4 with
        | some r1, some r2 => r1.rotate180.toString == r2.toString
        | none, none => true
        | _, _ => false
    | _, _ => false

-- E1: 部分落下（垂直ボンドなし）
-- stack(CrCr----, ----RgRg) = CrCrRgRg → r180 = RgRgCrCr
-- stack(----CrCr, RgRg----) = RgRgCrCr ✓
#guard stackR180Test "CrCr----" "----RgRg"

-- E2: ピン落下（部分的ピン）
-- stack(CrCr----, P-P-P-P-) = CrCrP-P-:P-P----- → r180 = P-P-CrCr:----P-P-
-- stack(----CrCr, P-P-P-P-) = P-P-CrCr:----P-P- ✓
#guard stackR180Test "CrCr----" "P-P-P-P-"

-- E3: ピン水平遮断により Rg が落下
-- stack(Cr------, P-Rg----) = CrRg----:P------- → r180 = ----CrRg:----P---
-- stack(----Cr--, ----P-Rg) = ----CrRg:----P--- ✓
#guard stackR180Test "Cr------" "P-Rg----"

-- E4: settled ベース + 非対称 top（sorry #3 関連）
-- stack(P-P-P-P-:CrCrCrCr, SbSb----) = P-P-P-P-:CrCrCrCr:SbSb---- → r180 = P-P-P-P-:CrCrCrCr:----SbSb
-- P-P-P-P-:CrCrCrCr は r180 対称 → stack(P-P-P-P-:CrCrCrCr, ----SbSb) = P-P-P-P-:CrCrCrCr:----SbSb ✓
#guard stackR180Test "P-P-P-P-:CrCrCrCr" "SbSb----"

-- E5: 2レイヤ bottom + 非対称 top
-- stack(CrCr----:RgRg----, ----SbSb) = CrCrSbSb:RgRg---- → r180 = SbSbCrCr:----RgRg
-- stack(----CrCr:----RgRg, SbSb----) = SbSbCrCr:----RgRg ✓
#guard stackR180Test "CrCr----:RgRg----" "----SbSb"
