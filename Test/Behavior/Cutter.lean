-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- Cutter (切断) のユニットテスト
import S2IL.Operations.Cutter.Cutter

-- ============================================================
-- テスト用データ
-- ============================================================

private def emptyLayer : Layer := Layer.mk .empty .empty .empty .empty

-- 象限の略記
private def Cr := Quarter.colored .circle .red
private def Cg := Quarter.colored .circle .green
private def Cb := Quarter.colored .circle .blue
private def Rr := Quarter.colored .rectangle .red
private def Rg := Quarter.colored .rectangle .green
private def Sb := Quarter.colored .star .blue
private def Wu := Quarter.colored .windmill .uncolored
private def cr := Quarter.crystal .red
private def cg := Quarter.crystal .green
private def cb := Quarter.crystal .blue
private def cu := Quarter.crystal .uncolored
private def P  := Quarter.pin
private def E  := Quarter.empty

-- ============================================================
-- Layer.eastHalf / westHalf
-- ============================================================

-- eastHalf: 東側 (NE, SE) を維持、西側を空にする
#guard (Layer.mk Cr Rg Sb Wu).eastHalf == Layer.mk Cr Rg E E
#guard (Layer.mk E E Sb Wu).eastHalf == emptyLayer
#guard emptyLayer.eastHalf == emptyLayer

-- westHalf: 西側 (SW, NW) を維持、東側を空にする
#guard (Layer.mk Cr Rg Sb Wu).westHalf == Layer.mk E E Sb Wu
#guard (Layer.mk Cr Rg E E).westHalf == emptyLayer
#guard emptyLayer.westHalf == emptyLayer

-- combineEastWest: 東側と西側を合成
#guard Layer.combineEastWest (Layer.mk Cr Rg E E) (Layer.mk E E Sb Wu) == Layer.mk Cr Rg Sb Wu
#guard Layer.combineEastWest emptyLayer emptyLayer == emptyLayer

-- eastHalf + westHalf = 元のレイヤ
#guard Layer.combineEastWest (Layer.mk Cr Rg Sb Wu).eastHalf (Layer.mk Cr Rg Sb Wu).westHalf == Layer.mk Cr Rg Sb Wu

-- ============================================================
-- Shape.eastHalf / westHalf
-- ============================================================

-- 1レイヤ: 東側抽出
#guard (Shape.single (Layer.mk Cr Rg Sb Wu)).eastHalf ==
    Shape.single (Layer.mk Cr Rg E E)

-- 1レイヤ: 西側抽出
#guard (Shape.single (Layer.mk Cr Rg Sb Wu)).westHalf ==
    Shape.single (Layer.mk E E Sb Wu)

-- 2レイヤ: 各レイヤから東側抽出
#guard (Shape.double (Layer.mk Cr Rg Sb Wu) (Layer.mk cr cg cb cu)).eastHalf ==
    Shape.double (Layer.mk Cr Rg E E) (Layer.mk cr cg E E)

-- 2レイヤ: 各レイヤから西側抽出
#guard (Shape.double (Layer.mk Cr Rg Sb Wu) (Layer.mk cr cg cb cu)).westHalf ==
    Shape.double (Layer.mk E E Sb Wu) (Layer.mk E E cb cu)

-- ============================================================
-- halfDestroy: 切断処理機
-- ============================================================

/-- halfDestroy テストヘルパー -/
private def halfDestroyTest (inputCode expected : String) : Bool :=
    match Shape.ofString? inputCode with
    | none => false
    | some s =>
        match s.halfDestroy with
        | none => false
        | some result => result.toString == expected

/-- halfDestroy が none になることを検証するヘルパー -/
private def halfDestroyNone (inputCode : String) : Bool :=
    match Shape.ofString? inputCode with
    | none => false
    | some s => s.halfDestroy.isNone

-- 基本テスト: 全象限が非結晶 → 砕け散りなし → 東側抽出
-- "CrRgSbWu" → "CrRg----"
#guard halfDestroyTest "CrRgSbWu" "CrRg----"

-- 東側のみ → そのまま出力
-- "CrRg----" → "CrRg----"
#guard halfDestroyTest "CrRg----" "CrRg----"

-- 西側のみ → 全空 → none
-- "----SbWu" → none
#guard halfDestroyNone "----SbWu"

-- 2レイヤ: 通常パーツのみ
-- "CrRgSbWu:RrRrRrRr" → "CrRg----:RrRr----"
#guard halfDestroyTest "CrRgSbWu:RrRrRrRr" "CrRg----:RrRr----"

-- 結晶砕け散り: 東西跨ぎクラスタ → 砕け散り後に東側抽出
-- "crcrcrcr" → 全砕け → "--------" → 東側=空 → none
#guard halfDestroyNone "crcrcrcr"

-- 部分砕け散り: "crRgSbcr" → 砕け散り後 "--RgSb--" → 東側 "--Rg----"
#guard halfDestroyTest "crRgSbcr" "--Rg----"

-- CrystalBond修正後: "crcrcgcg" → SE(cr)-SW(cg)が色不問で結合 → 全砕け → 東側=空 → none
#guard halfDestroyNone "crcrcgcg"

-- 砕けない結晶(東側のみ): "crcr----" → 東側 "crcr----"
#guard halfDestroyTest "crcr----" "crcr----"

-- 落下テスト: 上層が浮く場合
-- "CrCr----:----SbWu" → 切断砕け散りなし → 東側 "CrCr----:--------"
--   L2 は全空 → 正規化で除去 → "CrCr----"
-- ただし L2 の東側は空なので正規化される
#guard halfDestroyTest "CrCr----:----SbWu" "CrCr----"

-- 結晶砕け散り + 落下: 東西跨ぎ結晶の上に通常パーツ
-- "crcrcrcr:RrRrRrRr" → 砕け散り "--------:RrRrRrRr"
--   → 東側 "--------:RrRr----" → 浮遊 {L2:NE(Rr), L2:SE(Rr)} → 落下
--   → "RrRr----"
#guard halfDestroyTest "crcrcrcr:RrRrRrRr" "RrRr----"

-- ============================================================
-- cut: 切断機
-- ============================================================

/-- cut テストヘルパー。east と west を文字列比較 -/
private def cutTest (inputCode expectedEast expectedWest : String) : Bool :=
    match Shape.ofString? inputCode with
    | none => false
    | some s =>
        let (east, west) := s.cut
        let eastOk := match east with
            | some r => r.toString == expectedEast
            | none => false
        let westOk := match west with
            | some r => r.toString == expectedWest
            | none => false
        eastOk && westOk

/-- 片側が none になるケースのテストヘルパー -/
private def cutTestEastOnly (inputCode expectedEast : String) : Bool :=
    match Shape.ofString? inputCode with
    | none => false
    | some s =>
        let (east, west) := s.cut
        let eastOk := match east with
            | some r => r.toString == expectedEast
            | none => false
        eastOk && west.isNone

private def cutTestWestOnly (inputCode expectedWest : String) : Bool :=
    match Shape.ofString? inputCode with
    | none => false
    | some s =>
        let (east, west) := s.cut
        let westOk := match west with
            | some r => r.toString == expectedWest
            | none => false
        east.isNone && westOk

-- 基本テスト: 通常パーツのみ
-- "CrRgSbWu" → 東 "CrRg----", 西 "----SbWu"
#guard cutTest "CrRgSbWu" "CrRg----" "----SbWu"

-- 東側のみ → 東あり、西 none
#guard cutTestEastOnly "CrRg----" "CrRg----"

-- 西側のみ → 東 none、西あり
#guard cutTestWestOnly "----SbWu" "----SbWu"

-- 2レイヤ通常パーツ
-- "CrRgSbWu:RrRrRrRr" → 東 "CrRg----:RrRr----", 西 "----SbWu:----RrRr"
#guard cutTest "CrRgSbWu:RrRrRrRr" "CrRg----:RrRr----" "----SbWu:----RrRr"

-- 結晶砕け散り: 東西跨ぎ → 全砕け → 両方 none
-- "crcrcrcr" → 砕け散り "--------" → 両方空 → (none, none)
private def cutBothNone (inputCode : String) : Bool :=
    match Shape.ofString? inputCode with
    | none => false
    | some s =>
        let (east, west) := s.cut
        east.isNone && west.isNone

#guard cutBothNone "crcrcrcr"

-- CrystalBond修正後: "crcrcgcg" → SE(cr)-SW(cg)が色不問で結合 → 全砕け → 両方 none
#guard cutBothNone "crcrcgcg"

-- 部分砕け: "crRgSbcr" → "--RgSb--" → 東 "--Rg----", 西 "----Sb--"
#guard cutTest "crRgSbcr" "--Rg----" "----Sb--"

-- 結晶 + 落下: "crcrcrcr:RrRrRrRr" → 砕け散り "--------:RrRrRrRr"
--   東 "--------:RrRr----" → 浮遊 → 落下 → "RrRr----"
--   西 "--------:----RrRr" → 浮遊 → 落下 → "----RrRr"
#guard cutTest "crcrcrcr:RrRrRrRr" "RrRr----" "----RrRr"

-- ============================================================
-- cut: 落下を伴うテスト
-- ============================================================

-- 落下テスト: 上層が浮く場合
-- "CrRg----:----SbWu" → 砕け散りなし
--   東 "CrRg----:--------" → 正規化 "CrRg----"
--   西 "--------:----SbWu" → 浮遊 → 落下 → "----SbWu"
#guard cutTest "CrRg----:----SbWu" "CrRg----" "----SbWu"

-- ============================================================
-- cut: 結晶の落下前砕け散り
-- ============================================================

-- "Cr--cr--:--Rg--cr" → shatterOnCut: crがクラスタ {L1:SW(cr)}(西のみ), {L2:NW(cr)}(西のみ)
--   → 東西跨ぎなし → 砕け散りなし
--   東側: "Cr------:--Rg----" → Rg が浮遊 → Rg 落下 → "CrRg----"
--   西側: "----cr--:------cr" → cr(L1:SW) は接地、cr(L2:NW) は L1:NW が空で浮遊
--     → shatterOnFall: L2:NW(cr) が脆弱 → クラスタ判定: L2:NW は独立クラスタ → 砕ける
--     → "----cr--:--------" → 正規化 → "----cr--"
#guard cutTest "Cr--cr--:--Rg--cr" "CrRg----" "----cr--"

-- ============================================================
-- swap: スワップ機
-- ============================================================

/-- swap テストヘルパー -/
private def swapTest (code1 code2 expected1 expected2 : String) : Bool :=
    match Shape.ofString? code1, Shape.ofString? code2 with
    | some s1, some s2 =>
        let (r1, r2) := s1.swap s2
        let ok1 := match r1 with
            | some r => r.toString == expected1
            | none => false
        let ok2 := match r2 with
            | some r => r.toString == expected2
            | none => false
        ok1 && ok2
    | _, _ => false

-- 基本テスト: 通常パーツのみ、西側入れ替え
-- s1="CrRgSbWu", s2="RrRrRrRr"
-- 砕け散りなし, 安定化でも変化なし
-- settled1 → "CrRgSbWu", settled2 → "RrRrRrRr"
-- swap: result1 = east(s1) + west(s2) = "CrRg----" + "----RrRr" = "CrRgRrRr"
--        result2 = east(s2) + west(s1) = "RrRr----" + "----SbWu" = "RrRrSbWu"
#guard swapTest "CrRgSbWu" "RrRrRrRr" "CrRgRrRr" "RrRrSbWu"

-- 同一シェイプ → 結果は同じ
-- s1=s2="CrRgSbWu" → swap → 両方とも "CrRgSbWu"
#guard swapTest "CrRgSbWu" "CrRgSbWu" "CrRgSbWu" "CrRgSbWu"

-- 東側のみのシェイプとスワップ
-- s1="CrRg----", s2="----SbWu"
-- settled1 "CrRg----", settled2 "----SbWu"
-- result1 = east(s1) + west(s2) = "CrRg----" + "----SbWu" = "CrRgSbWu"
-- result2 = east(s2) + west(s1) = "--------" + "--------" = empty → none
private def swapTestOneNone (code1 code2 expected1 : String) : Bool :=
    match Shape.ofString? code1, Shape.ofString? code2 with
    | some s1, some s2 =>
        let (r1, r2) := s1.swap s2
        let ok1 := match r1 with
            | some r => r.toString == expected1
            | none => false
        ok1 && r2.isNone
    | _, _ => false

#guard swapTestOneNone "CrRg----" "----SbWu" "CrRgSbWu"

-- 結晶砕け散り + スワップ
-- s1="crcrcrcr" (全砕け) → settled1=none
-- s2="CrRgSbWu" (砕け散りなし) → settled2=some "CrRgSbWu"
-- → result1=none (s1が全空), result2=east(s2)のみ → "CrRg----"
private def swapBothTest (code1 code2 : String)
        (expected1 expected2 : Option String) : Bool :=
    match Shape.ofString? code1, Shape.ofString? code2 with
    | some s1, some s2 =>
        let (r1, r2) := s1.swap s2
        let ok1 := match r1, expected1 with
            | some r, some e => r.toString == e
            | none, none => true
            | _, _ => false
        let ok2 := match r2, expected2 with
            | some r, some e => r.toString == e
            | none, none => true
            | _, _ => false
        ok1 && ok2
    | _, _ => false

#guard swapBothTest "crcrcrcr" "CrRgSbWu" none (some "CrRg----")

-- 両方全砕け → 両方 none
#guard swapBothTest "crcrcrcr" "crcrcrcr" none none

-- ============================================================
-- swap: 結晶が維持されるケース
-- ============================================================

-- 結晶結合が破壊されないスワップ
-- s1="crcr----" (東側のみ結晶), s2="----cgcg" (西側のみ結晶)
-- 砕け散りなし → 安定化変化なし
-- swap: result1 = east(s1) + west(s2) = "crcr----" + "----cgcg" = "crcrcgcg"
--        result2 = east(s2) + west(s1) = "--------" + "--------" → none
#guard swapBothTest "crcr----" "----cgcg" (some "crcrcgcg") none

-- ============================================================
-- 2レイヤのスワップ
-- ============================================================

-- s1="CrCrSbSb:RrRrRrRr", s2="CgCgWuWu:SbSbSbSb"
-- 砕け散りなし
-- settled1="CrCrSbSb:RrRrRrRr", settled2="CgCgWuWu:SbSbSbSb"
-- result1= east(s1)+west(s2) = "CrCr----:RrRr----" + "----WuWu:----SbSb" = "CrCrWuWu:RrRrSbSb"
-- result2= east(s2)+west(s1) = "CgCg----:SbSb----" + "----SbSb:----RrRr" = "CgCgSbSb:SbSbRrRr"
#guard swapTest "CrCrSbSb:RrRrRrRr" "CgCgWuWu:SbSbSbSb" "CrCrWuWu:RrRrSbSb" "CgCgSbSb:SbSbRrRr"

-- ============================================================
-- halfDestroy = cut の東側出力
-- ============================================================

-- halfDestroy と cut.1 の一致確認
private def halfDestroyCutConsistency (inputCode : String) : Bool :=
    match Shape.ofString? inputCode with
    | none => false
    | some s =>
        s.halfDestroy == s.cut.1

#guard halfDestroyCutConsistency "CrRgSbWu"
#guard halfDestroyCutConsistency "crcrcrcr"
#guard halfDestroyCutConsistency "crcrcgcg"
#guard halfDestroyCutConsistency "crRgSbcr"
#guard halfDestroyCutConsistency "CrRgSbWu:RrRrRrRr"
#guard halfDestroyCutConsistency "crcrcrcr:RrRrRrRr"

-- ============================================================
-- 180° 回転と cut の可換性テスト
-- ============================================================

-- 180° 回転後に cut すると、東西が入れ替わる
private def cutRotateComm (inputCode : String) : Bool :=
    match Shape.ofString? inputCode with
    | none => false
    | some s =>
        let (east, west) := s.cut
        let (east180, west180) := s.rotate180.cut
        -- s.cut.east.rotate180 == s.rotate180.cut.west
        -- s.cut.west.rotate180 == s.rotate180.cut.east
        let ok1 := match east.map Shape.rotate180, west180 with
            | some a, some b => a == b
            | none, none => true
            | _, _ => false
        let ok2 := match west.map Shape.rotate180, east180 with
            | some a, some b => a == b
            | none, none => true
            | _, _ => false
        ok1 && ok2

#guard cutRotateComm "CrRgSbWu"
#guard cutRotateComm "CrRg----"
#guard cutRotateComm "----SbWu"
#guard cutRotateComm "crcrcgcg"
#guard cutRotateComm "CrRgSbWu:RrRrRrRr"

-- ============================================================
-- 結晶の砕け散り + 落下の複合テスト
-- ============================================================

-- 2レイヤ: 下層に東西跨ぎ結晶、上層に通常パーツ
-- "crcrcrcr:CrRgSbWu" → 砕け散り "--------:CrRgSbWu"
--   東側: "--------:CrRg----" → 浮遊 → 落下 → "CrRg----"
--   西側: "--------:----SbWu" → 浮遊 → 落下 → "----SbWu"
#guard cutTest "crcrcrcr:CrRgSbWu" "CrRg----" "----SbWu"

-- 砕け散りで片方のみ結晶消失 + 落下
-- "CrcgcgWu:--RgRg--" → SE(cg)-SW(cg) 東西跨ぎ → "Cr----Wu:--RgRg--"
--   東側: "Cr------:--Rg----" → Rg接地(真下Cr無し→L2:SE直下L1:SEは空→浮遊)
--          → 浮遊 {L2:SE(Rg)} → 砕け散りなし(非脆弱) → gravity → "CrRg----"
--   西側: "------Wu:------Rg" → L1:NW(Wu)接地, L2:NW(Rg), L1→L2垂直接触 → 接地
--          → 変化なし → "------Wu:------Rg"
#guard cutTest "CrcgcgWu:--RgRg--" "CrRg----" "----RgWu"

-- ============================================================
-- ピン関連のテスト
-- ============================================================

-- ピンのみのシェイプ: "P-P-P-P-" → 東 "P-P-----", 西 "----P-P-"
-- ピンは接地（L0）
#guard cutTest "P-P-P-P-" "P-P-----" "----P-P-"

-- ピン + 上層パーツ: "P-------:Cr------"
-- 東側: "P-------:Cr------" (ピン経由で接地) → 変化なし
-- 西側: "--------:--------" → none
#guard cutTestEastOnly "P-------:Cr------" "P-------:Cr------"
