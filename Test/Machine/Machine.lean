-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- Machine (加工装置ラッパー) のユニットテスト
import S2IL.Machine.Machine

-- ============================================================
-- テストヘルパー
-- ============================================================

/-- シェイプコードをパースして Option Shape にするヘルパー -/
private def s (code : String) : Option Shape := Shape.ofString? code

/-- Machine.paint の結果を文字列比較するヘルパー -/
private def mpaintTest (shapeCode : String) (color : Color) (expected : String) : Bool :=
    match Machine.paint (s shapeCode) (some color) with
    | some result => result.toString == expected
    | none => false

/-- Machine.crystallize の結果を文字列比較するヘルパー -/
private def mcrystallizeTest (shapeCode : String) (color : Color) (expected : String) : Bool :=
    match Machine.crystallize (s shapeCode) (some color) with
    | some result => result.toString == expected
    | none => false

/-- Machine.rotateCW の結果を文字列比較するヘルパー -/
private def mrotateCWTest (shapeCode expected : String) : Bool :=
    match Machine.rotateCW (s shapeCode) with
    | some result => result.toString == expected
    | none => false

/-- Machine.pinPush の結果を文字列比較するヘルパー（vanilla4）-/
private def mpinPushTest (shapeCode expected : String) : Bool :=
    match Machine.pinPush (s shapeCode) GameConfig.vanilla4 with
    | some result => result.toString == expected
    | none => false

/-- Machine.stack の結果を文字列比較するヘルパー（vanilla4）-/
private def mstackTest (bottomCode topCode expected : String) : Bool :=
    match Machine.stack (s bottomCode) (s topCode) GameConfig.vanilla4 with
    | some result => result.toString == expected
    | none => false

-- ############################################################
-- 入力欠落テスト: 入力が揃っていない場合は none を返す
-- ############################################################

-- ============================================================
-- 着色機: 入力欠落
-- ============================================================

-- シェイプなし、色あり → none
#guard (Machine.paint none (some Color.red)).isNone

-- シェイプあり、色なし → none
#guard (Machine.paint (s "CuCuCuCu") none).isNone

-- 両方なし → none
#guard (Machine.paint none none).isNone

-- ============================================================
-- 結晶製造機: 入力欠落
-- ============================================================

-- シェイプなし、色あり → none
#guard (Machine.crystallize none (some Color.red)).isNone

-- シェイプあり、色なし → none
#guard (Machine.crystallize (s "CuCuCuCu") none).isNone

-- 両方なし → none
#guard (Machine.crystallize none none).isNone

-- ============================================================
-- 回転機: 入力欠落
-- ============================================================

-- CW: 入力なし → none
#guard (Machine.rotateCW none).isNone

-- CCW: 入力なし → none
#guard (Machine.rotateCCW none).isNone

-- 180°: 入力なし → none
#guard (Machine.rotate180 none).isNone

-- ============================================================
-- ピン押し機: 入力欠落
-- ============================================================

-- 入力なし → none
#guard (Machine.pinPush none GameConfig.vanilla4).isNone

-- ============================================================
-- 積層機: 入力欠落
-- ============================================================

-- 下側なし、上側あり → none
#guard (Machine.stack none (s "CrCrCrCr") GameConfig.vanilla4).isNone

-- 下側あり、上側なし → none
#guard (Machine.stack (s "CrCrCrCr") none GameConfig.vanilla4).isNone

-- 両方なし → none
#guard (Machine.stack none none GameConfig.vanilla4).isNone

-- ############################################################
-- 入力有効テスト: コア関数と同じ結果を返す
-- ############################################################

-- ============================================================
-- 着色機: 有効入力
-- ============================================================

-- 基本着色
#guard mpaintTest "CuCuCuCu" .red "CrCrCrCr"

-- 部分着色
#guard mpaintTest "CuCu----" .blue "CbCb----"

-- 色の上書き
#guard mpaintTest "CrCrCrCr" .green "CgCgCgCg"

-- コア関数との等価性
#guard Machine.paint (s "CuCuCuCu") (some Color.red) ==
    (s "CuCuCuCu").map (·.paint .red)

-- ============================================================
-- 結晶製造機: 有効入力
-- ============================================================

-- 部分空シェイプに結晶充填
#guard mcrystallizeTest "CuCu----" .red "CuCucrcr"

-- 全ピンシェイプ → 全結晶
#guard mcrystallizeTest "P-P-P-P-" .red "crcrcrcr"

-- コア関数との等価性
#guard Machine.crystallize (s "CuCuCuCu") (some Color.red) ==
    (s "CuCuCuCu").map (·.crystallize .red)

#guard Machine.crystallize (s "P-P-P-P-") (some Color.blue) ==
    (s "P-P-P-P-").map (·.crystallize .blue)

-- ============================================================
-- 回転機: 有効入力
-- ============================================================

-- CW 回転
#guard mrotateCWTest "Cr------" "--Cr----"

-- コア関数との等価性 (CW)
#guard Machine.rotateCW (s "Cr------") ==
    (s "Cr------").map Shape.rotateCW

-- コア関数との等価性 (CCW)
#guard Machine.rotateCCW (s "Cr------") ==
    (s "Cr------").map Shape.rotateCCW

-- コア関数との等価性 (180°)
#guard Machine.rotate180 (s "Cr------") ==
    (s "Cr------").map Shape.rotate180

-- ============================================================
-- ピン押し機: 有効入力
-- ============================================================

-- 基本ピン押し
#guard mpinPushTest "CrCrCrCr" "P-P-P-P-:CrCrCrCr"

-- コア関数との等価性
#guard Machine.pinPush (s "CrCrCrCr") GameConfig.vanilla4 ==
    ((s "CrCrCrCr").bind (·.pinPush GameConfig.vanilla4))

-- ============================================================
-- 積層機: 有効入力
-- ============================================================

-- 基本積層
#guard mstackTest "CrCrCrCr" "RgRgRgRg" "CrCrCrCr:RgRgRgRg"

-- コア関数との等価性
#guard Machine.stack (s "CrCrCrCr") (s "RgRgRgRg") GameConfig.vanilla4 ==
    (match s "CrCrCrCr", s "RgRgRgRg" with
    | some b, some t => b.stack t GameConfig.vanilla4
    | _, _ => none)

-- ############################################################
-- No-op エッジケーステスト: 入力は有効だが結果が同じ
-- ############################################################

-- ============================================================
-- 着色機: no-op ケース
-- ============================================================

-- 全ピン層 → ピンは着色されないので入力と出力が同じ
#guard mpaintTest "P-P-P-P-" .red "P-P-P-P-"

-- 全結晶層 → 結晶は着色されないので入力と出力が同じ (結晶赤 = "cr")
#guard mpaintTest "crcrcrcr" .blue "crcrcrcr"

-- 既に同色で塗られている → 入力と出力が同じ
#guard mpaintTest "CrCrCrCr" .red "CrCrCrCr"

-- ピンと空の混在 → 着色対象がない
#guard mpaintTest "P-P-----" .green "P-P-----"

-- ============================================================
-- 着色機: 結晶や着色不能パーツだけの最上位レイヤ
-- ============================================================

-- 2レイヤ: 最上位レイヤが全ピン → 最上位レイヤは変わらない
-- 下層: CrCrCrCr, 上層: P-P-P-P-
#guard mpaintTest "CrCrCrCr:P-P-P-P-" .blue "CrCrCrCr:P-P-P-P-"

-- 2レイヤ: 最上位レイヤが全空 → あり得ない（正規化で除去される）
-- 2レイヤ: 最上位レイヤが着色パーツ有り → 着色される（最上位レイヤのみ）
#guard mpaintTest "CrCrCrCr:CuCuCuCu" .red "CrCrCrCr:CrCrCrCr"

-- ============================================================
-- 結晶製造機: no-op ケース
-- ============================================================

-- 空象限がないシェイプ → 結晶製造しても変わらない
-- 全パーツ埋まっている
#guard mcrystallizeTest "CrCrCrCr" .blue "CrCrCrCr"

-- 全象限が colored パーツ → 変わらない
#guard mcrystallizeTest "CuRuSuWu" .red "CuRuSuWu"

-- 2レイヤ: 両レイヤとも全パーツ埋まり → 変わらない
#guard mcrystallizeTest "CrCrCrCr:RgRgRgRg" .blue "CrCrCrCr:RgRgRgRg"

-- 全結晶 → 既存結晶は変更されないので変わらない
#guard mcrystallizeTest "crcrcrcr" .blue "crcrcrcr"

-- ============================================================
-- 回転機: no-op ケース (対称シェイプ)
-- ============================================================

-- 全象限同一 → 回転しても変化なし
#guard mrotateCWTest "CrCrCrCr" "CrCrCrCr"

-- 180° 回転で不変な対称シェイプ
#guard (Machine.rotate180 (s "CrRgCrRg")) == s "CrRgCrRg"

-- ============================================================
-- ピン押し機: 結果が none にはならないが有効入力のケース
-- ============================================================

-- ピン押し機は常に入力シェイプの下にピンを生成するので、
-- 完全な no-op にはならない

-- ============================================================
-- 積層機: 有効入力で落下後に1レイヤに収まるケース
-- ============================================================

-- 補完的に重なる → 1レイヤに統合
#guard mstackTest "Cr--Cr--" "--Rg--Rg" "CrRgCrRg"

-- ############################################################
-- 切断処理機 (Half-Destroyer): 入力欠落
-- ############################################################

#guard (Machine.halfDestroy none).isNone

-- ############################################################
-- 切断機 (Cutter): 入力欠落
-- ############################################################

#guard Machine.cut none == (none, none)

-- ############################################################
-- スワップ機 (Swapper): 入力欠落
-- ############################################################

-- 片方 none
#guard Machine.swap none (s "CrCrCrCr") == (none, none)
#guard Machine.swap (s "CrCrCrCr") none == (none, none)
-- 両方 none
#guard Machine.swap none none == (none, none)

-- ############################################################
-- 切断処理機: 有効入力
-- ############################################################

/-- Machine.halfDestroy の結果を文字列比較するヘルパー -/
private def mhalfDestroyTest (shapeCode expected : String) : Bool :=
    match Machine.halfDestroy (s shapeCode) with
    | some result => result.toString == expected
    | none => false

-- 基本: 東側だけ残る (NE, SE 保持)
#guard mhalfDestroyTest "CrCrCrCr" "CrCr----"

-- コア関数との等価性
#guard Machine.halfDestroy (s "CrCrCrCr") ==
    (s "CrCrCrCr").bind (fun sh => sh.halfDestroy)

-- 西側のみ → 結果なし (SW, NW のみ → 東側は空)
#guard (Machine.halfDestroy (s "----CrCr")).isNone

-- ############################################################
-- 切断機: 有効入力
-- ############################################################

/-- Machine.cut の結果を文字列ペアで比較するヘルパー -/
private def mcutTest (shapeCode : String) (expectedEast expectedWest : Option String) : Bool :=
    let (e, w) := Machine.cut (s shapeCode)
    let eOk := match e, expectedEast with
        | some r, some exp => r.toString == exp
        | none, none => true
        | _, _ => false
    let wOk := match w, expectedWest with
        | some r, some exp => r.toString == exp
        | none, none => true
        | _, _ => false
    eOk && wOk

-- 基本切断: 両半分が残る (東=NE+SE, 西=SW+NW)
#guard mcutTest "CrCrCrCr" (some "CrCr----") (some "----CrCr")

-- コア関数との等価性
#guard Machine.cut (s "CrCrCrCr") ==
    match s "CrCrCrCr" with
    | some sh => sh.cut
    | none => (none, none)

-- 東側のみのシェイプ → 西半分は none
#guard mcutTest "CrCr----" (some "CrCr----") none

-- ############################################################
-- スワップ機: 有効入力
-- ############################################################

/-- Machine.swap の結果を文字列ペアで比較するヘルパー -/
private def mswapTest (code1 code2 : String) (expected1 expected2 : Option String) : Bool :=
    let (r1, r2) := Machine.swap (s code1) (s code2)
    let ok1 := match r1, expected1 with
        | some r, some exp => r.toString == exp
        | none, none => true
        | _, _ => false
    let ok2 := match r2, expected2 with
        | some r, some exp => r.toString == exp
        | none, none => true
        | _, _ => false
    ok1 && ok2

-- 基本スワップ: 西半分 (SW, NW) を交換
#guard mswapTest "CrCrCrCr" "RgRgRgRg" (some "CrCrRgRg") (some "RgRgCrCr")

-- コア関数との等価性
#guard Machine.swap (s "CrCrCrCr") (s "RgRgRgRg") ==
    match s "CrCrCrCr", s "RgRgRgRg" with
    | some s1, some s2 => s1.swap s2
    | _, _ => (none, none)
