-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- Machine (加工装置ラッパー) のユニットテスト
import S2IL.Processing.Machine

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

/-- Machine.pinPush の結果を文字列比較するヘルパー -/
private def mpinPushTest (shapeCode expected : String) : Bool :=
    match Machine.pinPush (s shapeCode) with
    | some result => result.toString == expected
    | none => false

/-- Machine.stack の結果を文字列比較するヘルパー -/
private def mstackTest (bottomCode topCode expected : String) : Bool :=
    match Machine.stack (s bottomCode) (s topCode) with
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
#guard (Machine.pinPush none).isNone

-- ============================================================
-- 積層機: 入力欠落
-- ============================================================

-- 下側なし、上側あり → none
#guard (Machine.stack none (s "CrCrCrCr")).isNone

-- 下側あり、上側なし → none
#guard (Machine.stack (s "CrCrCrCr") none).isNone

-- 両方なし → none
#guard (Machine.stack none none).isNone

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
#guard Machine.pinPush (s "CrCrCrCr") ==
    ((s "CrCrCrCr").bind (·.pinPush))

-- ============================================================
-- 積層機: 有効入力
-- ============================================================

-- 基本積層
#guard mstackTest "CrCrCrCr" "RgRgRgRg" "CrCrCrCr:RgRgRgRg"

-- コア関数との等価性
#guard Machine.stack (s "CrCrCrCr") (s "RgRgRgRg") ==
    (match s "CrCrCrCr", s "RgRgRgRg" with
    | some b, some t => b.stack t
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
