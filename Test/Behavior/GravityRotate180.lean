-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- Gravity rotate180 等変性のテスト
import S2IL.Behavior.Gravity

open Gravity

/-- process_rotate180 が成立するかテスト -/
private def testProcessRotate180 (code : String) : Bool :=
    match Shape.ofString? code with
    | none => false
    | some s =>
        let lhs := (Gravity.process s).map Shape.rotate180
        let rhs := Gravity.process s.rotate180
        lhs == rhs

-- ============================================================
-- 基本テスト: (process s).map r180 = process s.r180
-- ============================================================

-- 1レイヤ: 落下なし
#guard testProcessRotate180 "CuCuCuCu"
#guard testProcessRotate180 "Cu----Cu"
#guard testProcessRotate180 "Cu--Cu--"
#guard testProcessRotate180 "CrCr----"
#guard testProcessRotate180 "----CrCr"

-- 2レイヤ: 単純落下
#guard testProcessRotate180 "--------:CuCuCuCu"
#guard testProcessRotate180 "--------:Cr------"
#guard testProcessRotate180 "--------:------Cr"
#guard testProcessRotate180 "Cr------:--Cr----"
#guard testProcessRotate180 "Cr------:------Cr"
#guard testProcessRotate180 "CrCr----:----CrCr"
#guard testProcessRotate180 "CrCr----:----RgRg"

-- 2レイヤ: ピン
#guard testProcessRotate180 "--------:P-------"
#guard testProcessRotate180 "--------:P-P-P-P-"
#guard testProcessRotate180 "P-------:--P-----"

-- 3レイヤ
#guard testProcessRotate180 "CrCrCrCr:--------:CrCrCrCr"
#guard testProcessRotate180 "Cr------:--------:------Cr"
#guard testProcessRotate180 "Cr------:------Cr:--------"
#guard testProcessRotate180 "--CrCr--:--------:--RgRg--"

-- 複数落下単位（異なる方角）
#guard testProcessRotate180 "CrCr----:--------:--RgRg--:--------:----SbSb"

-- 4レイヤ: 上下方角で分離したクラスタ
#guard testProcessRotate180 "Cu------:--------:------Cu"
#guard testProcessRotate180 "Cu------:--------:--------:------Cu"
#guard testProcessRotate180 "Cu--Cu--:--------:--Cu--Cu"
#guard testProcessRotate180 "Cu------:----Cu--:--Cu----:------Cu"

-- ============================================================
-- 反例: process_rotate180 は 6 レイヤ以上のシェイプで偽
-- ============================================================
-- 根本原因: 同 minLayer の方角共有 FU ペアで、一方の着地が他方の着地距離を変える
-- (NE 列のカスケード障害物効果)。5 レイヤ以下では floor contact が支配するため発生しない。

-- 6L 反例: L0={NE=cr NW=cr} L1={NE=cr} L2=empty L3={NE=cr SW=cr}
--          L4={SE=cr SW=cr} L5={NE=cr SE=cr SW=cr}
-- FU: {NE@3} ml=3, {SW@3 SW@4 SE@4 SE@5 NE@5} ml=3 (方角 NE 共有)
#guard !testProcessRotate180 "cr----cr:cr------:--------:cr--cr--:--crcr--:crcrcr--"

-- 7L 反例
#guard !testProcessRotate180 "cr----cr:cr------:cr------:--------:cr--cr--:----cr--:crcrcr--"

-- 対照: 5L 以下では成立
#guard testProcessRotate180 "------cr:cr--cr--:--cr----:crcrcr--"
