-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- Gravity rotate180 等変性のテスト
import S2IL.Operations.Gravity

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
-- ≥6L: waveStep の着地距離昇順ソートにより等変性が成立
-- ============================================================
-- 旧実装では同 minLayer の方角共有 FU ペアで BFS 順序依存のため ≥6L で偽だったが、
-- settling FU を事前計算着地距離の昇順でソートすることで解決。

-- 6L (旧反例): settling FU が方角 NE を共有するが、着地距離ソートにより等変
#guard testProcessRotate180 "cr----cr:cr------:--------:cr--cr--:--crcr--:crcrcr--"

-- 7L (旧反例)
#guard testProcessRotate180 "cr----cr:cr------:cr------:--------:cr--cr--:----cr--:crcrcr--"

-- 5L 以下でも引き続き成立
#guard testProcessRotate180 "------cr:cr--cr--:--cr----:crcrcr--"

-- ============================================================
-- ≥7L: placeLDGroups による同一 LD グループ一括配置で等変性が成立
-- ============================================================
-- 旧 foldl 実装では同一 LD の settling FU が方角列を共有する場合、
-- BFS 順序が rotate180 で逆転し foldl 結果が異なっていた。
-- placeLDGroups で同一 LD 内は固定 d で一括配置することで解決。

-- 7L: tied LD=4 の 2 FU が NE 方角列を共有
#guard testProcessRotate180 "--Cu--Cu:--------:--------:--------:Cu--Cu--:----Cu--:Cu--CuCu"
