-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity

/-!
# Test.Operations.Gravity

Wave Gravity の代表 I/O と Behavior A 回帰テスト。

`Shape.waveStep` は末尾空レイヤを保持する atomic tick、`Shape.gravity` は fixed fuel と
同値な早期停止 core 後に `normalize` する公開 API として確認する。
-/

open S2IL

namespace Test.Operations.Gravity

-- ============================================================
-- 共通サンプル
-- ============================================================

private def L_empty : Layer := Layer.empty

private def L_ne : Layer :=
  Layer.mk (.colored .circle .red) .empty .empty .empty

private def L_pin_ne : Layer :=
  Layer.mk .pin .empty .empty .empty

private def L_ne_se : Layer :=
  Layer.mk (.colored .circle .red) (.colored .star .blue) .empty .empty

private def s_stress8_grounded_column : Shape :=
  [L_ne, L_ne, L_ne, L_ne, L_ne, L_ne, L_ne, L_ne]

private def pos (layer : Nat) (dir : Direction) : QuarterPos :=
  QuarterPos.mk layer dir

private def waveStepTest (input expected : String) : Bool :=
  match Shape.ofString? input with
  | none => false
  | some s => (Shape.waveStep s).toString == expected

private def waveStepNoChange (input : String) : Bool :=
  waveStepTest input input

private def gravityTest (input expected : String) : Bool :=
  match Shape.ofString? input with
  | none => false
  | some s => (Shape.gravity s).toString == expected

private def gravityNoChange (input : String) : Bool :=
  gravityTest input input

private def gravityIdempotent (input : String) : Bool :=
  match Shape.ofString? input with
  | none => false
  | some s =>
      let result := Shape.gravity s
      (Shape.gravity result).toString == result.toString

private def floatingHeightTest (input : String) (expected : Nat) : Bool :=
  match Shape.ofString? input with
  | none => false
  | some s => floatingHeight s == expected

private def waveGravityCoreNoFloating (input : String) : Bool :=
  match Shape.ofString? input with
  | none => false
  | some s => (floatingPositions (Shape.waveGravityCore s.length s)).isEmpty

private def floatingPositionsOfString (input : String) : List QuarterPos :=
  match Shape.ofString? input with
  | none => []
  | some s => floatingPositions s

private def hasFloating (input : String) (p : QuarterPos) : Bool :=
  (floatingPositionsOfString input).contains p

private def noFloating (input : String) : Bool :=
  (floatingPositionsOfString input).isEmpty

-- ============================================================
-- waveStep: 1 tick の代表例
-- ============================================================

-- 単独 floating 象限は 1 レイヤ下がり、元レイヤは空になる。
#guard (Shape.waveStep [L_empty, L_ne]).toString == "Cr------:--------"

-- 複数 floating stack は同時に 1 レイヤ下がる。
#guard (Shape.waveStep [L_empty, L_pin_ne, L_pin_ne]).toString ==
  "P-------:P-------:--------"

-- 垂直接触で接地している象限は動かない。
#guard (Shape.waveStep [L_ne, L_ne]).toString == "Cr------:Cr------"

-- 同層の非ピン水平支持で接地している象限も動かない。
#guard (Shape.waveStep [L_ne, L_ne_se]).toString == "Cr------:CrSb----"

-- stress8 境界の接地済み column は floating を持たず、1 tick で不変。
#guard s_stress8_grounded_column.layerCount == GameConfig.stress8.maxLayers
#guard (floatingPositions s_stress8_grounded_column).isEmpty
#guard (Shape.waveStep s_stress8_grounded_column).toString ==
  s_stress8_grounded_column.toString

-- 旧 Model C テストからサルベージ: ピンは水平接地接触を伝播しない。
#guard hasFloating "Cr------:RgP-----" (pos 1 1)
#guard waveStepTest "Cr------:RgP-----" "CrP-----:Rg------"
#guard hasFloating "Cr------:P-Sb----" (pos 1 1)
#guard waveStepTest "Cr------:P-Sb----" "CrSb----:P-------"

-- 旧 Model C テストからサルベージ: 非ピン同士の水平接地接触とピン垂直連鎖。
#guard noFloating "Cr------:CrRg----"
#guard waveStepNoChange "Cr------:CrRg----"
#guard noFloating "Cr------:P-------:P-------"
#guard waveStepNoChange "Cr------:P-------:P-------"
#guard noFloating "CrCr----:P-Rg----"
#guard waveStepNoChange "CrCr----:P-Rg----"

-- 旧 stress8 寄りケース: 全方角のピン垂直連鎖は接地済みとして不変。
#guard noFloating "CrCrCrCr:P-P-P-P-:P-P-P-P-:RgRgRgRg"
#guard waveStepNoChange "CrCrCrCr:P-P-P-P-:P-P-P-P-:RgRgRgRg"

-- 旧 isUpwardGroundingContact 回帰 S1〜S4: 下方向伝播によるピン誤接地を防ぐ。
#guard hasFloating "Rr------:RrP-----:RrRr----" (pos 1 1)
#guard waveStepTest "Rr------:RrP-----:RrRr----" "RrP-----:Rr------:RrRr----"
#guard hasFloating "Rr------:RrP-P---:RrRrRr--" (pos 1 1)
#guard hasFloating "Rr------:RrP-P---:RrRrRr--" (pos 1 2)
#guard waveStepTest "Rr------:RrP-P---:RrRrRr--" "RrP-P---:Rr------:RrRrRr--"
#guard hasFloating "Rr------:RrP---P-:RrRrRrRr" (pos 1 1)
#guard hasFloating "Rr------:RrP---P-:RrRrRrRr" (pos 1 3)
#guard waveStepTest "Rr------:RrP---P-:RrRrRrRr" "RrP---P-:Rr------:RrRrRrRr"
#guard !hasFloating "Rr------:RrP-P-P-:RrRrRrRr" (pos 1 0)
#guard hasFloating "Rr------:RrP-P-P-:RrRrRrRr" (pos 1 1)
#guard hasFloating "Rr------:RrP-P-P-:RrRrRrRr" (pos 1 2)
#guard hasFloating "Rr------:RrP-P-P-:RrRrRrRr" (pos 1 3)
#guard waveStepTest "Rr------:RrP-P-P-:RrRrRrRr" "RrP-P-P-:Rr------:RrRrRrRr"

-- 旧追加エッジケース: 空レイヤをまたぐ 1 tick と複数孤立ピンの同時落下。
#guard waveStepTest "--------:--------:Cr------" "--------:Cr------:--------"
#guard waveStepTest "--------:P-P-P-P-" "P-P-P-P-:--------"

-- ============================================================
-- gravity: fixed fuel + normalize
-- ============================================================

#guard (Shape.gravity [L_empty, L_ne]).toString == "Cr------"

-- 旧 gravity 代表例からサルベージ: 基本落下と独立 floating 群。
#guard gravityTest "--------:Cr------" "Cr------"
#guard gravityTest "--------:--Cr--Cr" "--Cr--Cr"
#guard gravityTest "CrCr----:----RgRg" "CrCrRgRg"
#guard gravityNoChange "CrCr----:--RgRg--"

-- 旧 gravity 代表例からサルベージ: pin と空レイヤを含む fixed fuel 結果。
#guard gravityTest "--------:P-------:Cr------" "P-------:Cr------"
#guard gravityNoChange "CrCrCrCr:P-------:RgRgRgRg"
#guard gravityTest "--CrCr--:--------:--RgRg--" "--CrCr--:--RgRg--"
#guard gravityTest "CrCr----:--------:--RgRg--:--------:----SbSb"
  "CrCr----:--RgRg--:----SbSb"
#guard gravityTest "--------:--------:Cr------" "Cr------"
#guard gravityTest "--------:P-------" "P-------"
#guard gravityTest "--------:P-P-P-P-" "P-P-P-P-"

-- 旧 gravity 冪等性テストからサルベージ: 代表結果は再適用で変化しない。
#guard gravityIdempotent "--------:Cr------"
#guard gravityIdempotent "--------:--Cr--Cr"
#guard gravityIdempotent "CrCr----:----RgRg"
#guard gravityIdempotent "--------:P-------:Cr------"
#guard gravityIdempotent "CrCrCrCr:P-------:RgRgRgRg"
#guard gravityIdempotent "CrCr----:--------:--RgRg--:--------:----SbSb"

-- 旧 F1〜F6 stress audit の手動ケースからサルベージ: crystal / pin / 空レイヤ混在。
#guard floatingHeightTest "--------:crcr----:P-cr----:crcr----" 3
#guard waveStepTest "--------:crcr----:P-cr----:crcr----"
  "crcr----:P-cr----:crcr----:--------"
#guard gravityTest "--------:crcr----:P-cr----:crcr----" "crcr----:P-cr----:crcr----"
#guard waveGravityCoreNoFloating "--------:crcr----:P-cr----:crcr----"

#guard floatingHeightTest "Cr------:--Cr----" 1
#guard waveStepTest "Cr------:--Cr----" "CrCr----:--------"
#guard gravityTest "Cr------:--Cr----" "CrCr----"
#guard waveGravityCoreNoFloating "Cr------:--Cr----"

#guard floatingHeightTest "Cr------:RgRg----:----Sb--" 2
#guard waveStepTest "Cr------:RgRg----:----Sb--" "Cr------:RgRgSb--:--------"
#guard gravityTest "Cr------:RgRg----:----Sb--" "Cr------:RgRgSb--"
#guard waveGravityCoreNoFloating "Cr------:RgRg----:----Sb--"

#guard floatingHeightTest "P-------:--Cr----" 1
#guard waveStepTest "P-------:--Cr----" "P-Cr----:--------"
#guard gravityTest "P-------:--Cr----" "P-Cr----"
#guard waveGravityCoreNoFloating "P-------:--Cr----"

#guard floatingHeightTest "crcr----:P-------:--cr----" 2
#guard waveStepTest "crcr----:P-------:--cr----" "crcr----:P-cr----:--------"
#guard gravityTest "crcr----:P-------:--cr----" "crcr----:P-cr----"
#guard waveGravityCoreNoFloating "crcr----:P-------:--cr----"

#guard floatingHeightTest "Cr--Cr--:--Cr----:Cr--Cr--" 2
#guard waveStepTest "Cr--Cr--:--Cr----:Cr--Cr--" "CrCrCr--:Cr--Cr--:--------"
#guard gravityTest "Cr--Cr--:--Cr----:Cr--Cr--" "CrCrCr--:Cr--Cr--"
#guard waveGravityCoreNoFloating "Cr--Cr--:--Cr----:Cr--Cr--"

#guard floatingHeightTest "crcrcrcr:--------:crcrcrcr" 2
#guard waveStepTest "crcrcrcr:--------:crcrcrcr" "crcrcrcr:crcrcrcr:--------"
#guard gravityTest "crcrcrcr:--------:crcrcrcr" "crcrcrcr:crcrcrcr"
#guard waveGravityCoreNoFloating "crcrcrcr:--------:crcrcrcr"

#guard floatingHeightTest "P-P-P-P-:--------:Cr--Cr--" 2
#guard waveStepTest "P-P-P-P-:--------:Cr--Cr--" "P-P-P-P-:Cr--Cr--:--------"
#guard gravityTest "P-P-P-P-:--------:Cr--Cr--" "P-P-P-P-:Cr--Cr--"
#guard waveGravityCoreNoFloating "P-P-P-P-:--------:Cr--Cr--"

#guard floatingHeightTest "--Cr----:P-------" 1
#guard waveStepTest "--Cr----:P-------" "P-Cr----:--------"
#guard gravityTest "--Cr----:P-------" "P-Cr----"
#guard waveGravityCoreNoFloating "--Cr----:P-------"

#guard floatingHeightTest "Cr------:----Cr--:--Cr----" 2
#guard waveStepTest "Cr------:----Cr--:--Cr----" "Cr--Cr--:--Cr----:--------"
#guard gravityTest "Cr------:----Cr--:--Cr----" "CrCrCr--"
#guard waveGravityCoreNoFloating "Cr------:----Cr--:--Cr----"

-- ============================================================
-- Defs 層 collision-free 補題の公開確認
-- ============================================================

example {s : Shape} {p : QuarterPos} (h : FloatingPos s p) :
    (QuarterPos.getQuarter s p.down).isEmpty ∨ FloatingPos s p.down :=
  FloatingPos.down_empty_or_floating h

example {s : Shape} {p q : QuarterPos}
    (hp : FloatingPos s p) (hq : FloatingPos s q) (hdown : p.down = q.down) : p = q :=
  QuarterPos.down_injective_on_floating hp hq hdown

-- ============================================================
-- Behavior A: 接地保存補題と #guard 回帰
-- ============================================================

example {s : Shape} {p : QuarterPos} (h : IsGrounded s p) :
    QuarterPos.getQuarter (Shape.waveStep s) p = QuarterPos.getQuarter s p :=
  IsGrounded.waveStep_static h

example {s : Shape} {p : QuarterPos} (h : IsGrounded s p) :
    IsGrounded (Shape.waveStep s) p :=
  IsGrounded.waveStep_mono h

example {s : Shape} (h : IsSettled s) : Shape.waveStep s = s :=
  IsSettled.waveStep_fixed h

example {s : Shape} (h : 0 < floatingHeight (Shape.waveStep s)) :
    floatingHeight (Shape.waveStep s) < floatingHeight s :=
  floatingHeight_waveStep_lt h

example (s : Shape) : floatingPositions (Nat.iterate Shape.waveStep s.length s) = [] :=
  waveStep_iter_no_floating s

example (s : Shape) : (∀ p : QuarterPos, ¬ FloatingPos s p) ↔ IsSettled s :=
  no_floating_iff_isSettled s

example (s : Shape) : floatingPositions s = [] ↔ IsSettled s :=
  floatingPositions_eq_nil_iff_isSettled s

example {s : Shape} (h : floatingPositions s = []) : Shape.waveStep s = s :=
  Shape.waveStep_eq_self_of_floatingPositions_eq_nil h

example (fuel : Nat) (s : Shape) :
    Shape.waveGravityCoreFast fuel s = Shape.waveGravityCore fuel s :=
  Shape.waveGravityCoreFast_eq_waveGravityCore fuel s

example (s : Shape) : IsSettled (Shape.waveGravityCore s.length s) :=
  waveGravityCore_isSettled s

example (s : Shape) : IsSettled (Shape.waveGravityCoreFast s.length s) :=
  waveGravityCoreFast_isSettled s

example (s : Shape) : IsSettled (Shape.gravity s) :=
  Shape.gravity.isSettled s

example {s : Shape} (h : IsSettled s) : floatingPositions s = [] :=
  IsSettled.floatingPositions_eq_nil h

example {s : Shape} (h : ∀ p : QuarterPos, ¬ FloatingPos s p) : Shape.waveStep s = s :=
  Shape.waveStep_eq_self_of_no_floating h

example {s : Shape} (h : IsSettled s) (fuel : Nat) : Shape.waveGravityCore fuel s = s :=
  waveGravityCore_eq_self_of_IsSettled h fuel

example {s : Shape} (hSettled : IsSettled s) (hNorm : Shape.IsNormalized s) :
    Shape.gravity s = s :=
  Shape.gravity.of_isSettled hSettled hNorm

-- ============================================================
-- Equivariance: 公開 theorem の確認
-- ============================================================

example (s : Shape) (p : QuarterPos) :
    FloatingPos s.rotateCW p.rotateCW ↔ FloatingPos s p :=
  FloatingPos.rotateCW s p

example (s : Shape) : (Shape.waveStep s).rotateCW = Shape.waveStep s.rotateCW :=
  Shape.waveStep.rotateCW_comm s

example (fuel : Nat) (s : Shape) :
    (Shape.waveGravityCore fuel s).rotateCW = Shape.waveGravityCore fuel s.rotateCW :=
  Shape.waveGravityCore.rotateCW_comm fuel s

example (s : Shape) : Shape.rotateCW (Shape.gravity s) = Shape.gravity (Shape.rotateCW s) :=
  Shape.gravity.rotateCW_comm s

example (s : Shape) : (Shape.gravity s).rotate180 = Shape.gravity s.rotate180 :=
  Shape.gravity.rotate180_comm s

example (s : Shape) : (Shape.gravity s).rotateCCW = Shape.gravity s.rotateCCW :=
  Shape.gravity.rotateCCW_comm s

end Test.Operations.Gravity
