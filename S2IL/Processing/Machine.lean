-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Processing.Painter
import S2IL.Processing.CrystalGenerator
import S2IL.Processing.Rotate
import S2IL.Processing.PinPusher
import S2IL.Processing.Stacker

/-!
# Machine (加工装置)

各加工装置の `Option` 入力対応ラッパー関数を定義する。

## 概要

ゲーム上、加工装置は **有効な入力が全て揃っている場合にのみ出力を生成する**。
例えば着色機はシェイプと色の両方が、積層機は2つのシェイプが必要であり、
いずれかが欠けていれば加工は行われない（`none` を返す）。

一方で、入力が有効であれば結果的に何も行われない挙動（no-op）は許容される。
例えば着色機で全象限がピンや結晶である場合、入力と出力は結果として同一になる。

このモジュールでは、コア処理関数（`Shape.paint` 等）を `Option` で包み、
入力の存在/不在をハンドリングするラッパー関数を提供する。
-/

namespace Machine

-- ============================================================
-- 着色機 (Painter)
-- ============================================================

/-- 着色機を適用する。シェイプと色の両方が存在する場合のみ出力を生成する -/
def paint (shape : Option Shape) (color : Option Color) : Option Shape :=
    match shape, color with
    | some s, some c => some (s.paint c)
    | _, _ => none

-- ============================================================
-- 結晶製造機 (CrystalGenerator)
-- ============================================================

/-- 結晶製造機を適用する。シェイプと色の両方が存在する場合のみ出力を生成する -/
def crystallize (shape : Option Shape) (color : Option Color) : Option Shape :=
    match shape, color with
    | some s, some c => some (s.crystallize c)
    | _, _ => none

-- ============================================================
-- 回転機 (Rotator)
-- ============================================================

/-- 時計回り 90° 回転機を適用する。シェイプが存在する場合のみ出力を生成する -/
def rotateCW (shape : Option Shape) : Option Shape :=
    shape.map Shape.rotateCW

/-- 反時計回り 90° 回転機を適用する。シェイプが存在する場合のみ出力を生成する -/
def rotateCCW (shape : Option Shape) : Option Shape :=
    shape.map Shape.rotateCCW

/-- 180° 回転機を適用する。シェイプが存在する場合のみ出力を生成する -/
def rotate180 (shape : Option Shape) : Option Shape :=
    shape.map Shape.rotate180

-- ============================================================
-- ピン押し機 (PinPusher)
-- ============================================================

/-- ピン押し機を適用する。シェイプが存在する場合のみ出力を生成する -/
def pinPush (shape : Option Shape) (config : GameConfig := inferInstance)
        : Option Shape :=
    match shape with
    | some s => s.pinPush config
    | none => none

-- ============================================================
-- 積層機 (Stacker)
-- ============================================================

/-- 積層機を適用する。下側・上側の両シェイプが存在する場合のみ出力を生成する -/
def stack (bottom top : Option Shape) (config : GameConfig := inferInstance)
        : Option Shape :=
    match bottom, top with
    | some b, some t => b.stack t config
    | _, _ => none

end Machine
