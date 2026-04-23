-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Painter.Painter
import S2IL.Operations.CrystalGenerator.CrystalGenerator
import S2IL.Kernel.Transform.Rotate
import S2IL.Operations.PinPusher.PinPusher
import S2IL.Operations.Stacker.Stacker
import S2IL.Operations.Cutter.Cutter
import S2IL.Operations.ColorMixer.ColorMixer
import S2IL.SettledShape

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

## 安定状態 (Settled State) の方針

ゲーム規定により、ベルトで搬送されるシェイプおよび各加工装置の入出力は
常に安定状態 (`Shape.IsSettled`) であることが保証されている。

着色・回転・結晶化は `Shape.SettledShape` を入出力の型として採用済み。
積層・切断・ピン押し等は `gravity_IsSettled` axiom を利用して SettledShape に段階的に移行済み。
swap は `Shape.SettledShape.swap` により SettledShape 入出力へ移行済み。
-/

namespace Machine

-- ============================================================
-- 着色機 (Painter)
-- ============================================================

/-- 着色機を適用する。シェイプと色の両方が存在する場合のみ出力を生成する -/
def paint (shape : Option Shape.SettledShape) (color : Option Color) : Option Shape.SettledShape :=
    match shape, color with
    | some ss, some c => some (ss.paint c)
    | _, _ => none

-- ============================================================
-- 結晶製造機 (CrystalGenerator)
-- ============================================================

/-- 結晶製造機を適用する。シェイプと色の両方が存在する場合のみ出力を生成する。
    入力 Shape の安定状態に関わらず、出力は常に安定状態 -/
def crystallize (shape : Option Shape) (color : Option Color) : Option Shape.SettledShape :=
    match shape, color with
    | some s, some c => some (Shape.SettledShape.crystallize s c)
    | _, _ => none

-- ============================================================
-- 回転機 (Rotator)
-- ============================================================

/-- 時計回り 90° 回転機を適用する。シェイプが存在する場合のみ出力を生成する -/
def rotateCW (shape : Option Shape.SettledShape) : Option Shape.SettledShape :=
    shape.map (·.rotateCW)

/-- 反時計回り 90° 回転機を適用する。シェイプが存在する場合のみ出力を生成する -/
def rotateCCW (shape : Option Shape.SettledShape) : Option Shape.SettledShape :=
    shape.map (·.rotateCCW)

/-- 180° 回転機を適用する。シェイプが存在する場合のみ出力を生成する -/
def rotate180 (shape : Option Shape.SettledShape) : Option Shape.SettledShape :=
    shape.map (·.rotate180)

-- ============================================================
-- ピン押し機 (PinPusher)
-- ============================================================

/-- ピン押し機を適用する。シェイプが存在する場合のみ出力を生成する -/
def pinPush (shape : Option Shape) (config : GameConfig) : Option Shape :=
    shape.bind (·.pinPush config)

-- ============================================================
-- 積層機 (Stacker)
-- ============================================================

/-- 積層機を適用する。下側・上側の両シェイプが存在する場合のみ出力を生成する -/
def stack (bottom top : Option Shape) (config : GameConfig) : Option Shape :=
    match bottom, top with
    | some b, some t => b.stack t config
    | _, _ => none

-- ============================================================
-- 切断処理機 (Half-Destroyer)
-- ============================================================

/-- 切断処理機を適用する。シェイプが存在する場合のみ出力を生成する -/
def halfDestroy (shape : Option Shape) : Option Shape :=
    match shape with
    | some s => s.halfDestroy
    | none => none

-- ============================================================
-- 切断機 (Cutter)
-- ============================================================

/-- 切断機を適用する。シェイプが存在する場合のみ出力を生成する。
    戻り値: (東側の半分, 西側の半分) -/
def cut (shape : Option Shape) : Option Shape × Option Shape :=
    match shape with
    | some s => s.cut
    | none => (none, none)

-- ============================================================
-- スワップ機 (Swapper)
-- ============================================================

/-- スワップ機を適用する。2つのシェイプが存在する場合のみ出力を生成する。
    戻り値: (入れ替え後のシェイプ1, 入れ替え後のシェイプ2) -/
def swap (shape1 shape2 : Option Shape.SettledShape) :
        Option Shape.SettledShape × Option Shape.SettledShape :=
    match shape1, shape2 with
    | some ss1, some ss2 => ss1.swap ss2
    | _, _ => (none, none)

-- ============================================================
-- 混色機 (Color Mixer)
-- ============================================================

/-- 混色機を適用する。2つの色が存在する場合のみ出力を生成する -/
def mixColor (color1 color2 : Option Color) : Option Color :=
    match color1, color2 with
    | some c1, some c2 => some (ColorMixer.mix c1 c2)
    | _, _ => none

-- ============================================================
-- 回転等変性定理
-- ============================================================

-- --------------------------------------------------------
-- 内部ヘルパー：Option 2引数操作の回転等変性テンプレート
-- --------------------------------------------------------

/-- SettledShape 入出力の 2引数 Option 操作に対する rotation 等変性テンプレート。
    paint 系3定理が共通して使う -/
private theorem option_paint_rot_comm
        (rotOut : Shape.SettledShape → Shape.SettledShape)
        (rotIn : Shape.SettledShape → Shape.SettledShape)
        (h : ∀ ss c, rotOut (ss.paint c) = (rotIn ss).paint c)
        (shape : Option Shape.SettledShape) (color : Option Color) :
        (paint shape color).map rotOut = paint (shape.map rotIn) color := by
    cases shape with
    | none => cases color <;> rfl
    | some ss =>
        cases color with
        | none => rfl
        | some c =>
            simp only [paint, Option.map]
            exact congrArg some (h ss c)

/-- Shape → SettledShape の 2引数 Option 操作に対する rotation 等変性テンプレート。
    crystallize 系3定理が共通して使う -/
private theorem option_crystallize_rot_comm
        (rotOut : Shape.SettledShape → Shape.SettledShape)
        (rotIn : Shape → Shape)
        (h : ∀ s c, rotOut (Shape.SettledShape.crystallize s c) = Shape.SettledShape.crystallize (rotIn s) c)
        (shape : Option Shape) (color : Option Color) :
        (crystallize shape color).map rotOut = crystallize (shape.map rotIn) color := by
    cases shape with
    | none => cases color <;> rfl
    | some s =>
        cases color with
        | none => rfl
        | some c =>
            simp only [crystallize, Option.map]
            exact congrArg some (h s c)

/-- Machine.paint は rotateCW と可換 -/
theorem paint_rotateCW_comm (shape : Option Shape.SettledShape) (color : Option Color) :
        (paint shape color).map (·.rotateCW) =
        paint (shape.map (·.rotateCW)) color :=
    option_paint_rot_comm (·.rotateCW) (·.rotateCW) (fun ss c => Subtype.ext (Shape.paint_rotateCW_comm ss.val c)) shape color

/-- Machine.paint は rotate180 と可換 -/
theorem paint_rotate180_comm (shape : Option Shape.SettledShape) (color : Option Color) :
        (paint shape color).map (·.rotate180) =
        paint (shape.map (·.rotate180)) color :=
    option_paint_rot_comm (·.rotate180) (·.rotate180) (fun ss c => Subtype.ext (Shape.paint_rotate180_comm ss.val c)) shape color

/-- Machine.paint は rotateCCW と可換 -/
theorem paint_rotateCCW_comm (shape : Option Shape.SettledShape) (color : Option Color) :
        (paint shape color).map (·.rotateCCW) =
        paint (shape.map (·.rotateCCW)) color :=
    option_paint_rot_comm (·.rotateCCW) (·.rotateCCW) (fun ss c => Subtype.ext (Shape.paint_rotateCCW_comm ss.val c)) shape color

/-- Machine.crystallize は rotateCW と可換 -/
theorem crystallize_rotateCW_comm (shape : Option Shape) (color : Option Color) :
        (crystallize shape color).map (·.rotateCW) =
        crystallize (shape.map Shape.rotateCW) color :=
    option_crystallize_rot_comm (·.rotateCW) Shape.rotateCW (fun s c => Subtype.ext (Shape.crystallize_rotateCW_comm s c)) shape color

/-- Machine.crystallize は rotate180 と可換 -/
theorem crystallize_rotate180_comm (shape : Option Shape) (color : Option Color) :
        (crystallize shape color).map (·.rotate180) =
        crystallize (shape.map Shape.rotate180) color :=
    option_crystallize_rot_comm (·.rotate180) Shape.rotate180 (fun s c => Subtype.ext (Shape.crystallize_rotate180_comm s c)) shape color

/-- Machine.crystallize は rotateCCW と可換 -/
theorem crystallize_rotateCCW_comm (shape : Option Shape) (color : Option Color) :
        (crystallize shape color).map (·.rotateCCW) =
        crystallize (shape.map Shape.rotateCCW) color :=
    option_crystallize_rot_comm (·.rotateCCW) Shape.rotateCCW (fun s c => Subtype.ext (Shape.crystallize_rotateCCW_comm s c)) shape color

-- ============================================================
-- pinPush 回転等変性
-- ============================================================

/-- Machine.pinPush は rotateCW と可換 -/
theorem pinPush_rotateCW_comm (shape : Option Shape) (config : GameConfig)
        (h_config : config.maxLayers ≤ 5) :
        (pinPush shape config).map Shape.rotateCW =
        pinPush (shape.map Shape.rotateCW) config := by
    cases shape with
    | none => rfl
    | some s =>
        show (s.pinPush config).map Shape.rotateCW = s.rotateCW.pinPush config
        exact Shape.pinPush_rotateCW_comm _ _ h_config

/-- Machine.pinPush は rotate180 と可換 -/
theorem pinPush_rotate180_comm (shape : Option Shape) (config : GameConfig)
        (h_config : config.maxLayers ≤ 5) :
        (pinPush shape config).map Shape.rotate180 =
        pinPush (shape.map Shape.rotate180) config := by
    cases shape with
    | none => rfl
    | some s =>
        show (s.pinPush config).map Shape.rotate180 = s.rotate180.pinPush config
        exact Shape.pinPush_rotate180_comm _ _ h_config

/-- Machine.pinPush は rotateCCW と可換 -/
theorem pinPush_rotateCCW_comm (shape : Option Shape) (config : GameConfig)
        (h_config : config.maxLayers ≤ 5) :
        (pinPush shape config).map Shape.rotateCCW =
        pinPush (shape.map Shape.rotateCCW) config := by
    cases shape with
    | none => rfl
    | some s =>
        show (s.pinPush config).map Shape.rotateCCW = s.rotateCCW.pinPush config
        exact Shape.pinPush_rotateCCW_comm _ _ h_config

-- ============================================================
-- stack 回転等変性
-- ============================================================

/-- Machine.stack は rotateCW と可換（settled 入力が必要） -/
theorem stack_rotateCW_comm (bottom top : Option Shape) (config : GameConfig)
        (h_config : config.maxLayers ≤ 5)
        (h_bottom : ∀ s, bottom = some s → s.IsSettled)
        (h_top : ∀ s, top = some s → s.IsSettled) :
        (stack bottom top config).map Shape.rotateCW =
        stack (bottom.map Shape.rotateCW) (top.map Shape.rotateCW) config := by
    cases bottom with
    | none => cases top <;> rfl
    | some b =>
        cases top with
        | none => rfl
        | some t =>
            simp only [stack, Option.map]
            exact Shape.stack_rotateCW_comm b t config h_config
                (h_bottom b rfl) (h_top t rfl)

/-- Machine.stack は rotate180 と可換（settled 入力が必要） -/
theorem stack_rotate180_comm (bottom top : Option Shape) (config : GameConfig)
        (h_config : config.maxLayers ≤ 5)
        (h_bottom : ∀ s, bottom = some s → s.IsSettled)
        (h_top : ∀ s, top = some s → s.IsSettled) :
        (stack bottom top config).map Shape.rotate180 =
        stack (bottom.map Shape.rotate180) (top.map Shape.rotate180) config := by
    cases bottom with
    | none => cases top <;> rfl
    | some b =>
        cases top with
        | none => rfl
        | some t =>
            simp only [stack, Option.map]
            exact Shape.stack_rotate180_comm b t config h_config
                (h_bottom b rfl) (h_top t rfl)

/-- Machine.stack は rotateCCW と可換（settled 入力が必要） -/
theorem stack_rotateCCW_comm (bottom top : Option Shape) (config : GameConfig)
        (h_config : config.maxLayers ≤ 5)
        (h_bottom : ∀ s, bottom = some s → s.IsSettled)
        (h_top : ∀ s, top = some s → s.IsSettled) :
        (stack bottom top config).map Shape.rotateCCW =
        stack (bottom.map Shape.rotateCCW) (top.map Shape.rotateCCW) config := by
    cases bottom with
    | none => cases top <;> rfl
    | some b =>
        cases top with
        | none => rfl
        | some t =>
            simp only [stack, Option.map]
            exact Shape.stack_rotateCCW_comm b t config h_config
                (h_bottom b rfl) (h_top t rfl)

end Machine
