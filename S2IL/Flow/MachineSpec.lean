-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Flow.Capability
import S2IL.Operations

/-!
# S2IL.Flow.MachineSpec

Shape Processing Flow 上のマシン仕様。

本モジュールは `S2IL.Operations` facade の公開操作を Flow 層の `MachineKind` と
ポート仕様へ対応付ける。具体的な速度値は `Capability` として外から与える。
-/

namespace S2IL

namespace PortSpec

/-- ベルト入力または出力のポート仕様を作る。 -/
def belt (name : String) : PortSpec :=
  { kind := StreamKind.belt, name := name }

/-- パイプ入力または出力のポート仕様を作る。 -/
def pipe (name : String) : PortSpec :=
  { kind := StreamKind.pipe, name := name }

end PortSpec

/-- マシン 1 台の入力ポート列と出力ポート列。 -/
structure NodeSpec where
  /-- 入力ポート列。 -/
  inputs : List PortSpec
  /-- 出力ポート列。 -/
  outputs : List PortSpec
deriving Repr, DecidableEq, BEq

/-- Flow 層で扱う代表マシン種別。 -/
inductive MachineKind where
  | rotator
  | reverseRotator
  | rotator180
  | halfDestroyer
  | pinPusher
  | cutter
  | stacker
  | swapper
  | painter
  | crystalGenerator
  | colorMixer
  | trash
deriving Repr, DecidableEq, BEq

/-- `MachineKind` が参照する Operations 側の意味論の形。 -/
inductive MachineSemantics where
  | shapeUnary (operation : Shape -> Shape)
  | shapeUnaryWithConfig (operation : Shape -> GameConfig -> Shape)
  | shapeUnaryPair (operation : Shape -> Shape × Shape)
  | shapeBinaryWithConfig (operation : Shape -> Shape -> GameConfig -> Shape)
  | shapeBinaryPair (operation : Shape -> Shape -> Shape × Shape)
  | shapeWithColor (operation : Shape -> Color -> Shape)
  | colorBinary (operation : Color -> Color -> Color)
  | discardShape

/-- マシンのポート仕様と抽象処理能力。 -/
structure MachineSpec where
  /-- マシン種別。 -/
  kind : MachineKind
  /-- 入出力ポート仕様。 -/
  ports : NodeSpec
  /-- 抽象処理能力。 -/
  capability : Capability
deriving Repr, DecidableEq, BEq

namespace MachineKind

/-- マシン種別に対応する入出力ポート仕様。 -/
def nodeSpec : MachineKind -> NodeSpec
  | rotator | reverseRotator | rotator180 | halfDestroyer | pinPusher =>
      { inputs := [PortSpec.belt "input"], outputs := [PortSpec.belt "output"] }
  | cutter =>
      { inputs := [PortSpec.belt "input"], outputs := [PortSpec.belt "east", PortSpec.belt "west"] }
  | stacker =>
      { inputs := [PortSpec.belt "bottom", PortSpec.belt "top"], outputs := [PortSpec.belt "output"] }
  | swapper =>
      { inputs := [PortSpec.belt "left", PortSpec.belt "right"],
        outputs := [PortSpec.belt "left", PortSpec.belt "right"] }
  | painter | crystalGenerator =>
      { inputs := [PortSpec.belt "shape", PortSpec.pipe "fluid"], outputs := [PortSpec.belt "output"] }
  | colorMixer =>
      { inputs := [PortSpec.pipe "left", PortSpec.pipe "right"], outputs := [PortSpec.pipe "output"] }
  | trash =>
      { inputs := [PortSpec.belt "input"], outputs := [] }

/-- マシン種別に対応する Operations facade 側の意味論。 -/
noncomputable def semantics : MachineKind -> MachineSemantics
  | rotator => MachineSemantics.shapeUnary Operations.rotator
  | reverseRotator => MachineSemantics.shapeUnary Shape.rotateCCW
  | rotator180 => MachineSemantics.shapeUnary Shape.rotate180
  | halfDestroyer => MachineSemantics.shapeUnary Shape.halfDestroy
  | pinPusher => MachineSemantics.shapeUnaryWithConfig Shape.pinPush
  | cutter => MachineSemantics.shapeUnaryPair Shape.cut
  | stacker => MachineSemantics.shapeBinaryWithConfig Shape.stack
  | swapper => MachineSemantics.shapeBinaryPair Shape.swap
  | painter => MachineSemantics.shapeWithColor Shape.paint
  | crystalGenerator => MachineSemantics.shapeWithColor Shape.crystallize
  | colorMixer => MachineSemantics.colorBinary Operations.mix
  | trash => MachineSemantics.discardShape

/-- 指定した抽象処理能力を持つ `MachineSpec` を作る。 -/
def machineSpec (kind : MachineKind) (capability : Capability) : MachineSpec :=
  { kind := kind, ports := kind.nodeSpec, capability := capability }

end MachineKind

end S2IL
