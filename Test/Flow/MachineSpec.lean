-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Flow

/-!
# Test.Flow.MachineSpec

Flow マシン仕様の代表テスト。
-/

open S2IL

namespace Test.Flow.MachineSpec

private def amount1 : FlowAmount := { units := 1 }

private def beltThroughput : Throughput :=
  { kind := StreamKind.belt, amount := amount1 }

private def beltCapacity : Capacity :=
  { kind := StreamKind.belt, amount := amount1 }

private def capability : Capability :=
  { throughput := beltThroughput,
    inputCapacity := beltCapacity,
    outputCapacity := beltCapacity,
    requires := [], consumes := [], produces := [] }

private def inputKinds (kind : MachineKind) : List StreamKind :=
  kind.nodeSpec.inputs.map (fun port => port.kind)

private def outputKinds (kind : MachineKind) : List StreamKind :=
  kind.nodeSpec.outputs.map (fun port => port.kind)

-- ============================================================
-- PortSpec helpers
-- ============================================================

#guard PortSpec.belt "input" == { kind := StreamKind.belt, name := "input" }
#guard PortSpec.pipe "fluid" == { kind := StreamKind.pipe, name := "fluid" }

-- ============================================================
-- MachineKind.nodeSpec
-- ============================================================

#guard inputKinds MachineKind.rotator == [StreamKind.belt]
#guard outputKinds MachineKind.rotator == [StreamKind.belt]

#guard inputKinds MachineKind.cutter == [StreamKind.belt]
#guard outputKinds MachineKind.cutter == [StreamKind.belt, StreamKind.belt]

#guard inputKinds MachineKind.stacker == [StreamKind.belt, StreamKind.belt]
#guard outputKinds MachineKind.stacker == [StreamKind.belt]

#guard inputKinds MachineKind.painter == [StreamKind.belt, StreamKind.pipe]
#guard outputKinds MachineKind.painter == [StreamKind.belt]

#guard inputKinds MachineKind.colorMixer == [StreamKind.pipe, StreamKind.pipe]
#guard outputKinds MachineKind.colorMixer == [StreamKind.pipe]

#guard inputKinds MachineKind.trash == [StreamKind.belt]
#guard outputKinds MachineKind.trash == []

-- ============================================================
-- Operations facade との対応
-- ============================================================

noncomputable example :
    MachineKind.rotator.semantics = MachineSemantics.shapeUnary Operations.rotator := rfl

noncomputable example :
    MachineKind.stacker.semantics = MachineSemantics.shapeBinaryWithConfig Shape.stack := rfl

noncomputable example :
    MachineKind.colorMixer.semantics = MachineSemantics.colorBinary Operations.mix := rfl

-- ============================================================
-- MachineSpec construction
-- ============================================================

private def rotatorSpec : MachineSpec :=
  MachineKind.rotator.machineSpec capability

#guard rotatorSpec.kind == MachineKind.rotator
#guard rotatorSpec.ports == MachineKind.rotator.nodeSpec
#guard rotatorSpec.capability == capability

end Test.Flow.MachineSpec
