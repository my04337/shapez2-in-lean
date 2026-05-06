import S2IL.Flow

/-!
# Test.Flow.Capability

Flow の抽象処理能力と必要台数下界計算の代表テスト。
-/

open S2IL

namespace Test.Flow.Capability

private def amount120 : FlowAmount := { units := 120 }
private def amount60 : FlowAmount := { units := 60 }
private def amount40 : FlowAmount := { units := 40 }
private def amount0 : FlowAmount := { units := 0 }

private def beltThroughput120 : Throughput :=
  { kind := StreamKind.belt, amount := amount120 }

private def beltThroughput60 : Throughput :=
  { kind := StreamKind.belt, amount := amount60 }

private def beltThroughput40 : Throughput :=
  { kind := StreamKind.belt, amount := amount40 }

private def pipeThroughput40 : Throughput :=
  { kind := StreamKind.pipe, amount := amount40 }

private def minBasicMachineCount? (target : Throughput) (kind : MachineKind) : Option Nat :=
  match FlowConfig.basic.machineThroughput? kind with
  | some machine => minMachineCount target machine
  | none => none

private def addCount? (left right : Option Nat) : Option Nat :=
  match left, right with
  | some left, some right => some (left + right)
  | _, _ => none

private def mulCount? (factor : Nat) (count : Option Nat) : Option Nat :=
  match count with
  | some count => some (factor * count)
  | none => none

private def sumCounts? (counts : List (Option Nat)) : Option Nat :=
  counts.foldl addCount? (some 0)

-- ============================================================
-- ceiling division
-- ============================================================

#guard ceilDiv amount120 amount40 == some 3
#guard ceilDiv amount120 amount60 == some 2
#guard ceilDiv amount120 amount0 == none

-- ============================================================
-- single-machine lower bound
-- ============================================================

#guard minMachineCount beltThroughput120 beltThroughput40 == some 3
#guard minMachineCount beltThroughput120 beltThroughput60 == some 2
#guard minMachineCount beltThroughput120 pipeThroughput40 == none

-- ============================================================
-- quadrant extraction representative lower bound
-- ============================================================

private def quadrantExtractionMachineCount? : Option Nat :=
  sumCounts?
    [ minBasicMachineCount? beltThroughput120 MachineKind.halfDestroyer,
      minBasicMachineCount? beltThroughput120 MachineKind.reverseRotator,
      minBasicMachineCount? beltThroughput120 MachineKind.halfDestroyer ]

#guard minBasicMachineCount? beltThroughput120 MachineKind.halfDestroyer == some 3
#guard minBasicMachineCount? beltThroughput120 MachineKind.reverseRotator == some 2
#guard quadrantExtractionMachineCount? == some 8

-- ============================================================
-- 4-layer end-to-end representative lower bound
-- ============================================================

private def diagonalSplitMachineCount? : Option Nat :=
  sumCounts?
    [ minBasicMachineCount? beltThroughput60 MachineKind.cutter,
      mulCount? 2 (minBasicMachineCount? beltThroughput60 MachineKind.rotator),
      minBasicMachineCount? beltThroughput60 MachineKind.swapper,
      minBasicMachineCount? beltThroughput60 MachineKind.rotator ]

private def diagonalSplitX2MachineCount? : Option Nat :=
  mulCount? 2 diagonalSplitMachineCount?

private def stackerStagesMachineCount? : Option Nat :=
  mulCount? 3 (minBasicMachineCount? beltThroughput120 MachineKind.stacker)

private def painterFluidLauncherCoverage? : Option Nat :=
  match FlowConfig.basic.machineConsumes MachineKind.painter with
  | painterFluid :: _ => minMachineCount (FlowConfig.basic.pipeLauncherThroughput) painterFluid
  | [] => none

private def fourLayerEndToEndMachineCount? : Option Nat :=
  sumCounts?
    [ minBasicMachineCount? beltThroughput120 MachineKind.painter,
      diagonalSplitX2MachineCount?,
      stackerStagesMachineCount? ]

#guard minBasicMachineCount? beltThroughput120 MachineKind.painter == some 4
#guard painterFluidLauncherCoverage? == some 4
#guard minBasicMachineCount? beltThroughput60 MachineKind.cutter == some 2
#guard minBasicMachineCount? beltThroughput60 MachineKind.rotator == some 1
#guard minBasicMachineCount? beltThroughput60 MachineKind.swapper == some 2
#guard diagonalSplitMachineCount? == some 7
#guard diagonalSplitX2MachineCount? == some 14
#guard minBasicMachineCount? beltThroughput120 MachineKind.stacker == some 4
#guard stackerStagesMachineCount? == some 12
#guard fourLayerEndToEndMachineCount? == some 30

end Test.Flow.Capability
