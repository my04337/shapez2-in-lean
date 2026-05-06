import S2IL.Flow

/-!
# Test.Flow.Config

Flow の具体スループット設定層の代表テスト。
-/

open S2IL

namespace Test.Flow.Config

#guard FlowConfig.basic.speedTier == SpeedTier.basic
#guard FlowConfig.basic.beltItemsPerMinute.units == 120
#guard FlowConfig.basic.pipeLauncherLitersPerMinute.units == 1200
#guard FlowConfig.basic.rotatorItemsPerMinute.units == 60
#guard FlowConfig.basic.halfDestroyerItemsPerMinute.units == 40
#guard FlowConfig.basic.shapeAssemblerItemsPerMinute.units == 30
#guard FlowConfig.basic.painterLitersPerMinute.units == 300
#guard FlowConfig.basic.colorMixerOutputLitersPerMinute.units == 600
#guard FlowConfig.basic.crystalGeneratorItemsPerMinute.units == 20

#guard (FlowConfig.basic.machineThroughput? MachineKind.rotator).map (fun throughput => throughput.amount.units) ==
  some 60
#guard (FlowConfig.basic.machineThroughput? MachineKind.cutter).map (fun throughput => throughput.amount.units) ==
  some 30
#guard (FlowConfig.basic.machineThroughput? MachineKind.colorMixer).map (fun throughput => throughput.kind) ==
  some StreamKind.pipe
#guard FlowConfig.basic.machineThroughput? MachineKind.trash == none
#guard (FlowConfig.basic.machineConsumes MachineKind.painter).map (fun throughput => throughput.amount.units) ==
  [300]

end Test.Flow.Config
