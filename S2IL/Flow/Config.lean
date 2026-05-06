import S2IL.Flow.MachineSpec

/-!
# S2IL.Flow.Config

Shape Processing Flow の具体スループット値を差し込む設定層。

基本値の正本は `docs/shapez2/game-system-overview.md` に置き、このモジュールは
Flow 層から参照する preset として値を保持する。
-/

namespace S2IL

/-- Flow 速度設定の tier。 -/
structure SpeedTier where
  /-- 設定名。 -/
  name : String
  /-- 基本速度に対する整数倍率。 -/
  multiplier : Nat
deriving Repr, DecidableEq, BEq

namespace SpeedTier

/-- Shapez2 の基本速度 tier。 -/
def basic : SpeedTier :=
  { name := "basic", multiplier := 1 }

end SpeedTier

/-- Flow 層で使う具体スループット設定。 -/
structure FlowConfig where
  /-- 適用する速度 tier。 -/
  speedTier : SpeedTier
  /-- 通常ベルト 1 本ぶんの Shape 搬送量。 -/
  beltItemsPerMinute : FlowAmount
  /-- 液剤ランチャー / レシーバー 1 接続ぶんの液剤量。 -/
  pipeLauncherLitersPerMinute : FlowAmount
  /-- 宇宙パイプ 1 本ぶんの液剤量。 -/
  spacePipeLitersPerMinute : FlowAmount
  /-- 回転機 / 逆回転機 / 180 度回転機の Shape 処理量。 -/
  rotatorItemsPerMinute : FlowAmount
  /-- 切断処理機 / ピン押し機の Shape 処理量。 -/
  halfDestroyerItemsPerMinute : FlowAmount
  /-- 切断機 / スワップ機 / 積層機の Shape 処理量。 -/
  shapeAssemblerItemsPerMinute : FlowAmount
  /-- ミニ採掘機の Shape 産出量。 -/
  miniMinerItemsPerMinute : FlowAmount
  /-- ミニポンプの液剤産出量。 -/
  miniPumpLitersPerMinute : FlowAmount
  /-- 着色機の Shape 処理量。 -/
  painterItemsPerMinute : FlowAmount
  /-- 着色機 1 台あたりの液剤消費量。 -/
  painterLitersPerMinute : FlowAmount
  /-- 混色機 1 入力あたりの液剤処理量。 -/
  colorMixerInputLitersPerMinute : FlowAmount
  /-- 混色機の液剤出力量。 -/
  colorMixerOutputLitersPerMinute : FlowAmount
  /-- 結晶製造機の Shape 処理量。 -/
  crystalGeneratorItemsPerMinute : FlowAmount
  /-- 結晶製造機 1 台あたりの液剤消費量。 -/
  crystalGeneratorLitersPerMinute : FlowAmount
deriving Repr, DecidableEq, BEq

namespace FlowConfig

private def amount (units : Nat) : FlowAmount :=
  { units := units }

private def beltThroughputFrom (amount : FlowAmount) : Throughput :=
  { kind := StreamKind.belt, amount := amount }

private def pipeThroughputFrom (amount : FlowAmount) : Throughput :=
  { kind := StreamKind.pipe, amount := amount }

/-- Shapez2 基本速度に対応する Flow 設定 preset。 -/
def basic : FlowConfig :=
  { speedTier := SpeedTier.basic,
    beltItemsPerMinute := amount 120,
    pipeLauncherLitersPerMinute := amount 1200,
    spacePipeLitersPerMinute := amount 28800,
    rotatorItemsPerMinute := amount 60,
    halfDestroyerItemsPerMinute := amount 40,
    shapeAssemblerItemsPerMinute := amount 30,
    miniMinerItemsPerMinute := amount 30,
    miniPumpLitersPerMinute := amount 300,
    painterItemsPerMinute := amount 30,
    painterLitersPerMinute := amount 300,
    colorMixerInputLitersPerMinute := amount 300,
    colorMixerOutputLitersPerMinute := amount 600,
    crystalGeneratorItemsPerMinute := amount 20,
    crystalGeneratorLitersPerMinute := amount 400 }

/-- 通常ベルトの基準スループット。 -/
def beltThroughput (config : FlowConfig) : Throughput :=
  beltThroughputFrom config.beltItemsPerMinute

/-- 液剤ランチャー / レシーバーの基準スループット。 -/
def pipeLauncherThroughput (config : FlowConfig) : Throughput :=
  pipeThroughputFrom config.pipeLauncherLitersPerMinute

/-- マシン種別の主出力スループット。 -/
def machineThroughput? (config : FlowConfig) : MachineKind -> Option Throughput
  | MachineKind.rotator | MachineKind.reverseRotator | MachineKind.rotator180 =>
      some (beltThroughputFrom config.rotatorItemsPerMinute)
  | MachineKind.halfDestroyer | MachineKind.pinPusher =>
      some (beltThroughputFrom config.halfDestroyerItemsPerMinute)
  | MachineKind.cutter | MachineKind.stacker | MachineKind.swapper =>
      some (beltThroughputFrom config.shapeAssemblerItemsPerMinute)
  | MachineKind.painter =>
      some (beltThroughputFrom config.painterItemsPerMinute)
  | MachineKind.crystalGenerator =>
      some (beltThroughputFrom config.crystalGeneratorItemsPerMinute)
  | MachineKind.colorMixer =>
      some (pipeThroughputFrom config.colorMixerOutputLitersPerMinute)
  | MachineKind.trash => none

/-- マシン種別ごとの代表的な消費スループット。 -/
def machineConsumes (config : FlowConfig) : MachineKind -> List Throughput
  | MachineKind.painter => [pipeThroughputFrom config.painterLitersPerMinute]
  | MachineKind.crystalGenerator => [pipeThroughputFrom config.crystalGeneratorLitersPerMinute]
  | MachineKind.colorMixer =>
      [ pipeThroughputFrom config.colorMixerInputLitersPerMinute,
        pipeThroughputFrom config.colorMixerInputLitersPerMinute ]
  | _ => []

end FlowConfig

end S2IL
