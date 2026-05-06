import S2IL.Flow.Capability

/-!
# S2IL.Flow.Internal.CapabilityAlgebra

Shape Processing Flow の処理能力解析で使う最小限の自然数計算。

初期段階では、単一ストリームの要求量と 1 台あたり処理量から必要台数の
下界を計算する。
-/

namespace S2IL

/-- `target / perMachine` の切り上げ除算。

`perMachine.units = 0` の場合は処理能力がないため `none` を返す。 -/
def ceilDiv (target perMachine : FlowAmount) : Option Nat :=
  match perMachine.units with
  | 0 => none
  | perMachineUnits + 1 => some ((target.units + perMachineUnits) / (perMachineUnits + 1))

/-- 同一ストリーム種別の要求に対する単一マシン必要台数の下界。 -/
def minMachineCount (target machine : Throughput) : Option Nat :=
  if target.kind == machine.kind then
    ceilDiv target.amount machine.amount
  else
    none

end S2IL
