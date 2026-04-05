-- foldl settle の順列不変性の破綻を確認するテスト
-- 反例候補: 4つの独立浮遊ユニットで sortFU 順序依存性を示す
import S2IL.Behavior.Gravity

open Gravity

deriving instance Inhabited for FallingUnit

def main : IO Unit := do
    IO.println "=== foldl settle 順列不変性テスト ==="

    -- 反例候補: 8層シェイプ
    -- L0:empty, L1:pin@ne, L2:empty, L3:Cr@ne,se, L4:empty, L5:Cr@se,sw, L6:empty, L7:pin@sw
    let code1 := "--------:P-------:--------:CrCr----:--------:--CrCr--:--------:----P---"

    match Shape.ofString? code1 with
    | none => IO.println "PARSE FAILED"
    | some s =>
        let fus := floatingUnits s
        IO.println s!"Shape: {code1}"
        IO.println s!"floatingUnits count: {fus.length}"
        for i in List.range fus.length do
            IO.println s!"  fU[{i}]: positions={repr fus[i]!.positions}"

        -- process(s).map r180 == process(s.r180) ?
        let lhs := (process s).map Shape.rotate180
        let rhs := process s.rotate180
        IO.println s!"process_r180_comm: {lhs == rhs}"

        -- floatingUnits(s.r180)
        let fus_r := floatingUnits s.rotate180
        IO.println s!"floatingUnits(s.r180) count: {fus_r.length}"
        for i in List.range fus_r.length do
            IO.println s!"  fU_r[{i}]: positions={repr fus_r[i]!.positions}"

        -- sortFU results
        let sorted := sortFallingUnits fus
        let sorted_r := sortFallingUnits fus_r
        IO.println s!"sortFU(fU(s)): {repr (sorted.map (·.positions))}"
        IO.println s!"sortFU(fU(s.r180)): {repr (sorted_r.map (·.positions))}"

    -- 他のテストケース: process_r180 が成立するか
    let extras := [
        ("counter1", "--------:P-------:--------:CrCr----:--------:--CrCr--:--------:----P---"),
        ("counter2", "--------:P-------:--------:CrCr----:--------:--CrCr--:----P---"),
        ("counter3", "--------:--P-----:CrCr----:--------:----CrCr:P-------")
    ]
    for (label, code) in extras do
        match Shape.ofString? code with
        | none => IO.println s!"SKIP {label}"
        | some s =>
            let lhs := (process s).map Shape.rotate180
            let rhs := process s.rotate180
            IO.println s!"{label}: process_r180={lhs == rhs}, fU={floatingUnits s |>.length}"

    IO.println "=== テスト完了 ==="
