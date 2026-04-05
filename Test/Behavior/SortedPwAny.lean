-- sortFU((fU s).map r180) vs sortFU(fU(s.r180)) の pointwise .any 比較
import S2IL.Behavior.Gravity

open Gravity

-- FallingUnit の .any プロファイルを比較
private def anyEquiv (u v : FallingUnit) : Bool :=
    let allPs := u.positions ++ v.positions
    allPs.all fun p =>
        u.positions.any (· == p) == v.positions.any (· == p)

private def r180fu (u : FallingUnit) : FallingUnit :=
    match u with
    | .cluster ps => .cluster (ps.map QuarterPos.rotate180)
    | .pin p => .pin p.rotate180

def main : IO Unit := do
    IO.println "=== sortFU output pointwise .any 比較 ===\n"

    let codes := [
        "--------:P-------:CrCr----:--P-----",
        "--------:--------:P-------:CrCr----:--P-----",
        "--------:CrCr----:P---P---",
        "--------:CrCr----:Cr------:P---P---",
        "--------:CrCr----:P-----P-",
        "--------:CrCr----:--P-P---",
        "CrCr----:----CrCr",
        "--------:CuCuCuCu",
        "Cr------:--------:------Cr",
        "CrCrCrCr:--------:CrCrCrCr",
        "Cu------:----Cu--:--Cu----:------Cu",
        "--------:--CrCr--:--Cr----:Cr------:CrCr----",
        "--------:P-------:----CrCr:------P-",
        "--------:--P-----:CrCr----:P-------",
        "--------:------P-:----CrCr:P-------",
        "--------:P-P-----:CrCrCrCr:--P---P-",
        "--------:Cr------:Cr------:--------",
        "--------:CrCr----:CrCr----",
        "--------:P-------",
        "P-------:--------:------P-",
        "--------:CrCrCrCr:--------:CrCrCrCr"
    ]

    let mut allPwAny := true
    for code in codes do
        match Shape.ofString? code with
        | none => IO.println s!"  PARSE ERROR: {code}"
        | some s =>
            let l1 := (floatingUnits s).map r180fu
            let l2 := floatingUnits s.rotate180
            let sl1 := sortFallingUnits l1
            let sl2 := sortFallingUnits l2

            let eq_len := sl1.length == sl2.length
            let mut pw_any := eq_len
            if eq_len then
                for i in List.range sl1.length do
                    if h1 : i < sl1.length then
                        if h2 : i < sl2.length then
                            if !anyEquiv sl1[i] sl2[i] then
                                pw_any := false

            let marker := if sl1 == sl2 then "=" else if pw_any then "~" else "✗"
            if !pw_any then allPwAny := false
            IO.println s!"{marker} {code} (fU={l1.length})"
            if !pw_any then
                for i in List.range (max sl1.length sl2.length) do
                    if h1 : i < sl1.length then
                        let u1 := sl1[i]
                        let ps1 := u1.positions.map (fun p => s!"({p.layer},{reprStr p.dir})")
                        if h2 : i < sl2.length then
                            let u2 := sl2[i]
                            let ps2 := u2.positions.map (fun p => s!"({p.layer},{reprStr p.dir})")
                            IO.println s!"  [{i}]: any={anyEquiv u1 u2} sl1={ps1} sl2={ps2}"

    IO.println s!"\n{if allPwAny then "ALL SORTED OUTPUTS POINTWISE .any EQUIV ✓" else "SOME DIFFER"}"
