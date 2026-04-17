-- sortFallingUnits_shouldProcessBefore_order の反例チェック（insertSorted 修正後）
import S2IL.Behavior.Gravity

open Gravity (FallingUnit sortFallingUnits floatingUnits)

private def spb (a b : FallingUnit) : Bool :=
    Direction.all.any fun dir =>
        match a.minLayerAtDir dir, b.minLayerAtDir dir with
        | some la, some lb => la < lb
        | _, _ => false

-- posIn（Gravity.lean の private をローカルに再定義）
private def posIn (x : FallingUnit) (l : List FallingUnit) : Nat :=
    l.findIdx (fun y => decide (y = x))

-- sortFallingUnits の shouldProcessBefore order チェック: shouldProcessBefore(a,b) なら posIn a < posIn b
private def checkSortFUOrder (label : String) (units : List FallingUnit) : IO Bool := do
    let sorted := sortFallingUnits units
    let mut ok := true
    for a in units do
        for b in units do
            if a != b && spb a b then
                let pa := posIn a sorted
                let pb := posIn b sorted
                if pa >= pb then
                    ok := false
                    let posA := a.positions.map (fun p => s!"({p.layer},{reprStr p.dir})")
                    let posB := b.positions.map (fun p => s!"({p.layer},{reprStr p.dir})")
                    IO.println s!"  {label} FAIL: spb({posA}->{posB}) pos {pa}>={pb}"
    return ok

-- 全順列チェック
private def permutations : List FallingUnit → List (List FallingUnit)
    | [] => [[]]
    | x :: xs =>
        let perms := permutations xs
        perms.flatMap fun perm =>
            (List.range (perm.length + 1)).map fun i =>
                perm.take i ++ [x] ++ perm.drop i

def main : IO Unit := do
    IO.println "=== sortFallingUnits_shouldProcessBefore_order 反例チェック (insertSorted 修正後) ===\n"

    -- テストシェイプ
    let codes := [
        "--------:CrCr----:P---P---",
        "--------:CrCr----:Cr------:P---P---",
        "--------:CrCr----:P-----P-",
        "--------:CrCr----:--P-P---",
        "--------:CrCr----:P-P-----",
        "CrCr----:----CrCr",
        "--------:CuCuCuCu",
        "Cr------:--------:------Cr",
        "CrCrCrCr:--------:CrCrCrCr",
        "Cu------:----Cu--:--Cu----:------Cu",
        "--------:--CrCr--:--Cr----:Cr------:CrCr----"
    ]

    for code in codes do
        match Shape.ofString? code with
        | none => IO.println s!"  PARSE ERROR: {code}"
        | some s =>
            let fu := floatingUnits s
            IO.println s!"Shape: {code} (fU count: {fu.length})"

            -- 全順列テスト
            if fu.length ≤ 6 then
                let perms := permutations fu
                let mut allOk := true
                let mut failCount := 0
                for perm in perms do
                    let ok ← checkSortFUOrder s!"{code} perm" perm
                    if !ok then
                        allOk := false
                        failCount := failCount + 1
                if allOk then
                    IO.println s!"  ALL {perms.length} permutations OK"
                else
                    IO.println s!"  FAILED: {failCount}/{perms.length} permutations"
            else
                -- fU が多い場合は自然順序のみ
                let ok ← checkSortFUOrder code fu
                IO.println s!"  natural order: {if ok then "OK" else "FAIL"}"

            -- rotate180 版も
            let fur := floatingUnits s.rotate180
            if fur.length ≤ 6 then
                let perms := permutations fur
                let mut allOk := true
                let mut failCount := 0
                for perm in perms do
                    let ok ← checkSortFUOrder s!"{code}.r180 perm" perm
                    if !ok then
                        allOk := false
                        failCount := failCount + 1
                if allOk then
                    IO.println s!"  r180: ALL {perms.length} permutations OK"
                else
                    IO.println s!"  r180: FAILED: {failCount}/{perms.length} permutations"
            else
                let ok ← checkSortFUOrder s!"{code}.r180" fur
                IO.println s!"  r180 natural order: {if ok then "OK" else "FAIL"}"

            IO.println ""

    IO.println "=== Done ==="
