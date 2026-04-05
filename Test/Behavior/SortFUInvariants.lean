-- sortFallingUnits_shouldProcessBefore_order の厳密な反例チェック
-- 特に非推移的パターン: pin_a → cluster_u → pin_c だが pin_a ↛ pin_c
import S2IL.Behavior.Gravity

open Gravity

private def spb (a b : FallingUnit) : Bool :=
    Direction.all.any fun dir =>
        match a.minLayerAtDir dir, b.minLayerAtDir dir with
        | some la, some lb => la < lb
        | _, _ => false

private def posIn' (x : FallingUnit) (l : List FallingUnit) : Nat :=
    l.findIdx (fun y => decide (y = x))

-- 全順列
private def permutations : List FallingUnit → List (List FallingUnit)
    | [] => [[]]
    | x :: xs =>
        let perms := permutations xs
        perms.flatMap fun perm =>
            (List.range (perm.length + 1)).map fun i =>
                perm.take i ++ [x] ++ perm.drop i

private def checkSortFUOrder (label : String) (units : List FallingUnit) : IO Bool := do
    let sorted := sortFallingUnits units
    let mut ok := true
    for a in units do
        for b in units do
            if a != b && spb a b then
                let pa := posIn' a sorted
                let pb := posIn' b sorted
                if pa >= pb then
                    ok := false
                    let posA := a.positions.map (fun p => s!"({p.layer},{reprStr p.dir})")
                    let posB := b.positions.map (fun p => s!"({p.layer},{reprStr p.dir})")
                    IO.println s!"  {label} FAIL: spb({posA}->{posB}) pos {pa}>={pb}"
    return ok

def main : IO Unit := do
    IO.println "=== 非推移的パターンの反例チェック ===\n"

    -- 候補シェイプ: pin_a(1,NE) → cluster(2,NE+SE) → pin_c(3,SE)
    -- Layer 0: -------- (全空)
    -- Layer 1: P------- (NE=pin)
    -- Layer 2: CrCr---- (NE=Cr, SE=Cr)
    -- Layer 3: --P----- (SE=pin)
    let codes := [
        "--------:P-------:CrCr----:--P-----",
        -- variant with layer 0 having some grounded content
        "Cr------:P-------:CrCr----:--P-----",
        -- variant: pin at SW instead of SE
        "--------:P-------:CrCr----:----P---",
        -- all empty bottom, more separation
        "--------:--------:P-------:CrCr----",
        -- 5 layers for more clearance
        "--------:--------:P-------:CrCr----:--P-----"
    ]

    for code in codes do
        match Shape.ofString? code with
        | none => IO.println s!"  PARSE ERROR: {code}"
        | some s =>
            let fu := floatingUnits s
            IO.println s!"Shape: {code}"
            IO.println s!"  layers: {s.layerCount}, fU count: {fu.length}"

            -- FU の詳細
            for i in List.range fu.length do
                if h : i < fu.length then
                    let u := fu[i]
                    let ps := u.positions.map (fun p => s!"({p.layer},{reprStr p.dir})")
                    let dirs := u.positions.map (fun p => p.dir)
                    let minLayers := [Direction.ne, Direction.se, Direction.sw, Direction.nw].map fun d =>
                        s!"{reprStr d}={match u.minLayerAtDir d with | some l => toString l | none => "-"}"
                    IO.println s!"  fU[{i}]: minL={u.minLayer} pos={ps} minL=[{String.intercalate ", " minLayers}]"

            -- shouldProcessBefore 関係
            IO.println s!"  spb relations:"
            for a in fu do
                for b in fu do
                    if a != b then
                        let sp := spb a b
                        if sp then
                            let posA := a.positions.map (fun p => s!"({p.layer},{reprStr p.dir})")
                            let posB := b.positions.map (fun p => s!"({p.layer},{reprStr p.dir})")
                            IO.println s!"    spb({posA} -> {posB})"

            -- 全順列テスト
            if fu.length ≤ 6 then
                let perms := permutations fu
                let mut allOk := true
                let mut failCount := 0
                for perm in perms do
                    let ok ← checkSortFUOrder s!"perm" perm
                    if !ok then
                        allOk := false
                        failCount := failCount + 1
                if allOk then
                    IO.println s!"  ALL {perms.length} permutations OK"
                else
                    IO.println s!"  FAILED: {failCount}/{perms.length} permutations"
            IO.println ""

    IO.println "=== Done ==="
