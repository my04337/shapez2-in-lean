-- sortFallingUnits(perm).foldl が全順列で同じ結果を返すか検証
import S2IL.Behavior.Gravity

open Gravity

deriving instance Inhabited for FallingUnit

-- placeFallingUnit と landingDistance をローカルに使う
-- (private なので直接アクセスできない → processSettleStep を使う)

-- settle one unit into the obstacle
-- processSettleStep は public でないかもしれないので、代わりに sortFallingUnits + foldl を直接分解

-- foldl の結果を比較（全順列）
private def checkFoldlPermInvariant (label : String) (_s : Shape) (fus : List FallingUnit) (_obs : List Layer) : IO Bool := do
    let perms := fus.permutations
    if perms.isEmpty then return true
    -- 基準: 最初の順列
    let ref := sortFallingUnits perms.head!
    -- sortFallingUnits の結果自体は順列によって変わるので、foldl 結果を見るために
    -- process 関数全体を使う（obs は空リストから開始）
    -- ただし process は floatingUnits を内部で計算するので、任意の順列を入力できない
    -- → 代替: sortFallingUnits の結果を比較
    let mut allSame := true
    for perm in perms do
        let sorted := sortFallingUnits perm
        if sorted != ref then
            allSame := false
    if allSame then
        IO.println s!"{label}: sortFallingUnits output SAME for all {perms.length} permutations"
    else
        IO.println s!"{label}: sortFallingUnits output DIFFERS across permutations"
    return allSame

def main : IO Unit := do
    IO.println "=== sortFallingUnits 出力のperm不変性チェック ==="

    let testShapes : List (String × String) := [
        ("1pin", "--------:--P-----"),
        ("2pin_diff", "--------:P-P-----"),
        ("nontrans", "--------:P-------:CrCr----:--P-----"),
        ("cross_pin", "CrCr----:P---P---"),
        ("full3", "--------:P-P-----:CrCrCrCr:--P---P-"),
        ("3layer", "--------:CrCr----:----CrCr"),
        ("diag_clust", "Cr------:------Cr")
    ]
    for (label, code) in testShapes do
        match Shape.ofString? code with
        | none => IO.println s!"SKIP {label}: parse failed"
        | some s =>
            let fus := floatingUnits s
            IO.println s!"{label}: {fus.length} units"
            let _ ← checkFoldlPermInvariant label s fus []

    IO.println "=== チェック完了 ==="
