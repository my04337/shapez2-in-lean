-- sortFU_later_not_spb_earlier の反例チェック
-- sortFU 出力で j > i のとき spb(output[j], output[i]) = false を検証
import S2IL.Behavior.Gravity

open Gravity

deriving instance Inhabited for FallingUnit

-- shouldProcessBefore をローカルに再定義（private なので）
private def spb (a b : FallingUnit) : Bool :=
    Direction.all.any fun dir =>
        match a.minLayerAtDir dir, b.minLayerAtDir dir with
        | some la, some lb => la < lb
        | _, _ => false

-- sortFU 出力で sortFU_later_not_spb_earlier が成り立つかチェック
private def checkLaterNotSpb (label : String) (fus : List FallingUnit) : IO Unit := do
    -- 全順列を生成してチェック
    let perms := fus.permutations
    for perm in perms do
        let sorted := sortFallingUnits perm
        for i in List.range sorted.length do
            for j in List.range sorted.length do
                if i < j then
                    let a := sorted[i]!
                    let b := sorted[j]!
                    if spb b a then
                        IO.println s!"FAIL {label}: perm input order matters, i={i}, j={j}, spb(sorted[{j}], sorted[{i}])=true"

def main : IO Unit := do
    IO.println "=== sortFU_later_not_spb_earlier 反例チェック ==="

    -- テストシェイプのコード文字列
    let testShapes : List (String × String) := [
        ("empty2", "--------:--------"),
        ("1pin", "--------:--P-----"),
        ("2pin_diff", "--------:P-P-----"),
        ("nontrans", "--------:P-------:CrCr----:--P-----"),
        ("cross_pin", "CrCr----:P---P---"),
        ("full3", "--------:P-P-----:CrCrCrCr:--P---P-"),
        ("clust_diag", "Cr------:------Cr"),
        ("3layer", "--------:CrCr----:----CrCr")
    ]
    for (label, code) in testShapes do
        match Shape.ofString? code with
        | none => IO.println s!"SKIP {label}: parse failed"
        | some s =>
            let fus := floatingUnits s
            IO.println s!"{label}: {fus.length} units, {fus.permutations.length} perms"
            checkLaterNotSpb label fus

    IO.println "=== チェック完了 ==="
