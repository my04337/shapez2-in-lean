-- mutual spb の不可能性チェック
-- 同一シェイプの異なる floatingUnit 間で spb(a,b)=true ∧ spb(b,a)=true が成立するか
import S2IL.Behavior.Gravity

open Gravity

deriving instance Inhabited for FallingUnit

private def spb (a b : FallingUnit) : Bool :=
    Direction.all.any fun dir =>
        match a.minLayerAtDir dir, b.minLayerAtDir dir with
        | some la, some lb => la < lb
        | _, _ => false

-- 網羅的なシェイプ生成（2-4 レイヤ, 各象限を empty/pin/crystal で試す）
-- 計算量を抑えるため 2-3 レイヤに限定
private def allQuarterTypes : List Quarter := [.empty, .pin, .crystal .red]

private def allLayers2 : List (Layer × Layer) :=
    allQuarterTypes.flatMap fun ne1 =>
    allQuarterTypes.flatMap fun se1 =>
    allQuarterTypes.flatMap fun sw1 =>
    allQuarterTypes.flatMap fun nw1 =>
    allQuarterTypes.flatMap fun ne2 =>
    allQuarterTypes.flatMap fun se2 =>
    allQuarterTypes.flatMap fun sw2 =>
    allQuarterTypes.map fun nw2 =>
        (⟨ne1, se1, sw1, nw1⟩, ⟨ne2, se2, sw2, nw2⟩)

def main : IO Unit := do
    IO.println "=== mutual spb チェック ==="
    let mut mutualCount := 0
    let mut totalShapes := 0
    let mut totalPairs := 0

    -- 2レイヤ全探索
    for (l1, l2) in allLayers2 do
        let s : Shape := ⟨[l1, l2], by simp⟩
        totalShapes := totalShapes + 1
        let fus := floatingUnits s
        for a in fus do
            for b in fus do
                if a != b then
                    totalPairs := totalPairs + 1
                    if spb a b && spb b a then
                        mutualCount := mutualCount + 1
                        IO.println s!"MUTUAL SPB: shape={s.toString}"

    IO.println s!"2-layer: shapes={totalShapes}, pairs={totalPairs}, mutual={mutualCount}"

    -- 手動テスト: 非推移的パターン
    let extra := ["--------:P-------:CrCr----:--P-----",
                   "--------:P-P-----:CrCrCrCr:--P---P-",
                   "CrCr----:P---P---",
                   "--------:CrCr----:----CrCr",
                   "Cr------:------Cr"]
    for code in extra do
        match Shape.ofString? code with
        | none => IO.println s!"SKIP: {code}"
        | some s =>
            let fus := floatingUnits s
            for a in fus do
                for b in fus do
                    if a != b && spb a b && spb b a then
                        IO.println s!"MUTUAL SPB: {code}"

    -- 3レイヤ: サンプリング（全探索は 3^12 ≈ 500K）
    -- 各象限を3種で、3レイヤ → 3^12 = 531441。時間かかるので省略
    IO.println "=== チェック完了 ==="
