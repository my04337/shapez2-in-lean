-- Benchmark: 反例チェックの各層数での実行時間を計測
-- `lake env lean --run Scratch/LayerBenchmark.lean` で実行
import S2IL

open Gravity

-- process_rotate180 の検証
def benchProcessRotate180 (shapes : List Shape) : IO Unit := do
    let mut violations := 0
    let mut total := 0
    for s in shapes do
        total := total + 1
        let lhs := (process s).map Shape.rotate180
        let rhs := process s.rotate180
        if lhs != rhs then
            violations := violations + 1
    IO.println s!"  process_rotate180: {total} shapes, {violations} violations"

-- sortFU foldl 結果の等価性検証（private 関数に依存しない方法）
def benchFoldlEq (shapes : List Shape) : IO Unit := do
    let mut violations := 0
    let mut total := 0
    for s in shapes do
        total := total + 1
        -- process は sortFU foldl 全体を含む。結果の一致 = foldl 等価
        let lhs := (process s).map Shape.rotate180
        let rhs := process s.rotate180
        if lhs != rhs then
            violations := violations + 1
            IO.println s!"    VIOLATION: {s}"
    IO.println s!"  foldl eq check: {total} shapes, {violations} violations"

-- 各層数でサンプルシェイプを生成
-- NE/SE のみ 3 パターン (empty, pin, crystal red) を使い、SW/NW は empty 固定
def sampleLayers2Dir (n : Nat) : List (List Layer) :=
    let simpleQuarters := [Quarter.empty, Quarter.pin, Quarter.crystal Color.red]
    let simpleLayers : List Layer := do
        let ne ← simpleQuarters
        let se ← simpleQuarters
        return Layer.mk ne se Quarter.empty Quarter.empty
    match n with
    | 0 => [[]]
    | n + 1 =>
        let rest := sampleLayers2Dir n
        do
            let l ← simpleLayers
            let ls ← rest
            return l :: ls

-- 4方角版サンプル（NE/SE/SW/NW 各2パターン → 16 layer/層）
def sampleLayers4Dir (n : Nat) : List (List Layer) :=
    let quarters := [Quarter.empty, Quarter.pin]
    let allLayers : List Layer := do
        let ne ← quarters
        let se ← quarters
        let sw ← quarters
        let nw ← quarters
        return Layer.mk ne se sw nw
    match n with
    | 0 => [[]]
    | n + 1 =>
        let rest := sampleLayers4Dir n
        do
            let l ← allLayers
            let ls ← rest
            return l :: ls

def mkShape (layers : List Layer) : Option Shape :=
    match h : layers with
    | [] => none
    | _ :: _ => some ⟨layers, by simp [h]⟩

def main : IO Unit := do
    IO.println "=== 2方角 (NE/SE) × 3パターン ベンチマーク ==="
    IO.println "(9^n shapes: 2L=81, 3L=729, 4L=6561, 5L=59049)"
    for numLayers in [2, 3, 4, 5] do
        let samples := sampleLayers2Dir numLayers
        let shapes := samples.filterMap mkShape
        IO.println s!"\n--- {numLayers} layers: {shapes.length} sample shapes ---"
        let start ← IO.monoMsNow
        benchFoldlEq shapes
        let mid ← IO.monoMsNow
        benchProcessRotate180 shapes
        let finish ← IO.monoMsNow
        IO.println s!"  foldl eq time: {mid - start} ms"
        IO.println s!"  process_r180 time: {finish - mid} ms"
        IO.println s!"  total time: {finish - start} ms"

    IO.println "\n\n=== 4方角 × 2パターン (empty/pin) ベンチマーク ==="
    IO.println "(16^n shapes: 2L=256, 3L=4096, 4L=65536, 5L=1048576)"
    for numLayers in [2, 3, 4] do
        let samples := sampleLayers4Dir numLayers
        let shapes := samples.filterMap mkShape
        IO.println s!"\n--- {numLayers} layers: {shapes.length} sample shapes ---"
        let start ← IO.monoMsNow
        benchFoldlEq shapes
        let mid ← IO.monoMsNow
        benchProcessRotate180 shapes
        let finish ← IO.monoMsNow
        IO.println s!"  foldl eq time: {mid - start} ms"
        IO.println s!"  process_r180 time: {finish - mid} ms"
        IO.println s!"  total time: {finish - start} ms"

    -- 8 層テスト（少量サンプル）
    IO.println "\n\n=== 8層 stress テスト (2方角 × 2パターン, 4^8=65536 shapes) ==="
    let stressQuarters := [Quarter.empty, Quarter.pin]
    let stressLayers : List Layer := do
        let ne ← stressQuarters
        let se ← stressQuarters
        return Layer.mk ne se Quarter.empty Quarter.empty
    let rec buildLayers : Nat → List (List Layer)
        | 0 => [[]]
        | n + 1 =>
            let rest := buildLayers n
            do
                let l ← stressLayers
                let ls ← rest
                return l :: ls
    let samples8 := buildLayers 8
    let shapes8 := samples8.filterMap mkShape
    IO.println s!"--- 8 layers: {shapes8.length} shapes ---"
    let start ← IO.monoMsNow
    benchProcessRotate180 shapes8
    let finish ← IO.monoMsNow
    IO.println s!"  process_r180 time: {finish - start} ms"
