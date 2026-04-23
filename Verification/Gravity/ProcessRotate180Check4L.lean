-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- process_rotate180 の 4L 全数検証スクリプト
-- 実行: lake env lean --run Verification/Gravity/ProcessRotate180Check4L.lean
--
-- 検証結果 (2026-04-05):
--   1L (3-type): 81 shapes, 0 failures
--   2L (3-type): 6,561 shapes, 0 failures
--   3L (3-type): 531,441 shapes, 0 failures
--   4L (2-type): 65,536 shapes, 0 failures
--   4L (pin-layer0): 331,776 shapes, 0 failures
--   4L (pin-layer1): 331,776 shapes, 0 failures
--   4L (pin-layer2): 331,776 shapes, 0 failures
--   4L (pin-layer3): 331,776 shapes, 0 failures
--   Structural coverage: 24 shapes, 0 failures
--   合計: 1,930,747 shapes, 0 failures

import S2IL.Operations.Gravity

open Gravity

-- ============================================================
-- 代表象限（重力挙動の全類型をカバー）
-- ============================================================

-- 3 代表: empty / pin / crystal（重力挙動の全分岐をカバー）
--   empty: isEmpty=true, canFormBond=false
--   pin:   isEmpty=false, canFormBond=false, isPin=true
--   crystal: isEmpty=false, canFormBond=true, isPin=false
private def repQuarters3 : Array Quarter :=
    #[Quarter.empty, Quarter.pin, Quarter.crystal Color.red]

-- 2 代表: empty / crystal（構造のみ、ピン省略）
private def repQuarters2 : Array Quarter :=
    #[Quarter.empty, Quarter.crystal Color.red]

-- ============================================================
-- 代表レイヤの生成
-- ============================================================

private def genLayers (qs : Array Quarter) : Array Layer := Id.run do
    let mut result : Array Layer := #[]
    for ne in qs do
        for se in qs do
            for sw in qs do
                for nw in qs do
                    result := result.push ⟨ne, se, sw, nw⟩
    return result

-- ============================================================
-- テスト関数
-- ============================================================

/-- process_rotate180 が成立するかテスト -/
private def testShape (s : Shape) : Bool :=
    (Gravity.process s).map Shape.rotate180 == Gravity.process s.rotate180

/-- テスト結果の集計 -/
structure TestResult where
    label : String
    tested : Nat
    failures : Nat
    firstFailure : Option String

instance : ToString TestResult where
    toString r :=
        if r.failures > 0 then
            s!"  FAIL: {r.label}: {r.failures}/{r.tested} failures. First: {r.firstFailure.getD "?"}"
        else
            s!"  OK: {r.label}: {r.tested} shapes, 0 failures"

-- ============================================================
-- Phase 1: 1L 全数 (3-type, 81 shapes)
-- ============================================================

private def test1L (layers : Array Layer) : IO TestResult := do
    let mut tested := 0
    let mut failures := 0
    let mut firstFail : Option String := none
    for l1 in layers do
        match Shape.ofLayers [l1] with
        | none => pure ()
        | some s =>
            tested := tested + 1
            if !(testShape s) then
                failures := failures + 1
                if firstFail.isNone then firstFail := some s.toString
    return { label := "1L (3-type)", tested, failures, firstFailure := firstFail }

-- ============================================================
-- Phase 2: 2L 全数 (3-type, 6561 shapes)
-- ============================================================

private def test2L (layers : Array Layer) : IO TestResult := do
    let mut tested := 0
    let mut failures := 0
    let mut firstFail : Option String := none
    for l1 in layers do
        for l2 in layers do
            match Shape.ofLayers [l1, l2] with
            | none => pure ()
            | some s =>
                tested := tested + 1
                if !(testShape s) then
                    failures := failures + 1
                    if firstFail.isNone then firstFail := some s.toString
    return { label := "2L (3-type)", tested, failures, firstFailure := firstFail }

-- ============================================================
-- Phase 3: 3L 全数 (3-type, 531441 shapes)
-- ============================================================

private def test3L (layers : Array Layer) : IO TestResult := do
    let mut tested := 0
    let mut failures := 0
    let mut firstFail : Option String := none
    let total := layers.size * layers.size * layers.size
    for l1 in layers do
        for l2 in layers do
            for l3 in layers do
                match Shape.ofLayers [l1, l2, l3] with
                | none => pure ()
                | some s =>
                    tested := tested + 1
                    if !(testShape s) then
                        failures := failures + 1
                        if firstFail.isNone then firstFail := some s.toString
        -- 進捗表示（外側ループごと）
        if tested % 50000 < layers.size * layers.size then
            IO.eprint s!"\r  3L: {tested}/{total}..."
    IO.eprintln ""
    return { label := "3L (3-type)", tested, failures, firstFailure := firstFail }

-- ============================================================
-- Phase 4: 4L 全数 (2-type, 65536 shapes)
-- ============================================================

private def test4L2Type (layers : Array Layer) : IO TestResult := do
    let mut tested := 0
    let mut failures := 0
    let mut firstFail : Option String := none
    for l1 in layers do
        for l2 in layers do
            for l3 in layers do
                for l4 in layers do
                    match Shape.ofLayers [l1, l2, l3, l4] with
                    | none => pure ()
                    | some s =>
                        tested := tested + 1
                        if !(testShape s) then
                            failures := failures + 1
                            if firstFail.isNone then firstFail := some s.toString
    return { label := "4L (2-type)", tested, failures, firstFailure := firstFail }

-- ============================================================
-- Phase 5: 4L ピン集中テスト
-- 1層をピン含む3-type、残り3層を2-type で検証
-- ============================================================

private def test4LPinLayer (pinLayers : Array Layer) (baseLayers : Array Layer)
        (pinPos : Nat) : IO TestResult := do
    let mut tested := 0
    let mut failures := 0
    let mut firstFail : Option String := none
    let allLayers := #[baseLayers, baseLayers, baseLayers, baseLayers].set! pinPos pinLayers
    for l0 in allLayers[0]! do
        for l1 in allLayers[1]! do
            for l2 in allLayers[2]! do
                for l3 in allLayers[3]! do
                    match Shape.ofLayers [l0, l1, l2, l3] with
                    | none => pure ()
                    | some s =>
                        tested := tested + 1
                        if !(testShape s) then
                            failures := failures + 1
                            if firstFail.isNone then firstFail := some s.toString
    return { label := s!"4L (pin-layer{pinPos})", tested, failures, firstFailure := firstFail }

-- ============================================================
-- Phase 6: 構造的カバレッジ（手作りケース）
-- ============================================================

private def structuralCoverageTests : Array String := #[
    -- 空レイヤ混在
    "--------:CrCrCrCr:--------:CrCrCrCr",
    "CrCrCrCr:--------:CrCrCrCr:--------",
    "--------:--------:--------:CrCrCrCr",
    "CrCrCrCr:--------:--------:--------",
    -- 大規模クラスタ（全象限充填）
    "CrCrCrCr:CrCrCrCr:CrCrCrCr:CrCrCrCr",
    "SrSrSrSr:SrSrSrSr:SrSrSrSr:SrSrSrSr",
    "WrWrWrWr:WrWrWrWr:WrWrWrWr:WrWrWrWr",
    -- 複数独立クラスタ
    "Cr--Cr--:--------:--Cr--Cr",
    "Cr------:--------:------Cr:--------",
    "Cr------:------Cr:Cr------:------Cr",
    -- ピン集中
    "P-P-P-P-:--------:P-P-P-P-",
    "P-P-P-P-:P-P-P-P-:P-P-P-P-:P-P-P-P-",
    "P-------:--------:--------:-------P-",
    "P-P-----:--P-P---:----P-P-:------P-P-",
    -- 混合方角（NE/SW のみ使用）
    "Cr----Cr:--------:Cr----Cr",
    "Cr------:--------:------Cr",
    "--Cr--Cr:--------:Cr--Cr--",
    -- ピンとクリスタルの混合
    "P-Cr----:--------:----CrP-",
    "CrP-CrP-:P-CrP-Cr",
    "P-CrP-Cr:CrP-CrP-:P-CrP-Cr:CrP-CrP-",
    -- 5レイヤ（vanilla5 レベル）
    "Cr------:--------:--------:--------:------Cr",
    "CrCrCrCr:--------:--------:--------:CrCrCrCr",
    "P-P-P-P-:--------:--------:--------:P-P-P-P-",
    "Cr------:P-------:--------:-------P-:------Cr",
    -- 複数チェーン（落下距離が異なる）
    "Cr------:------Cr:--------:--------",
    "CrCr----:--------:----CrCr:--------",
    "--------:Cr------:--------:------Cr"
]

private def testStructural : IO TestResult := do
    let mut tested := 0
    let mut failures := 0
    let mut firstFail : Option String := none
    for code in structuralCoverageTests do
        match Shape.ofString? code with
        | none => pure ()
        | some s =>
            tested := tested + 1
            if !(testShape s) then
                failures := failures + 1
                if firstFail.isNone then firstFail := some code
    return { label := "Structural coverage", tested, failures, firstFailure := firstFail }

-- ============================================================
-- メイン
-- ============================================================

def main : IO Unit := do
    IO.println "=== process_rotate180 4L Exhaustive Check ==="
    IO.println ""

    let layers3 := genLayers repQuarters3  -- 81 layers
    let layers2 := genLayers repQuarters2  -- 16 layers

    let mut allOk := true
    let mut totalTested := 0

    -- Phase 1: 1L 全数 (3-type)
    let r1 ← test1L layers3
    IO.println (toString r1)
    allOk := allOk && r1.failures == 0
    totalTested := totalTested + r1.tested

    -- Phase 2: 2L 全数 (3-type)
    let r2 ← test2L layers3
    IO.println (toString r2)
    allOk := allOk && r2.failures == 0
    totalTested := totalTested + r2.tested

    -- Phase 3: 3L 全数 (3-type)
    IO.println "  3L (3-type): running..."
    let r3 ← test3L layers3
    IO.println (toString r3)
    allOk := allOk && r3.failures == 0
    totalTested := totalTested + r3.tested

    -- Phase 4: 4L 全数 (2-type)
    let r4 ← test4L2Type layers2
    IO.println (toString r4)
    allOk := allOk && r4.failures == 0
    totalTested := totalTested + r4.tested

    -- Phase 5: 4L ピン集中（各レイヤ位置）
    for pos in [0, 1, 2, 3] do
        let r5 ← test4LPinLayer layers3 layers2 pos
        IO.println (toString r5)
        allOk := allOk && r5.failures == 0
        totalTested := totalTested + r5.tested

    -- Phase 6: 構造的カバレッジ
    let r6 ← testStructural
    IO.println (toString r6)
    allOk := allOk && r6.failures == 0
    totalTested := totalTested + r6.tested

    IO.println ""
    IO.println s!"Total shapes tested: {totalTested}"
    if allOk then
        IO.println "=== ALL PASSED ==="
    else
        IO.println "=== FAILURES DETECTED ==="
        IO.Process.exit 1
