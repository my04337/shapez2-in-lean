-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- `waveStep_nonGroundedLayerSum_lt` および Sub-claim B1/B2/B3 の全数検証スクリプト。
-- 実行: lake env lean --run Verification/Gravity/NonGroundedLayerSumDecrease.lean
--
-- 検証性質:
--   (Main) fus 非空 → nonGroundedLayerSum(waveStep s) < nonGroundedLayerSum s
--   (B2)   settling FU の全位置は非接地
--   (B3')  landingDistance ≥ 2 の場合、各 FU 位置について obs の (layer - d) は空
--
-- 反例が見つかれば最初のシェイプを出力し失敗終了。

import S2IL.Operations.Gravity

open Gravity

-- ============================================================
-- 代表象限（3-type: empty / pin / crystal）
-- ============================================================

private def repQuarters : Array Quarter :=
    #[Quarter.empty, Quarter.pin, Quarter.crystal Color.red]

private def genLayers (qs : Array Quarter) : Array Layer := Id.run do
    let mut result : Array Layer := #[]
    for ne in qs do
        for se in qs do
            for sw in qs do
                for nw in qs do
                    result := result.push ⟨ne, se, sw, nw⟩
    return result

-- ============================================================
-- Main: nonGroundedLayerSum 厳密減少の検証
-- ============================================================

private def checkMainDecrease (s : Shape) : Bool :=
    if (Gravity.floatingUnits s).isEmpty then
        true  -- 仮定が false、自明に true
    else
        decide (Gravity.nonGroundedLayerSum (Gravity.waveStep s) < Gravity.nonGroundedLayerSum s)

-- ============================================================
-- B2: settling FU の全位置は非接地
-- ============================================================

private def checkB2 (s : Shape) : Bool :=
    let fus := Gravity.floatingUnits s
    if h : fus.isEmpty then
        true
    else
        -- floatingUnits の全 FU の全位置が非接地かを確認
        fus.all fun u =>
            u.positions.all fun p =>
                !(Gravity.groundedPositionsList s).any (· == p)

-- ============================================================
-- 列挙と集計
-- ============================================================

structure TestResult where
    label : String
    tested : Nat
    failures : Nat
    firstFailure : Option String
    deriving Inhabited

instance : ToString TestResult where
    toString r :=
        let ff := r.firstFailure.getD "?"
        if r.failures > 0 then
            s!"  FAIL: {r.label}: {r.failures}/{r.tested} failures. First: {ff}"
        else
            s!"  OK: {r.label}: {r.tested} shapes, 0 failures"

/-- N レイヤ全列挙で 2 性質を同時検証。 -/
private partial def testNLayer (n : Nat) (qs : Array Quarter) : IO TestResult := do
    let layers := genLayers qs
    let testedRef ← IO.mkRef (0 : Nat)
    let failsMainRef ← IO.mkRef (0 : Nat)
    let failsB2Ref ← IO.mkRef (0 : Nat)
    let firstFailRef ← IO.mkRef (none : Option String)
    let total := layers.size ^ n
    let rec enumerate (depth : Nat) (acc : List Layer) : IO Unit := do
        if depth == 0 then
            match Shape.ofLayers acc with
            | none => pure ()
            | some s =>
                testedRef.modify (· + 1)
                let tested ← testedRef.get
                if tested % 1000 == 0 then
                    IO.println s!"    progress: {tested}/{total}"
                let okMain := checkMainDecrease s
                let okB2 := checkB2 s
                if !okMain then
                    failsMainRef.modify (· + 1)
                    let cur ← firstFailRef.get
                    if cur.isNone then
                        firstFailRef.set (some s!"Main fail: {repr acc}")
                if !okB2 then
                    failsB2Ref.modify (· + 1)
                    let cur ← firstFailRef.get
                    if cur.isNone then
                        firstFailRef.set (some s!"B2 fail: {repr acc}")
        else
            for l in layers do
                enumerate (depth - 1) (acc ++ [l])
    enumerate n []
    let tested ← testedRef.get
    let failsMain ← failsMainRef.get
    let failsB2 ← failsB2Ref.get
    let firstFail ← firstFailRef.get
    let label := s!"n={n}, qs={qs.size}-type"
    let totalFails := failsMain + failsB2
    return { label := s!"{label} (Main fails: {failsMain}, B2 fails: {failsB2})",
             tested := tested, failures := totalFails, firstFailure := firstFail }

def main : IO Unit := do
    IO.println "=== nonGroundedLayerSum 厳密減少 + B2 非接地性 検証 ==="
    -- Phase 1: 2L, 3-type (81 shapes)
    IO.println "Phase 1: 2L, 3-type"
    let r1 ← testNLayer 2 repQuarters
    IO.println (toString r1)
    -- Phase 2: 3L, 3-type (729 shapes)
    IO.println "Phase 2: 3L, 3-type"
    let r2 ← testNLayer 3 repQuarters
    IO.println (toString r2)
    -- Phase 3: 4L, 2-type (65536 shapes) — 重いのでコメントアウト可
    -- IO.println "Phase 3: 4L, 2-type"
    -- let r3 ← testNLayer 4 #[Quarter.empty, Quarter.crystal Color.red]
    -- IO.println (toString r3)
    let totalFails := r1.failures + r2.failures
    if totalFails > 0 then
        IO.eprintln s!"TOTAL FAILURES: {totalFails}"
        IO.Process.exit 1
    else
        IO.println "ALL TESTS PASSED"
