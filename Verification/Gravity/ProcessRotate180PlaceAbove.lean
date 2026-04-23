-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- placeAbove 構造シェイプの process_rotate180 検証
-- 実行: lake env lean --run Verification/Gravity/ProcessRotate180PlaceAbove.lean

import S2IL.Operations.Gravity
import S2IL.Operations.Stacker.Stacker

open Gravity Stacker

-- ============================================================
-- 代表象限
-- ============================================================

-- 4 代表: empty / pin / crystal / colored（全 canFormBond 分岐をカバー）
private def repQuarters4 : Array Quarter := #[
    Quarter.empty,
    Quarter.pin,
    Quarter.crystal Color.red,
    Quarter.colored RegularPartCode.rectangle Color.red
]

-- 3 代表: empty / pin / colored（shatter 後のトップ部分をカバー）
private def repQuarters3 : Array Quarter := #[
    Quarter.empty,
    Quarter.pin,
    Quarter.colored RegularPartCode.rectangle Color.red
]

-- 2 代表: empty / colored（高速スイープ用）
private def repQuarters2 : Array Quarter := #[
    Quarter.empty,
    Quarter.colored RegularPartCode.rectangle Color.red
]

-- ============================================================
-- レイヤ生成
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

/-- placeAbove + shatterTopCrystals で process_rotate180 が成立するかテスト -/
private def testPlaceAbove (bottom top : Shape) : Bool :=
    let combined := placeAbove bottom top
    let afterShatter := shatterTopCrystals combined bottom.layerCount
    (process afterShatter).map Shape.rotate180 == process afterShatter.rotate180

-- ============================================================
-- 擬似乱数生成器 (SplitMix64)
-- ============================================================

structure Rng where
    state : UInt64

private def Rng.next (rng : Rng) : UInt64 × Rng :=
    let s := rng.state + 0x9E3779B97F4A7C15
    let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
    let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
    let z := z ^^^ (z >>> 31)
    (z, ⟨s⟩)

private def Rng.nextNat (rng : Rng) (bound : Nat) : Nat × Rng :=
    let (v, rng') := rng.next
    (v.toNat % bound, rng')

private def allQuartersRandom : Array Quarter := #[
    Quarter.empty,
    Quarter.pin,
    Quarter.crystal Color.red,
    Quarter.crystal Color.green,
    Quarter.colored RegularPartCode.circle Color.red,
    Quarter.colored RegularPartCode.rectangle Color.blue,
    Quarter.colored RegularPartCode.star Color.yellow,
    Quarter.colored RegularPartCode.windmill Color.cyan
]

private instance : Inhabited Quarter := ⟨Quarter.empty⟩

private def randomQuarter (rng : Rng) : Quarter × Rng :=
    let (idx, rng') := rng.nextNat allQuartersRandom.size
    (allQuartersRandom[idx]!, rng')

private def randomLayer (rng : Rng) : Layer × Rng :=
    let (ne, rng) := randomQuarter rng
    let (se, rng) := randomQuarter rng
    let (sw, rng) := randomQuarter rng
    let (nw, rng) := randomQuarter rng
    (⟨ne, se, sw, nw⟩, rng)

private def randomShape (rng : Rng) (numLayers : Nat) : Option Shape × Rng :=
    let rec go (n : Nat) (acc : List Layer) (rng : Rng) : List Layer × Rng :=
        match n with
        | 0 => (acc.reverse, rng)
        | n + 1 =>
            let (l, rng') := randomLayer rng
            go n (l :: acc) rng'
    let (layers, rng') := go numLayers [] rng
    (Shape.ofLayers layers, rng')

-- ============================================================
-- Phase 1: 1L+1L=2L 全数 (4-type, 256*256 = 65536)
-- ============================================================

private def test1L1L (layers : Array Layer) : IO (Nat × Nat × Option String) := do
    let mut tested := 0
    let mut failures := 0
    let mut firstFail : Option String := none
    for lb in layers do
        for lt in layers do
            match Shape.ofLayers [lb], Shape.ofLayers [lt] with
            | some b, some t =>
                tested := tested + 1
                if !(testPlaceAbove b t) then
                    failures := failures + 1
                    if firstFail.isNone then
                        firstFail := some s!"bottom={b}, top={t}"
            | _, _ => pure ()
    return (tested, failures, firstFail)

-- ============================================================
-- Phase 2: 2L+2L=4L 全数 (3-type, 81*81 = 6561*6561 ≈ 43M → 要削減)
-- → 2-type: 16*16=256 底×256 上 = 65536
-- ============================================================

private def test2L2L (layers : Array Layer) : IO (Nat × Nat × Option String) := do
    let mut tested := 0
    let mut failures := 0
    let mut firstFail : Option String := none
    for lb1 in layers do
        for lb2 in layers do
            for lt1 in layers do
                for lt2 in layers do
                    match Shape.ofLayers [lb1, lb2], Shape.ofLayers [lt1, lt2] with
                    | some b, some t =>
                        tested := tested + 1
                        if !(testPlaceAbove b t) then
                            failures := failures + 1
                            if firstFail.isNone then
                                firstFail := some s!"bottom={b}, top={t}"
                    | _, _ => pure ()
        if tested % 10000 < layers.size * layers.size * layers.size then
            IO.eprint s!"\r  2L+2L: {tested}..."
    IO.eprintln ""
    return (tested, failures, firstFail)

-- ============================================================
-- Phase 3: ランダムサンプリング (3L+3L=6L ～ 5L+5L=10L)
-- ============================================================

private def testRandom (configs : Array (Nat × Nat × Nat)) (rng : Rng) :
        IO (Nat × Nat × Option String × Rng) := do
    let mut totalTested := 0
    let mut totalFailures := 0
    let mut firstFail : Option String := none
    let mut rng := rng
    for (bLayers, tLayers, samples) in configs do
        let mut tested := 0
        let mut failures := 0
        for _ in List.range samples do
            let (b, rng') := randomShape rng bLayers
            rng := rng'
            let (t, rng') := randomShape rng tLayers
            rng := rng'
            match b, t with
            | some bs, some ts =>
                tested := tested + 1
                if !(testPlaceAbove bs ts) then
                    failures := failures + 1
                    if firstFail.isNone then
                        firstFail := some s!"{bLayers}+{tLayers}L: bottom={bs}, top={ts}"
            | _, _ => pure ()
        totalTested := totalTested + tested
        totalFailures := totalFailures + failures
        IO.println s!"  {bLayers}+{tLayers}={bLayers+tLayers}L: {tested} shapes, {failures} failures"
    return (totalTested, totalFailures, firstFail, rng)

-- ============================================================
-- メイン
-- ============================================================

def main : IO Unit := do
    IO.println "=== process_rotate180 PlaceAbove Verification ==="
    IO.println ""
    let mut totalTested := 0
    let mut totalFailures := 0
    let mut allOk := true

    -- Phase 1: 1L+1L 全数 (4-type)
    IO.println "Phase 1: 1L+1L exhaustive (4-type quarters)"
    let layers4 := genLayers repQuarters4
    let (t1, f1, ff1) ← test1L1L layers4
    totalTested := totalTested + t1
    totalFailures := totalFailures + f1
    if f1 > 0 then allOk := false
    IO.println s!"  {t1} shapes, {f1} failures{if let some s := ff1 then s!" First: {s}" else ""}"

    -- Phase 2: 2L+2L 全数 (2-type)
    IO.println "Phase 2: 2L+2L exhaustive (2-type quarters)"
    let layers2 := genLayers repQuarters2
    let (t2, f2, ff2) ← test2L2L layers2
    totalTested := totalTested + t2
    totalFailures := totalFailures + f2
    if f2 > 0 then allOk := false
    IO.println s!"  {t2} shapes, {f2} failures{if let some s := ff2 then s!" First: {s}" else ""}"

    -- Phase 3: ランダムサンプリング
    IO.println "Phase 3: Random sampling (larger shapes)"
    let seed ← IO.monoMsNow
    IO.println s!"  Seed: {seed}"
    let rng := Rng.mk (UInt64.ofNat seed)
    -- (bottomLayers, topLayers, samples)
    let configs : Array (Nat × Nat × Nat) := #[
        (2, 3, 5000),   -- 2+3=5L
        (3, 3, 10000),  -- 3+3=6L ← key: 6L counterexample exists in general
        (3, 4, 5000),   -- 3+4=7L
        (4, 4, 5000),   -- 4+4=8L
        (5, 5, 3000),   -- 5+5=10L ← max config
        (4, 3, 3000),   -- 4+3=7L
        (5, 3, 2000),   -- 5+3=8L
        (5, 4, 2000)    -- 5+4=9L
    ]
    let (t3, f3, ff3, _) ← testRandom configs rng
    totalTested := totalTested + t3
    totalFailures := totalFailures + f3
    if f3 > 0 then allOk := false

    -- Summary
    IO.println ""
    IO.println s!"=== Total: {totalTested} shapes, {totalFailures} failures ==="
    if allOk then
        IO.println "ALL PASSED"
    else
        IO.println s!"FAILURES DETECTED! First: {ff1.getD (ff2.getD (ff3.getD "?"))}"
        IO.Process.exit 1
