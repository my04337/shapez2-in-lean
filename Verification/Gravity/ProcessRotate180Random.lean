-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- process_rotate180 の 5L+ ランダムサンプリング検証
-- 実行: lake env lean --run Verification/Gravity/ProcessRotate180Random.lean
--
-- 検証結果 (2026-04-05, seed: 49517580):
--   5L:  10,000 shapes, 0 failures
--   6L:   5,000 shapes, 0 failures
--   7L:   2,000 shapes, 0 failures
--   8L:   1,000 shapes, 0 failures
--   10L:    500 shapes, 0 failures
--   16L:    200 shapes, 0 failures
--   合計: 18,700 shapes, 0 failures

import S2IL.Operations.Gravity

open Gravity

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

-- ============================================================
-- ランダムシェイプ生成
-- ============================================================

-- 全Quarter種（重力挙動に影響する代表）
private def allQuarters : Array Quarter := #[
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
    let (idx, rng') := rng.nextNat allQuarters.size
    (allQuarters[idx]!, rng')

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
-- テスト関数
-- ============================================================

private def testShape (s : Shape) : Bool :=
    (Gravity.process s).map Shape.rotate180 == Gravity.process s.rotate180

-- ============================================================
-- メイン
-- ============================================================

def main : IO Unit := do
    IO.println "=== process_rotate180 Random Sampling (5L+) ==="
    IO.println ""

    -- シード: 現在時刻ベース
    let seed ← IO.monoMsNow
    let mut rng := Rng.mk (UInt64.ofNat seed)
    let mut totalTested := 0
    let mut totalFailures := 0
    let mut allOk := true

    -- 各レイヤ数ごとにサンプリング
    let configs : Array (Nat × Nat) := #[
        (5, 10000),   -- 5L: 10,000 samples
        (6, 5000),    -- 6L: 5,000 samples
        (7, 2000),    -- 7L: 2,000 samples
        (8, 1000),    -- 8L: 1,000 samples
        (10, 500),    -- 10L: 500 samples
        (16, 200)     -- 16L: 200 samples
    ]

    for (numLayers, numSamples) in configs do
        let mut tested := 0
        let mut failures := 0
        let mut firstFail : Option String := none
        for _ in List.range numSamples do
            let (ms, rng') := randomShape rng numLayers
            rng := rng'
            match ms with
            | none => pure ()
            | some s =>
                tested := tested + 1
                if !(testShape s) then
                    failures := failures + 1
                    if firstFail.isNone then firstFail := some s.toString
        -- 進捗表示
        if failures > 0 then
            IO.println s!"  FAIL: {numLayers}L ({numSamples} samples): {failures}/{tested} failures. First: {firstFail.getD "?"}"
            allOk := false
        else
            IO.println s!"  OK: {numLayers}L: {tested} shapes, 0 failures"
        totalTested := totalTested + tested
        totalFailures := totalFailures + failures

    IO.println ""
    IO.println s!"Total shapes tested: {totalTested}"
    IO.println s!"Seed: {seed}"
    if allOk then
        IO.println "=== ALL PASSED ==="
    else
        IO.println s!"=== FAILURES DETECTED ({totalFailures} total) ==="
        IO.Process.exit 1
