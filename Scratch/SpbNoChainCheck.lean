-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- spb_no_chain の反例検証
import S2IL.Behavior.Gravity

open Gravity in
private def mySpb (a b : FallingUnit) : Bool :=
    Direction.all.any fun dir =>
        match a.minLayerAtDir dir, b.minLayerAtDir dir with
        | some la, some lb => la < lb
        | _, _ => false

-- 3-pin same column test
#eval do
  match Shape.ofString? "--------:P-------:--------:P-------:--------:P-------" with
  | none => IO.println "parse failed"
  | some s =>
    let fus := Gravity.floatingUnits s
    IO.println s!"=== 3-pin same column ==="
    IO.println s!"fus count: {fus.length}"
    for u in fus do
      for v in fus do
        if u != v then
          IO.println s!"spb({repr u}, {repr v}) = {mySpb u v}"
    IO.println ""

-- Mixed direction test
#eval do
  match Shape.ofString? "--------:P-------:CrCr----:--P-----" with
  | none => IO.println "parse failed"
  | some s =>
    let fus := Gravity.floatingUnits s
    IO.println s!"=== Mixed direction ==="
    IO.println s!"fus count: {fus.length}"
    for u in fus do
      IO.println s!"  {repr u}"
    IO.println ""
    for u in fus do
      for v in fus do
        if u != v then
          IO.println s!"spb({repr u}, {repr v}) = {mySpb u v}"

    -- Check sortFU
    let sorted1 := Gravity.sortFallingUnits fus
    let sorted2 := Gravity.sortFallingUnits fus.reverse
    IO.println s!"\nsortFU(fus): {repr sorted1}"
    IO.println s!"sortFU(fus.rev): {repr sorted2}"
    IO.println s!"sortFU equal: {sorted1 == sorted2}"

    -- Check process_rotate180
    let proc := Gravity.process s
    let proc_r := Gravity.process s.rotate180
    let r_proc := proc.map Shape.rotate180
    IO.println s!"\nprocess_rotate180: {r_proc == proc_r}"

-- Multiple shapes with chains — check process_rotate180
private def checkShape (code : String) : IO Unit := do
  match Shape.ofString? code with
  | none => IO.println s!"{code}: parse failed"
  | some s =>
    let proc := Gravity.process s
    let proc_r := Gravity.process s.rotate180
    let r_proc := proc.map Shape.rotate180
    IO.println s!"{code}\n  process_rotate180: {r_proc == proc_r}"

#eval checkShape "--------:P-------:--------:P-------:--------:P-------"
#eval checkShape "--------:P-------:CrCr----:--P-----"
#eval checkShape "--------:P-------:P-------:P-------"
