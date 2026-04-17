-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT
import S2IL

open Gravity Quarter Layer Shape QuarterPos Direction

/-- pin NE 発生時の obs で ImmBelow（全 nonEmpty l≥1 の below が nonEmpty）が成り立つか -/
def checkImmBelowAtPinNE : IO Unit := do
  let allQ : List Quarter := [.empty, .pin, .crystal .red]
  let allDirs := [Direction.ne, Direction.nw, Direction.se, Direction.sw]
  let mut layers2d : List Layer := []
  for nw in allQ do
    for ne in allQ do
      layers2d := { ne := ne, se := .empty, sw := .empty, nw := nw } :: layers2d
  let mut totalPinNE := (0 : Nat)
  let mut immBelowOK := (0 : Nat)
  let mut immBelowFail := (0 : Nat)
  for l0 in layers2d do
   for l1 in layers2d do
    for l2 in layers2d do
     for l3 in layers2d do
      for l4 in layers2d do
       let sLayers := [l0, l1, l2, l3, l4]
       match Shape.ofLayers sLayers with
       | none => pure ()
       | some s =>
         let units := floatingUnits s
         let sorted := sortFallingUnits' units
         let allFP := sorted.flatMap FallingUnit.positions
         let obs0 := (s.clearPositions allFP).layers
         let mut obs := obs0
         for u in sorted do
           let d_drop := landingDistance u obs
           let isPin := match u with | .pin _ => true | _ => false
           if isPin then
             let pos := match u with | .pin p => p | _ => ⟨0, .ne⟩
             let landLayer := pos.layer - d_drop
             let landQ := getDir (obs.getD landLayer .empty) pos.dir
             if !landQ.isEmpty then
               totalPinNE := totalPinNE + 1
               -- check ImmBelow
               let immBelow := allDirs.all fun d =>
                 (List.range obs.length).all fun l =>
                   if l == 0 then true
                   else
                     let q := getDir (obs.getD l .empty) d
                     if !q.isEmpty then
                       let belowQ := getDir (obs.getD (l-1) .empty) d
                       !belowQ.isEmpty
                     else true
               if immBelow then immBelowOK := immBelowOK + 1
               else immBelowFail := immBelowFail + 1
           obs := placeFallingUnit s obs u d_drop
  IO.println s!"totalPinNE={totalPinNE}"
  IO.println s!"immBelowOK={immBelowOK}"
  IO.println s!"immBelowFail={immBelowFail}"

def main : IO Unit := checkImmBelowAtPinNE
