-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT
import S2IL

open Gravity Quarter Layer Shape QuarterPos Direction

/-- pin 配置で groundedPositions が単調増加（∀p∈gp(obs), p∈gp(obs')）かチェック -/
def checkGPMono : IO Unit := do
  let allQ : List Quarter := [.empty, .pin, .crystal .red]
  let mut layers2d : List Layer := []
  for nw in allQ do
    for ne in allQ do
      layers2d := { ne := ne, se := .empty, sw := .empty, nw := nw } :: layers2d
  let mut totalPinPlace := (0 : Nat)
  let mut monoOK := (0 : Nat)
  let mut monoFail := (0 : Nat)
  let mut totalClusterPlace := (0 : Nat)
  let mut clusterMonoOK := (0 : Nat)
  let mut clusterMonoFail := (0 : Nat)
  -- 5L 2dir
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
           let obs' := placeFallingUnit s obs u d_drop
           -- check gp mono
           match Shape.ofLayers obs, Shape.ofLayers obs' with
           | some sObs, some sObs' =>
             let gpObs := groundedPositionsList sObs
             let gpObs' := groundedPositionsList sObs'
             let allKept := gpObs.all fun p => gpObs'.any (· == p)
             let isPin := match u with
               | .pin _ => true
               | .cluster _ => false
             if isPin then
               totalPinPlace := totalPinPlace + 1
               if allKept then monoOK := monoOK + 1
               else monoFail := monoFail + 1
             else
               totalClusterPlace := totalClusterPlace + 1
               if allKept then clusterMonoOK := clusterMonoOK + 1
               else clusterMonoFail := clusterMonoFail + 1
           | _, _ => pure ()
           obs := obs'
  IO.println s!"Pin: total={totalPinPlace}, monoOK={monoOK}, monoFail={monoFail}"
  IO.println s!"Cluster: total={totalClusterPlace}, monoOK={clusterMonoOK}, monoFail={clusterMonoFail}"

def main : IO Unit := checkGPMono
