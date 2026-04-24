-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT
import S2IL

open Gravity Quarter Layer Shape QuarterPos Direction

/-- ANEG + ImmBelow の obs で crystal→pin gp mono を検証 -/
def checkGPMonoWithImmBelow : IO Unit := do
  let allQ : List Quarter := [.empty, .pin, .crystal .red]
  let allDirs := [Direction.ne, Direction.nw, Direction.se, Direction.sw]
  let mut total := (0 : Nat)
  let mut gpOK := (0 : Nat)
  let mut gpFail := (0 : Nat)
  -- 3L 2dir
  for l0ne in allQ do
   for l0nw in allQ do
    for l1ne in allQ do
     for l1nw in allQ do
      for l2ne in allQ do
       for l2nw in allQ do
        let layers := [
          { ne := l0ne, se := .empty, sw := .empty, nw := l0nw : Layer },
          { ne := l1ne, se := .empty, sw := .empty, nw := l1nw : Layer },
          { ne := l2ne, se := .empty, sw := .empty, nw := l2nw : Layer }
        ]
        match Shape.ofLayers layers with
        | none => pure ()
        | some sObs =>
          let gp := groundedPositionsList sObs
          let isANEG := allDirs.all fun d =>
            (List.range layers.length).all fun l =>
              let q := getDir (layers.getD l .empty) d
              if !q.isEmpty then gp.any (· == ⟨l, d⟩)
              else true
          -- ImmBelow check
          let isImmBelow := allDirs.all fun d =>
            (List.range layers.length).all fun l =>
              if l == 0 then true
              else
                let q := getDir (layers.getD l .empty) d
                if !q.isEmpty then
                  let belowQ := getDir (layers.getD (l-1) .empty) d
                  !belowQ.isEmpty
                else true
          if isANEG && isImmBelow then
            for pd in allDirs do
              for pl in List.range layers.length do
                let curQ := getDir (layers.getD pl .empty) pd
                let isCrystal := match curQ with | .crystal _ | .colored _ _ => true | _ => false
                if isCrystal then
                  total := total + 1
                  let newLayers := (layers.zip (List.range layers.length)).map fun ⟨layer, i⟩ =>
                    if i == pl then
                      match pd with
                      | .ne => { layer with ne := .pin }
                      | .nw => { layer with nw := .pin }
                      | .se => { layer with se := .pin }
                      | .sw => { layer with sw := .pin }
                    else layer
                  match Shape.ofLayers newLayers with
                  | none => pure ()
                  | some sObs' =>
                    let gp' := groundedPositionsList sObs'
                    let allKept := gp.all fun p => gp'.any (· == p)
                    if allKept then gpOK := gpOK + 1
                    else gpFail := gpFail + 1
  IO.println s!"total={total}, gpOK={gpOK}, gpFail={gpFail}"

def main : IO Unit := checkGPMonoWithImmBelow
