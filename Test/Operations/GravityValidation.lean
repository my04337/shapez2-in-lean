import S2IL
import Plausible

open S2IL
open Plausible

namespace Test.Operations.GravityValidation

private def vanillaSamples : Nat := 500
private def stressSamples : Nat := 500

private def shapeEq (a b : Shape) : Bool :=
  a.toString == b.toString

private structure VanillaShape where
  shape : Shape

private instance : Repr VanillaShape where
  reprPrec vs _ := repr vs.shape.toString

private instance : Shrinkable VanillaShape where
  shrink _ := []

private instance : Arbitrary VanillaShape where
  arbitrary := do
    let shape <- Arbitrary.arbitrary (α := Shape)
    return { shape }

private instance : SampleableExt VanillaShape where
  proxy := VanillaShape
  sample := inferInstance
  shrink := inferInstance
  interp := id

private structure StressShape where
  shape : Shape

private instance : Repr StressShape where
  reprPrec ss _ := repr ss.shape.toString

private def stressQuarterGen : Gen Quarter := do
  Gen.oneOf #[
    pure .empty,
    pure .pin,
    pure (.crystal .red),
    pure (.crystal .green),
    pure (.crystal .blue),
    pure (.colored .circle .red),
    pure (.colored .star .blue),
    pure (.colored .windmill .yellow),
    pure (.colored .rectangle .green)]

private def stressLayerGen : Gen Layer := do
  let q0 <- stressQuarterGen
  let q1 <- stressQuarterGen
  let q2 <- stressQuarterGen
  let q3 <- stressQuarterGen
  return Layer.mk q0 q1 q2 q3

private def stressShapeGen : Gen StressShape := do
  let nLayers <- Gen.oneOf #[pure 0, pure 1, pure 2, pure 3, pure 4, pure 5, pure 6, pure 7, pure 8]
  let mut layers : List Layer := []
  for _ in List.range nLayers do
    let layer <- stressLayerGen
    layers := layers ++ [layer]
  return { shape := layers }

private instance : Shrinkable StressShape where
  shrink _ := []

private instance : Arbitrary StressShape where
  arbitrary := stressShapeGen

private instance : SampleableExt StressShape where
  proxy := StressShape
  sample := inferInstance
  shrink := inferInstance
  interp := id

private def propDefs (s : Shape) : Bool :=
  (s.length <= GameConfig.stress8.maxLayers) &&
  (floatingPositions s).all (fun p =>
    ((QuarterPos.getQuarter s p.down).isEmpty || (floatingPositions s).contains p.down) &&
    (floatingPositions s).all (fun q =>
      if p.down == q.down then p == q else true))

private def propGroundedPreservation (s : Shape) : Bool :=
  (Gravity.Internal.groundedPositions s).all (fun p =>
    (QuarterPos.getQuarter (Shape.waveStep s) p == QuarterPos.getQuarter s p) &&
    (Gravity.Internal.groundedPositions (Shape.waveStep s)).contains p)

private def propOrigin (s : Shape) : Bool :=
  let step := Shape.waveStep s
  let oldFloating := floatingPositions s
  let nonemptyOrigin := (QuarterPos.allValid step).all (fun r =>
    if (QuarterPos.getQuarter step r).isEmpty then
      true
    else
      let static := (!oldFloating.contains r) && (!(QuarterPos.getQuarter s r).isEmpty)
      let shifted := oldFloating.any (fun p =>
        (p.down == r) && (QuarterPos.getQuarter step r == QuarterPos.getQuarter s p))
      static || shifted)
  let floatingOrigin := (floatingPositions step).all (fun r =>
    oldFloating.any (fun p => p.down == r))
  nonemptyOrigin && floatingOrigin

private def propTermination (s : Shape) : Bool :=
  let stepHeight := floatingHeight (Shape.waveStep s)
  let heightDecreases := (stepHeight == 0) || decide (stepHeight < floatingHeight s)
  let fixedFuelSettled := (floatingPositions (Shape.waveGravityCore s.length s)).isEmpty
  let fastFuelSettled := (floatingPositions (Shape.waveGravityCoreFast s.length s)).isEmpty
  heightDecreases && fixedFuelSettled && fastFuelSettled

private def propSettledFixedPoints (s : Shape) : Bool :=
  let noFloatingFixed :=
    if (floatingPositions s).isEmpty then
      shapeEq (Shape.waveStep s) s &&
      shapeEq (Shape.waveGravityCore (s.length + 2) s) s
    else
      true
  let gravitySettled := (floatingPositions (Shape.gravity s)).isEmpty
  let gravityIdempotent := shapeEq (Shape.gravity (Shape.gravity s)) (Shape.gravity s)
  let fastEqCore := shapeEq (Shape.waveGravityCoreFast (s.length + 2) s)
    (Shape.waveGravityCore (s.length + 2) s)
  noFloatingFixed && gravitySettled && gravityIdempotent && fastEqCore

private def propEquivariance (s : Shape) : Bool :=
  let floatingRotate := (QuarterPos.allValid s).all (fun p =>
    ((floatingPositions s.rotateCW).contains p.rotateCW) == ((floatingPositions s).contains p))
  let waveStepRotate := shapeEq (Shape.waveStep s).rotateCW (Shape.waveStep s.rotateCW)
  let coreRotate := shapeEq (Shape.waveGravityCore (s.length + 2) s).rotateCW
    (Shape.waveGravityCore (s.length + 2) s.rotateCW)
  let gravityCW := shapeEq (Shape.gravity s).rotateCW (Shape.gravity s.rotateCW)
  let gravity180 := shapeEq (Shape.gravity s).rotate180 (Shape.gravity s.rotate180)
  let gravityCCW := shapeEq (Shape.gravity s).rotateCCW (Shape.gravity s.rotateCCW)
  floatingRotate && waveStepRotate && coreRotate && gravityCW && gravity180 && gravityCCW

private def propPublicGravityTheorems (s : Shape) : Bool :=
  [propDefs s,
   propGroundedPreservation s,
   propOrigin s,
   propTermination s,
   propSettledFixedPoints s,
   propEquivariance s].all id

#eval! Plausible.Testable.check
  (forall vs : VanillaShape, propPublicGravityTheorems vs.shape = true)
  { numInst := vanillaSamples, maxSize := 5, randomSeed := some 2026050533, quiet := true }

#eval! Plausible.Testable.check
  (forall ss : StressShape, propPublicGravityTheorems ss.shape = true)
  { numInst := stressSamples, maxSize := 8, randomSeed := some 2026050534, quiet := true }

end Test.Operations.GravityValidation
