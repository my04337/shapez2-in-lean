-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Flow

/-!
# Test.Flow.CrazyFinal

vanilla5 の難解な 5 レイヤ目標図形を、Test 側の独立サンプルとして表現する。

参考資料では `X` が任意のスペーサー図形として使われているため、このファイルでは
スター `S` をスペーサーとして読む。スペーサーは結晶生成時に空白を保護するための
作業用素材であり、最終出力には残さない。
-/

open S2IL

namespace Test.Flow.CrazyFinal

/-- このサンプルで仮定するプリミティブ入力。 -/
private structure PrimitiveInputs where
  cuFull : Shape
  ruFull : Shape
  suFull : Shape
  wuFull : Shape
  red : Color
  green : Color
  blue : Color

private def shapeOrEmpty (code : String) : Shape :=
  match Shape.ofString? code with
  | some shape => shape
  | none => Shape.empty

private def primitiveInputs : PrimitiveInputs :=
  { cuFull := shapeOrEmpty "CuCuCuCu"
    ruFull := shapeOrEmpty "RuRuRuRu"
    suFull := shapeOrEmpty "SuSuSuSu"
    wuFull := shapeOrEmpty "WuWuWuWu"
    red := Color.red
    green := Color.green
    blue := Color.blue }

private def targetShape : Shape :=
  shapeOrEmpty "RmCcWcCm:--cm--cc:RcccCmcm:cmcccccm:cw--cw--"

#guard Shape.toString primitiveInputs.cuFull == "CuCuCuCu"
#guard Shape.toString primitiveInputs.ruFull == "RuRuRuRu"
#guard Shape.toString primitiveInputs.suFull == "SuSuSuSu"
#guard Shape.toString primitiveInputs.wuFull == "WuWuWuWu"
#guard Shape.toString targetShape == "RmCcWcCm:--cm--cc:RcccCmcm:cmcccccm:cw--cw--"

private def cyanOf (input : PrimitiveInputs) : Color :=
  S2IL.Operations.mix input.green input.blue

private def magentaOf (input : PrimitiveInputs) : Color :=
  S2IL.Operations.mix input.red input.blue

private def whiteOf (input : PrimitiveInputs) : Color :=
  S2IL.Operations.mix input.red (cyanOf input)

#guard cyanOf primitiveInputs == Color.cyan
#guard magentaOf primitiveInputs == Color.magenta
#guard whiteOf primitiveInputs == Color.white

/-- 90 度回転して E/W 合成し、戻すことで北半分と南半分を合成する。 -/
private def combineNorthSouth : Flow (Shape × Shape) Shape :=
  Flow.comp (Flow.pairMap Flow.rotateCW Flow.rotateCW)
    (Flow.comp Flow.combineHalves Flow.rotateCCW)

/-- 4 つの単一象限 Shape を NE / SE / SW / NW の順に 1 レイヤへ合成する。 -/
private def assembleQuadrants : Flow (((Shape × Shape) × Shape) × Shape) Shape :=
  Flow.prim (fun input =>
    let ne := input.1.1.1
    let se := input.1.1.2
    let sw := input.1.2
    let nw := input.2
    let east := Flow.eval combineNorthSouth (ne, se)
    let west := Flow.eval combineNorthSouth (nw, sw)
    Flow.eval Flow.combineHalves (east, west))

private def blankOneLayer : Shape := [Layer.empty]

private def blankQuadrant : Flow PrimitiveInputs Shape :=
  Flow.constant blankOneLayer

private def paintedOnly
    (source : PrimitiveInputs → Shape) (color : PrimitiveInputs → Color)
    (extract : Flow Shape Shape) : Flow PrimitiveInputs Shape :=
  Flow.comp (Flow.prim (fun input => (source input, color input)))
    (Flow.comp Flow.paintWith extract)

private def spacerThenCrystalOnly
    (color : PrimitiveInputs → Color) (spacer : Flow Shape Shape)
    (extract : Flow Shape Shape) : Flow PrimitiveInputs Shape :=
  Flow.comp (Flow.prim (fun input => (Flow.eval spacer input.suFull, color input)))
    (Flow.comp Flow.crystallizeWith extract)

private def crystalNE (color : PrimitiveInputs → Color) : Flow PrimitiveInputs Shape :=
  spacerThenCrystalOnly color Flow.Examples.extractSE Flow.Examples.extractNE

private def crystalSE (color : PrimitiveInputs → Color) : Flow PrimitiveInputs Shape :=
  spacerThenCrystalOnly color Flow.Examples.extractNE Flow.Examples.extractSE

private def crystalSW (color : PrimitiveInputs → Color) : Flow PrimitiveInputs Shape :=
  spacerThenCrystalOnly color Flow.Examples.extractNE Flow.Examples.extractSW

private def crystalNW (color : PrimitiveInputs → Color) : Flow PrimitiveInputs Shape :=
  spacerThenCrystalOnly color Flow.Examples.extractNE Flow.Examples.extractNW

private def layerFromQuadrants
    (ne se sw nw : Flow PrimitiveInputs Shape) : Flow PrimitiveInputs Shape :=
  Flow.comp (Flow.fanout (Flow.fanout (Flow.fanout ne se) sw) nw) assembleQuadrants

private def layer1 : Flow PrimitiveInputs Shape :=
  layerFromQuadrants
    (paintedOnly PrimitiveInputs.ruFull magentaOf Flow.Examples.extractNE)
    (paintedOnly PrimitiveInputs.cuFull cyanOf Flow.Examples.extractSE)
    (paintedOnly PrimitiveInputs.wuFull cyanOf Flow.Examples.extractSW)
    (paintedOnly PrimitiveInputs.cuFull magentaOf Flow.Examples.extractNW)

private def layer2 : Flow PrimitiveInputs Shape :=
  layerFromQuadrants
    blankQuadrant
    (crystalSE magentaOf)
    blankQuadrant
    (crystalNW cyanOf)

private def layer3 : Flow PrimitiveInputs Shape :=
  layerFromQuadrants
    (paintedOnly PrimitiveInputs.ruFull cyanOf Flow.Examples.extractNE)
    (crystalSE cyanOf)
    (paintedOnly PrimitiveInputs.cuFull magentaOf Flow.Examples.extractSW)
    (crystalNW magentaOf)

private def layer4 : Flow PrimitiveInputs Shape :=
  layerFromQuadrants
    (crystalNE magentaOf)
    (crystalSE cyanOf)
    (crystalSW cyanOf)
    (crystalNW magentaOf)

private def layer5 : Flow PrimitiveInputs Shape :=
  layerFromQuadrants
    (crystalNE whiteOf)
    blankQuadrant
    (crystalSW whiteOf)
    blankQuadrant

private def targetLayers : Flow PrimitiveInputs ((((Shape × Shape) × Shape) × Shape) × Shape) :=
  Flow.fanout (Flow.fanout (Flow.fanout (Flow.fanout layer1 layer2) layer3) layer4) layer5

/-- 計算可能な structural stacking。vanilla5 の 5 層上限に収まる形を検査する。 -/
private def stack5Structural : Flow ((((Shape × Shape) × Shape) × Shape) × Shape) Shape :=
  Flow.prim (fun input =>
    Shape.placeAbove
      (Shape.placeAbove
        (Shape.placeAbove
          (Shape.placeAbove input.1.1.1.1 input.1.1.1.2)
          input.1.1.2)
        input.1.2)
      input.2)

/-- 原色・プリミティブ素材から目標図形を作る Test-only の大規模 composite flow。 -/
private def crazyFinalStructuralLine : Flow PrimitiveInputs Shape :=
  Flow.comp targetLayers stack5Structural

#guard Shape.toString (Flow.eval layer1 primitiveInputs) == "RmCcWcCm"
#guard Shape.toString (Flow.eval layer2 primitiveInputs) == "--cm--cc"
#guard Shape.toString (Flow.eval layer3 primitiveInputs) == "RcccCmcm"
#guard Shape.toString (Flow.eval layer4 primitiveInputs) == "cmcccccm"
#guard Shape.toString (Flow.eval layer5 primitiveInputs) == "cw--cw--"
#guard Shape.toString (Flow.eval crazyFinalStructuralLine primitiveInputs) ==
  "RmCcWcCm:--cm--cc:RcccCmcm:cmcccccm:cw--cw--"

example :
    Shape.toString (Flow.eval crazyFinalStructuralLine primitiveInputs) =
      Shape.toString targetShape := by
  rfl

noncomputable section

/-- 実 Stacker を 4 段使う vanilla5 版。exact output は structural 版で smoke test する。 -/
private def stack5WithStacker (config : GameConfig) :
    Flow ((((Shape × Shape) × Shape) × Shape) × Shape) Shape :=
  Flow.prim (fun input =>
    Shape.stack
      (Shape.stack
        (Shape.stack
          (Shape.stack input.1.1.1.1 input.1.1.1.2 config)
          input.1.1.2 config)
        input.1.2 config)
      input.2 config)

/-- vanilla5 の実 Stacker を使う同型ライン。 -/
private def crazyFinalStackerLine : Flow PrimitiveInputs Shape :=
  Flow.comp targetLayers (stack5WithStacker GameConfig.vanilla5)

example :
    Flow.eval crazyFinalStackerLine primitiveInputs =
      Flow.eval (stack5WithStacker GameConfig.vanilla5)
        (Flow.eval targetLayers primitiveInputs) := by
  rfl

end

end Test.Flow.CrazyFinal
