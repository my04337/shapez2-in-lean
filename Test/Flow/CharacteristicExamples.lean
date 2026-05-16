-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Flow

/-!
# Test.Flow.CharacteristicExamples

ゲーム内の特徴的な加工フローを Test 側で検証する。

ここに置く flow は、MAM や通常ライブラリの公開 API ではなく、口語資料から
現行 S2IL の Flow DSL へ読み替えた代表例である。throughput やベルト速度は
Layer C-1 の対象外なので、1 tick の Shape 値変換として扱う。
-/

open S2IL

namespace Test.Flow.CharacteristicExamples

private def shapeOrEmpty (code : String) : Shape :=
  match Shape.ofString? code with
  | some shape => shape
  | none => Shape.empty

/-! ## Example1: 入力シェイプの NE 側を取得する -/

private def example1Input : Shape := shapeOrEmpty "CrRgSbRu"
private def example1Expected : Shape := shapeOrEmpty "Cr------"

#guard Shape.toString example1Input == "CrRgSbRu"
#guard Shape.toString example1Expected == "Cr------"

/--
現行の E/W Half-Destroyer で NE だけを残す flow。

資料の「Reverse Rotator」は、現行実装ではいったん CW で NE を東側へ寄せ、
2 回目の Half-Destroyer の後に CCW で元の NE 位置へ戻す流れとして読む。
-/
private def example1ExtractNE : Flow Shape Shape :=
  Flow.comp (Flow.comp Flow.halfDestroy Flow.rotateCW)
    (Flow.comp Flow.halfDestroy Flow.rotateCCW)

#guard Shape.toString (Flow.eval example1ExtractNE example1Input) == "Cr------"

example : Flow.eval example1ExtractNE example1Input =
    Flow.eval Flow.Examples.extractNE example1Input := by
  rfl

/-! ## Example2: 4 象限図形から対角化された図形を取得する -/

private def example2Input : Shape := shapeOrEmpty "CuCuCuCu"
private def example2CutEast : Shape := shapeOrEmpty "CuCu----"
private def example2CutWest : Shape := shapeOrEmpty "----CuCu"
private def example2RotatedEast : Shape := shapeOrEmpty "--CuCu--"
private def example2RotatedWest : Shape := shapeOrEmpty "Cu----Cu"
private def example2SwapFirst : Shape := shapeOrEmpty "--Cu--Cu"
private def example2SwapSecond : Shape := shapeOrEmpty "Cu--Cu--"

#guard Shape.toString example2Input == "CuCuCuCu"
#guard Shape.toString example2SwapSecond == "Cu--Cu--"

/-- 現行 S2IL の Cutter 出力順は `(eastHalf, westHalf)`。 -/
private def example2CutEastWest : Flow Shape (Shape × Shape) :=
  Flow.cut

/-- 東側・西側の出力をそれぞれ CW 90 度回転する。 -/
private def example2RotateEastWest : Flow Shape (Shape × Shape) :=
  Flow.comp example2CutEastWest (Flow.pairMap Flow.rotateCW Flow.rotateCW)

/-- 回転後の `(east, west)` を Swapper へ投入し、第 1 / 第 2 出力を得る。 -/
private def example2SwapOutputs : Flow Shape (Shape × Shape) :=
  Flow.comp example2RotateEastWest Flow.swapShapes

/-- Swapper の第 2 出力を残す対角化 flow。 -/
private def example2Diagonal : Flow Shape Shape :=
  Flow.comp example2SwapOutputs (Flow.trashFirstShape : Flow (Shape × Shape) Shape)

/-- Swapper の第 1 出力を CW 回転して第 2 出力と同じ向きに揃える flow。 -/
private def example2DiagonalFromFirst : Flow Shape Shape :=
  Flow.comp example2SwapOutputs
    (Flow.comp (Flow.trashSecondShape : Flow (Shape × Shape) Shape) Flow.rotateCW)

#guard Shape.toString (Flow.eval example2CutEastWest example2Input).1 == Shape.toString example2CutEast
#guard Shape.toString (Flow.eval example2CutEastWest example2Input).2 == Shape.toString example2CutWest
#guard Shape.toString (Flow.eval example2RotateEastWest example2Input).1 ==
  Shape.toString example2RotatedEast
#guard Shape.toString (Flow.eval example2RotateEastWest example2Input).2 ==
  Shape.toString example2RotatedWest
#guard Shape.toString (Flow.eval example2SwapOutputs example2Input).1 ==
  Shape.toString example2SwapFirst
#guard Shape.toString (Flow.eval example2SwapOutputs example2Input).2 ==
  Shape.toString example2SwapSecond
#guard Shape.toString (Flow.eval example2Diagonal example2Input) == "Cu--Cu--"
#guard Shape.toString (Flow.eval example2DiagonalFromFirst example2Input) == "Cu--Cu--"

/-! ## Example3: 着色あり 4 レイヤシェイプの作成 -/

private def ruFull : Shape := shapeOrEmpty "RuRuRuRu"
private def suFull : Shape := shapeOrEmpty "SuSuSuSu"
private def rbFull : Shape := shapeOrEmpty "RbRbRbRb"
private def rbDiagonal : Shape := shapeOrEmpty "Rb--Rb--"
private def example3Expected : Shape :=
  shapeOrEmpty "Rb--Rb--:RuRuRuRu:Rb--Rb--:SuSuSuSu"

#guard Shape.toString ruFull == "RuRuRuRu"
#guard Shape.toString suFull == "SuSuSuSu"
#guard Shape.toString rbFull == "RbRbRbRb"
#guard Shape.toString rbDiagonal == "Rb--Rb--"
#guard Shape.toString example3Expected == "Rb--Rb--:RuRuRuRu:Rb--Rb--:SuSuSuSu"

/-- Paint-Ru-to-Rb: `RuRuRuRu` と blue 液剤から `RbRbRbRb` を作る。 -/
private def paintRuToRb : Flow (Shape × Color) Shape :=
  Flow.paintWith

/-- Diagonal-Split: 4 象限図形から `Rb--Rb--` 型の対角図形を得る。 -/
private def diagonalSplit : Flow Shape Shape :=
  example2Diagonal

/-- Diagonal-Split x2: C-1 では throughput ではなく product 出力として 2 本ぶんを表す。 -/
private def diagonalSplitX2 : Flow Shape (Shape × Shape) :=
  Flow.fanout diagonalSplit diagonalSplit

/-- Stack-4Layers の入力形へ並べ替える。 -/
private def prepareStack4Input : Flow (Shape × (Shape × Shape)) (((Shape × Shape) × Shape) × Shape) :=
  Flow.prim (fun input =>
    let diagonals := Flow.eval diagonalSplitX2 input.1
    (((diagonals.1, input.2.1), diagonals.2), input.2.2))

/-- 計算可能な構造的 Stack-4Layers。層順の smoke test 用。 -/
private def stack4LayersStructural : Flow (((Shape × Shape) × Shape) × Shape) Shape :=
  Flow.prim (fun input =>
    Shape.placeAbove
      (Shape.placeAbove
        (Shape.placeAbove input.1.1.1 input.1.1.2)
        input.1.2)
      input.2)

/-- Paint -> Diagonal-Split x2 -> structural Stack-4Layers の固定ライン。 -/
private def example3StructuralLine : Flow ((Shape × Color) × (Shape × Shape)) Shape :=
  Flow.comp (Flow.comp (Flow.first paintRuToRb) prepareStack4Input) stack4LayersStructural

#guard Shape.toString (Flow.eval paintRuToRb (ruFull, Color.blue)) == "RbRbRbRb"
#guard Shape.toString (Flow.eval diagonalSplit rbFull) == "Rb--Rb--"
#guard Shape.toString (Flow.eval diagonalSplitX2 rbFull).1 == "Rb--Rb--"
#guard Shape.toString (Flow.eval diagonalSplitX2 rbFull).2 == "Rb--Rb--"
#guard Shape.toString
    (Flow.eval stack4LayersStructural (((rbDiagonal, ruFull), rbDiagonal), suFull)) ==
  "Rb--Rb--:RuRuRuRu:Rb--Rb--:SuSuSuSu"
#guard Shape.toString
    (Flow.eval example3StructuralLine ((ruFull, Color.blue), (ruFull, suFull))) ==
  "Rb--Rb--:RuRuRuRu:Rb--Rb--:SuSuSuSu"

noncomputable section

/-- 実 Stacker を使う Stack-4Layers。出力値の計算検査は structural 版で担保する。 -/
private def stack4LayersWithStacker (config : GameConfig) :
    Flow (((Shape × Shape) × Shape) × Shape) Shape :=
  Flow.comp (Flow.first (Flow.first (Flow.stack config)))
    (Flow.comp (Flow.first (Flow.stack config)) (Flow.stack config))

/-- Paint -> Diagonal-Split x2 -> 実 Stacker x3 の固定ライン。 -/
private def example3StackerLine (config : GameConfig) :
    Flow ((Shape × Color) × (Shape × Shape)) Shape :=
  Flow.comp (Flow.comp (Flow.first paintRuToRb) prepareStack4Input)
    (stack4LayersWithStacker config)

example (config : GameConfig) (input : (((Shape × Shape) × Shape) × Shape)) :
    Flow.eval (stack4LayersWithStacker config) input =
      Shape.stack
        (Shape.stack
          (Shape.stack input.1.1.1 input.1.1.2 config)
          input.1.2 config)
        input.2 config := by
  rfl

example :
    Flow.eval (example3StackerLine GameConfig.vanilla4) ((ruFull, Color.blue), (ruFull, suFull)) =
      Flow.eval (stack4LayersWithStacker GameConfig.vanilla4)
        (Flow.eval prepareStack4Input
          (Flow.eval (Flow.first paintRuToRb) ((ruFull, Color.blue), (ruFull, suFull)))) := by
  rfl

end

end Test.Flow.CharacteristicExamples
