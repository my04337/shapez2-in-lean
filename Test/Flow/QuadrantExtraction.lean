import S2IL.Flow

/-!
# Test.Flow.QuadrantExtraction

Flow 象限抽出サンプル theorem の代表値テスト。

入力 `CrRgSbWy` は NE=Cr, SE=Rg, SW=Sb, NW=Wy を表す。
`halfDestroy -> rotate* -> halfDestroy` の方角仕様をここで固定する。
-/

open S2IL

namespace Test.Flow.QuadrantExtraction

private def probeLayer : Layer :=
  Layer.mk
    (.colored .circle .red)
    (.colored .rectangle .green)
    (.colored .star .blue)
    (.colored .windmill .yellow)

private def probe : Shape := Shape.single probeLayer

#guard Shape.toString probe == "CrRgSbWy"
#guard Shape.toString (Shape.halfDestroy probe) == "CrRg----"

-- `halfDestroy -> rotateCW -> halfDestroy`: 元 NE を SE に残す。
#guard Shape.toString
    (Shape.halfDestroy (Shape.rotateCW (Shape.halfDestroy probe))) == "--Cr----"

-- `halfDestroy -> rotateCCW -> halfDestroy`: 元 SE を NE に残す。
#guard Shape.toString
    (Shape.halfDestroy (Shape.rotateCCW (Shape.halfDestroy probe))) == "Rg------"

-- `halfDestroy -> rotate180 -> halfDestroy`: 東半分が西側へ移るため空になる。
#guard Shape.toString
    (Shape.halfDestroy (Shape.rotate180 (Shape.halfDestroy probe))) == "--------"

example (s : Shape) (n : Nat) (d : Direction) :
    QuarterPos.getQuarter (Shape.halfDestroy s) (n, d) =
      if d.val < 2 then QuarterPos.getQuarter s (n, d) else Quarter.empty :=
  Flow.QuadrantExtraction.halfDestroy_getQuarter s n d

example (s : Shape) (n : Nat) (d : Direction) :
    QuarterPos.getQuarter (Shape.halfDestroy (Shape.rotateCW (Shape.halfDestroy s))) (n, d) =
      if d = 1 then QuarterPos.getQuarter s (n, 0) else Quarter.empty :=
  Flow.QuadrantExtraction.extractAfterRotateCW_getQuarter s n d

example (s : Shape) (n : Nat) (d : Direction) :
    QuarterPos.getQuarter (Shape.halfDestroy (Shape.rotateCCW (Shape.halfDestroy s))) (n, d) =
      if d = 0 then QuarterPos.getQuarter s (n, 1) else Quarter.empty :=
  Flow.QuadrantExtraction.extractAfterRotateCCW_getQuarter s n d

example (s : Shape) (n : Nat) (d : Direction) :
    QuarterPos.getQuarter (Shape.halfDestroy (Shape.rotate180 (Shape.halfDestroy s))) (n, d) =
      Quarter.empty :=
  Flow.QuadrantExtraction.extractAfterRotate180_getQuarter s n d

example (s : Shape) :
    Flow.QuadrantExtraction.extractNEToNE s = Flow.QuadrantExtraction.keepOnlyAt s 0 0 ∧
    Flow.QuadrantExtraction.extractSEToNE s = Flow.QuadrantExtraction.keepOnlyAt s 1 0 ∧
    Flow.QuadrantExtraction.extractSWToNE s = Flow.QuadrantExtraction.keepOnlyAt s 2 0 ∧
    Flow.QuadrantExtraction.extractNWToNE s = Flow.QuadrantExtraction.keepOnlyAt s 3 0 :=
  Flow.QuadrantExtraction.complete s

end Test.Flow.QuadrantExtraction
