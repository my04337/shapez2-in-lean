-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.QuarterPos
import S2IL.Shape.GameConfig
import Plausible

/-!
# Plausible 用 Arbitrary / SampleableExt インスタンス

S2IL の主要型に対して `Plausible.Arbitrary` / `Plausible.Shrinkable` / `Plausible.SampleableExt`
インスタンスを定義する。これにより `by plausible` タクティクで S2IL 型を含む
全称命題のランダムテスト（プロパティベーステスト）が可能になる。

## 対応型一覧

| 型 | 生成戦略 |
|---|---|
| `Color` | 8 バリアントから均一選択 |
| `PartCode` | 6 バリアントから均一選択 |
| `RegularPartCode` | 4 バリアントから均一選択 |
| `Direction` | 4 バリアントから均一選択 |
| `Quarter` | empty / pin / crystal / colored を均一選択後、必要なフィールドをランダム生成 |
| `Layer` | 4 象限をそれぞれランダム生成 |
| `Shape` | 1～4 レイヤをランダム生成（非空保証付き） |
| `QuarterPos` | レイヤ位置 (0～7) と方角をランダム生成 |
| `GameConfig` | maxLayers を 1～8 でランダム生成 |
-/

open Plausible

namespace S2IL.Arbitrary

-- ============================================================
-- Color
-- ============================================================

instance : Shrinkable Color where shrink _ := []
instance : Arbitrary Color where
    arbitrary := Gen.oneOf #[
        pure .red, pure .green, pure .blue, pure .yellow,
        pure .cyan, pure .magenta, pure .white, pure .uncolored]
instance : SampleableExt Color where
    proxy := Color; sample := inferInstance; shrink := inferInstance; interp := id

-- ============================================================
-- PartCode
-- ============================================================

instance : Shrinkable PartCode where shrink _ := []
instance : Arbitrary PartCode where
    arbitrary := Gen.oneOf #[
        pure .circle, pure .rectangle, pure .star,
        pure .windmill, pure .pin, pure .crystal]
instance : SampleableExt PartCode where
    proxy := PartCode; sample := inferInstance; shrink := inferInstance; interp := id

-- ============================================================
-- RegularPartCode
-- ============================================================

instance : Shrinkable RegularPartCode where shrink _ := []
instance : Arbitrary RegularPartCode where
    arbitrary := Gen.oneOf #[
        pure .circle, pure .rectangle, pure .star, pure .windmill]
instance : SampleableExt RegularPartCode where
    proxy := RegularPartCode; sample := inferInstance; shrink := inferInstance; interp := id

-- ============================================================
-- Direction
-- ============================================================

instance : Shrinkable Direction where shrink _ := []
instance : Arbitrary Direction where
    arbitrary := Gen.oneOf #[pure .ne, pure .se, pure .sw, pure .nw]
instance : SampleableExt Direction where
    proxy := Direction; sample := inferInstance; shrink := inferInstance; interp := id

-- ============================================================
-- Quarter
-- ============================================================

instance : Shrinkable Quarter where shrink _ := []

/-- Quarter のランダム生成器。4 種のコンストラクタを均一に選択する -/
private def quarterGen : Gen Quarter := do
    let tag ← Gen.oneOf #[pure 0, pure 1, pure 2, pure 3]
    match tag with
    | 0 => return .empty
    | 1 => return .pin
    | 2 => do
        let c ← Arbitrary.arbitrary (α := Color)
        return .crystal c
    | _ => do
        let p ← Arbitrary.arbitrary (α := RegularPartCode)
        let c ← Arbitrary.arbitrary (α := Color)
        return .colored p c

instance : Arbitrary Quarter where arbitrary := quarterGen
instance : SampleableExt Quarter where
    proxy := Quarter; sample := inferInstance; shrink := inferInstance; interp := id

-- ============================================================
-- Layer
-- ============================================================

instance : Shrinkable Layer where shrink _ := []

/-- Layer のランダム生成器。4 象限をそれぞれ独立にランダム生成する -/
private def layerGen : Gen Layer := do
    let ne ← Arbitrary.arbitrary (α := Quarter)
    let se ← Arbitrary.arbitrary (α := Quarter)
    let sw ← Arbitrary.arbitrary (α := Quarter)
    let nw ← Arbitrary.arbitrary (α := Quarter)
    return { ne, se, sw, nw }

instance : Arbitrary Layer where arbitrary := layerGen
instance : SampleableExt Layer where
    proxy := Layer; sample := inferInstance; shrink := inferInstance; interp := id

-- ============================================================
-- Shape
-- ============================================================

instance : Shrinkable Shape where shrink _ := []

/-- Shape のランダム生成器。1～4 レイヤをランダムに生成する -/
private def shapeGen : Gen Shape := do
    let nLayers ← Gen.oneOf #[pure 1, pure 2, pure 3, pure 4]
    let mut layers : List Layer := []
    for _ in List.range nLayers do
        let l ← Arbitrary.arbitrary (α := Layer)
        layers := layers ++ [l]
    match h : layers with
    | [] => return Shape.single Layer.empty
    | _ :: _ => return {
        layers
        layers_ne := by simp only [h, ne_eq, reduceCtorEq, not_false_eq_true]
    }

instance : Arbitrary Shape where arbitrary := shapeGen
instance : SampleableExt Shape where
    proxy := Shape; sample := inferInstance; shrink := inferInstance; interp := id

-- ============================================================
-- QuarterPos
-- ============================================================

instance : Shrinkable QuarterPos where shrink _ := []

/-- QuarterPos のランダム生成器。レイヤ位置 (0～7) と方角を独立に生成する -/
private def quarterPosGen : Gen QuarterPos := do
    let layer ← Gen.oneOf #[pure 0, pure 1, pure 2, pure 3, pure 4, pure 5, pure 6, pure 7]
    let dir ← Arbitrary.arbitrary (α := Direction)
    return { layer, dir }

instance : Arbitrary QuarterPos where arbitrary := quarterPosGen
instance : SampleableExt QuarterPos where
    proxy := QuarterPos; sample := inferInstance; shrink := inferInstance; interp := id

-- ============================================================
-- GameConfig
-- ============================================================

instance : Shrinkable GameConfig where shrink _ := []

/-- GameConfig の Repr インスタンス（Prop フィールドを含むため手動定義） -/
private instance : Repr GameConfig where
    reprPrec gc _ := s!"GameConfig.mk {gc.maxLayers}"

/-- GameConfig のランダム生成器。maxLayers を 1～8 でランダム生成する -/
private def gameConfigGen : Gen GameConfig := do
    Gen.oneOf #[
        pure { maxLayers := 1, maxLayers_pos := by omega },
        pure { maxLayers := 2, maxLayers_pos := by omega },
        pure { maxLayers := 3, maxLayers_pos := by omega },
        pure { maxLayers := 4, maxLayers_pos := by omega },
        pure { maxLayers := 5, maxLayers_pos := by omega },
        pure { maxLayers := 6, maxLayers_pos := by omega },
        pure { maxLayers := 7, maxLayers_pos := by omega },
        pure { maxLayers := 8, maxLayers_pos := by omega }]

instance : Arbitrary GameConfig where arbitrary := gameConfigGen
instance : SampleableExt GameConfig where
    proxy := GameConfig; sample := inferInstance; shrink := inferInstance; interp := id

end S2IL.Arbitrary
