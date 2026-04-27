-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.Types
import S2IL.Shape.GameConfig
import Plausible

/-!
# Plausible 用 Arbitrary / SampleableExt インスタンス

S2IL の主要型に対する Plausible のインスタンスを提供する。
これにより `by plausible` で S2IL 型を含む全称命題のランダム検証が可能。

| 型 | 生成戦略 |
|---|---|
| `Color` | 9 値から均一選択 |
| `PartCode` | 6 値から均一選択 |
| `RegularPartCode` | 4 値から均一選択 |
| `Quarter` | 4 種コンストラクタを均一選択し必要フィールドを生成 |
| `Layer` | 4 象限を独立に生成し `Layer.mk` で合成 |
| `Shape` | 0～4 レイヤをランダム生成 |
| `GameConfig` | `maxLayers` を 1～8 でランダム選択 |

`Direction (= Fin 4)` と `QuarterPos (= Nat × Fin 4)` は Plausible 標準のインスタンスを利用する。
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
    pure .cyan, pure .magenta, pure .white, pure .black, pure .uncolored]
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
-- Quarter
-- ============================================================

instance : Shrinkable Quarter where shrink _ := []

private def quarterGen : Gen Quarter := do
  let tag ← Gen.oneOf #[pure 0, pure 1, pure 2, pure 3]
  match tag with
  | 0 => return .empty
  | 1 => return .pin
  | 2 => return .crystal (← Arbitrary.arbitrary (α := Color))
  | _ =>
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

/-- Layer の Repr。関数型のため `Layer.toString` 経由で出力する。 -/
private instance : Repr Layer where
  reprPrec l _ :=
    repr ((l 0, l 1, l 2, l 3))

private def layerGen : Gen Layer := do
  let q0 ← Arbitrary.arbitrary (α := Quarter)
  let q1 ← Arbitrary.arbitrary (α := Quarter)
  let q2 ← Arbitrary.arbitrary (α := Quarter)
  let q3 ← Arbitrary.arbitrary (α := Quarter)
  return Layer.mk q0 q1 q2 q3

instance : Arbitrary Layer where arbitrary := layerGen
instance : SampleableExt Layer where
  proxy := Layer; sample := inferInstance; shrink := inferInstance; interp := id

-- ============================================================
-- Shape（0～4 レイヤ）
-- ============================================================

instance : Shrinkable Shape where shrink _ := []

private def shapeGen : Gen Shape := do
  let nLayers ← Gen.oneOf #[pure 0, pure 1, pure 2, pure 3, pure 4]
  let mut layers : List Layer := []
  for _ in List.range nLayers do
    let l ← Arbitrary.arbitrary (α := Layer)
    layers := layers ++ [l]
  return layers

instance : Arbitrary Shape where arbitrary := shapeGen
instance : SampleableExt Shape where
  proxy := Shape; sample := inferInstance; shrink := inferInstance; interp := id

-- ============================================================
-- GameConfig
-- ============================================================

instance : Shrinkable GameConfig where shrink _ := []

private instance : Repr GameConfig where
  reprPrec gc _ := s!"GameConfig.mk {gc.maxLayers}"

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
