-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel
import S2IL.Operations.Common
import S2IL.Operations.Settled
import S2IL.Operations.Gravity
import S2IL.Operations.Shatter

/-!
# S2IL.Operations.Stacker

積層機 (A-2-4 + B-4-1)。Phase D-9 で `shatterTopCrystals` 依存も含め axiom-free 化
（残るのは `Shape.gravity` 系のみ、Phase D-10 で降格予定）。

## セマンティクス（ゲーム仕様）

`stack(bottom, top, config)` は次のパイプラインで定義される
（[docs/shapez2/mam.md §4-2](../../docs/shapez2/mam.md)）:

1. `placeAbove bottom top` — bottom の上に top を積む（List 連結）
2. `truncate ... config` — レイヤ上限超過分を捨てる
3. `shatterTopCrystals ... config.maxLayers` — 切り詰め境界に
   触れる結晶クラスタを砕け散らせる（[docs/shapez2/crystal-shatter.md](../../docs/shapez2/crystal-shatter.md)）
4. `gravity` — 浮遊単位を落下させ安定化

## 公開 API

- `Shape.placeAbove : Shape → Shape → Shape`（≃ `bottom ++ top`、全関数）
- `Shape.stack : Shape → Shape → GameConfig → Shape`（合成 `noncomputable def`、全関数）
- 構造的恒等式 (`placeAbove.layerCount`)
- CW 等変性 (`placeAbove.rotateCW_comm` 他) と 180° / CCW 1 行系

## 単一チェーン原則

CW 等変性のみを直接証明、180° / CCW は 1 行系。
`shatterTopCrystals` の本体は `Operations.Shatter` で定義済み（Phase D-9）。

## 残存 axiom

なし（`Shape.gravity` 関連は `Operations.Gravity` 側で残存、Phase D-10）。
-/

namespace S2IL

-- ============================================================
-- placeAbove: bottom の上に top を積む
-- ============================================================

/-- 積層: bottom の上に top を積み重ねる（List 連結）。 -/
def Shape.placeAbove (bottom top : Shape) : Shape := bottom ++ top

@[simp] theorem Shape.placeAbove_nil_left (top : Shape) :
    Shape.placeAbove [] top = top := rfl

@[simp] theorem Shape.placeAbove_nil_right (bottom : Shape) :
    Shape.placeAbove bottom [] = bottom := by
  simp [Shape.placeAbove]

/-- `placeAbove` のレイヤ数は加算。 -/
@[simp] theorem Shape.placeAbove.layerCount (bottom top : Shape) :
    (Shape.placeAbove bottom top).layerCount = bottom.layerCount + top.layerCount := by
  simp [Shape.placeAbove, Shape.layerCount, List.length_append]

/-- `placeAbove` と CW 回転は可換。 -/
theorem Shape.placeAbove.rotateCW_comm (bottom top : Shape) :
    Shape.rotateCW (Shape.placeAbove bottom top) =
      Shape.placeAbove (Shape.rotateCW bottom) (Shape.rotateCW top) := by
  simp [Shape.placeAbove, Shape.rotateCW, List.map_append]

/-- `placeAbove` と 180° 回転は可換（CW の系）。 -/
theorem Shape.placeAbove.rotate180_comm (bottom top : Shape) :
    (Shape.placeAbove bottom top).rotate180 =
      Shape.placeAbove bottom.rotate180 top.rotate180 := by
  simp [Shape.rotate180_eq_rotateCW_rotateCW, Shape.placeAbove.rotateCW_comm]

/-- `placeAbove` と CCW 回転は可換（CW の系）。 -/
theorem Shape.placeAbove.rotateCCW_comm (bottom top : Shape) :
    (Shape.placeAbove bottom top).rotateCCW =
      Shape.placeAbove bottom.rotateCCW top.rotateCCW := by
  simp [Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW, Shape.placeAbove.rotateCW_comm]

-- ============================================================
-- shatterTopCrystals は Operations.Shatter で定義済み（Phase D-9）
-- ============================================================

-- ============================================================
-- stack: パイプライン全体（全関数 def）
-- ============================================================

/-- 積層機（全関数）。
    `gravity ∘ shatterTopCrystals(maxLayers) ∘ truncate ∘ placeAbove`。
    `gravity` がまだ axiom のため `noncomputable`。 -/
noncomputable def Shape.stack (bottom top : Shape) (config : GameConfig) : Shape :=
  Shape.gravity
    (Shape.shatterTopCrystals
      (Shape.truncate (Shape.placeAbove bottom top) config)
      config.maxLayers)

/-- `stack` と CW 回転は可換（合成チェーン）。 -/
theorem Shape.stack.rotateCW_comm (bottom top : Shape) (config : GameConfig) :
    Shape.rotateCW (Shape.stack bottom top config) =
      Shape.stack (Shape.rotateCW bottom) (Shape.rotateCW top) config := by
  unfold Shape.stack
  rw [Shape.gravity.rotateCW_comm,
      Shape.shatterTopCrystals.rotateCW_comm,
      Shape.truncate.rotateCW_comm,
      Shape.placeAbove.rotateCW_comm]

/-- `stack` と 180° 回転は可換（CW の系）。 -/
theorem Shape.stack.rotate180_comm (bottom top : Shape) (config : GameConfig) :
    (Shape.stack bottom top config).rotate180 =
      Shape.stack bottom.rotate180 top.rotate180 config := by
  simp [Shape.rotate180_eq_rotateCW_rotateCW, Shape.stack.rotateCW_comm]

/-- `stack` と CCW 回転は可換（CW の系）。 -/
theorem Shape.stack.rotateCCW_comm (bottom top : Shape) (config : GameConfig) :
    (Shape.stack bottom top config).rotateCCW =
      Shape.stack bottom.rotateCCW top.rotateCCW config := by
  simp [Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW, Shape.stack.rotateCW_comm]

end S2IL
