-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape

/-!
# S2IL.Kernel.Transform

回転操作の中心定義。全て `def` で具体化されている（Phase C re-scaffold 済み）。

## 設計

- `Layer.rotateCW` は `Shape/Types.lean` で定義済み（`fun d => l (d - 1)`）
- `Shape.rotateCW` は `List.map Layer.rotateCW` として定義
- `rotate180` / `rotateCCW` は単一チェーン原則（§1.4）で CW の合成

## 公開 API

- `Shape.rotateCW` / `Shape.rotate180` / `Shape.rotateCCW`
- `Layer.rotate180` / `Layer.rotateCCW`
- 4 周性・レイヤ数保存（全て theorem）

## Internal

- `S2IL.Kernel.Internal.Rotate180Lemmas` — 書換系（Phase C で整備）
-/

namespace S2IL

-- ============================================================
-- Layer（rotateCW は Types.lean で定義済み）
-- ============================================================

/-- レイヤを 180° 回転。`rotateCW` の 2 回合成として定義する。 -/
def Layer.rotate180 (l : Layer) : Layer :=
  l.rotateCW.rotateCW

/-- レイヤを反時計回り 90° 回転。`rotateCW` の 3 回合成として定義する。 -/
def Layer.rotateCCW (l : Layer) : Layer :=
  l.rotateCW.rotateCW.rotateCW

@[simp] theorem Layer.rotate180_eq_rotateCW_rotateCW (l : Layer) :
    l.rotate180 = l.rotateCW.rotateCW := rfl

@[simp] theorem Layer.rotateCCW_eq_rotateCW_rotateCW_rotateCW (l : Layer) :
    l.rotateCCW = l.rotateCW.rotateCW.rotateCW := rfl

/-- Layer の 4 周性。`Layer.rotateCW` は `fun d => l (d - 1)` なので、
    4 回適用で `fun d => l (d - 4)` = `fun d => l d`。 -/
theorem Layer.rotateCW.four (l : Layer) :
    l.rotateCW.rotateCW.rotateCW.rotateCW = l := by
  funext d; simp [Layer.rotateCW]; congr 1; omega

-- ============================================================
-- Shape
-- ============================================================

/-- シェイプを時計回り 90° 回転。各レイヤに `Layer.rotateCW` を適用。 -/
def Shape.rotateCW (s : Shape) : Shape := s.map Layer.rotateCW

/-- シェイプを 180° 回転。`rotateCW` の 2 回合成として定義する。 -/
def Shape.rotate180 (s : Shape) : Shape :=
  s.rotateCW.rotateCW

/-- シェイプを反時計回り 90° 回転。`rotateCW` の 3 回合成として定義する。 -/
def Shape.rotateCCW (s : Shape) : Shape :=
  s.rotateCW.rotateCW.rotateCW

@[simp] theorem Shape.rotate180_eq_rotateCW_rotateCW (s : Shape) :
    s.rotate180 = s.rotateCW.rotateCW := rfl

@[simp] theorem Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW (s : Shape) :
    s.rotateCCW = s.rotateCW.rotateCW.rotateCW := rfl

/-- Shape の 4 周性。 -/
theorem Shape.rotateCW.four (s : Shape) :
    s.rotateCW.rotateCW.rotateCW.rotateCW = s := by
  simp only [Shape.rotateCW, List.map_map]
  have : (Layer.rotateCW ∘ Layer.rotateCW ∘ Layer.rotateCW ∘ Layer.rotateCW) = id := by
    funext l; exact Layer.rotateCW.four l
  rw [show Layer.rotateCW ∘ (Layer.rotateCW ∘ (Layer.rotateCW ∘ Layer.rotateCW))
      = Layer.rotateCW ∘ Layer.rotateCW ∘ Layer.rotateCW ∘ Layer.rotateCW from rfl,
      this, List.map_id]

/-- CW 回転はレイヤ数を保存。 -/
theorem Shape.layerCount.rotateCW (s : Shape) :
    s.rotateCW.layerCount = s.layerCount := by
  simp [Shape.rotateCW, Shape.layerCount, List.length_map]

/-- 180° 回転はレイヤ数保存（CW の系）。 -/
theorem Shape.layerCount.rotate180 (s : Shape) :
    s.rotate180.layerCount = s.layerCount := by
  simp [Shape.rotate180_eq_rotateCW_rotateCW, Shape.layerCount.rotateCW]

/-- CCW 回転はレイヤ数保存（CW の系）。 -/
theorem Shape.layerCount.rotateCCW (s : Shape) :
    s.rotateCCW.layerCount = s.layerCount := by
  simp [Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW, Shape.layerCount.rotateCW]

end S2IL
