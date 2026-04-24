-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape

/-!
# S2IL.Kernel.Transform

回転操作 `rotateCW` の中心定義と、`rotate180` / `rotateCCW` の派生。

## 単一チェーン原則

`Shape.rotateCW` のみを axiom 化し、`rotate180` / `rotateCCW` は `rotateCW` の
合成として定義する（[architecture-layer-ab.md §1.4](../../docs/plans/architecture-layer-ab.md)）。

## 公開 API

- `Layer.rotateCW` / `Layer.rotate180` / `Layer.rotateCCW`
- `Shape.rotateCW` / `Shape.rotate180` / `Shape.rotateCCW`
- 各反転性・空性保存・レイヤ数保存の定理

## Internal

- `S2IL.Kernel.Internal.Rotate180Lemmas` — rotateCW 系から派生する系群
-/

namespace S2IL

-- ============================================================
-- Layer
-- ============================================================

/-- レイヤを 180° 回転。`rotateCW` の 2 回合成として定義する。 -/
noncomputable def Layer.rotate180 (l : Layer) : Layer :=
  l.rotateCW.rotateCW

/-- レイヤを反時計回り 90° 回転。`rotateCW` の 3 回合成として定義する。 -/
noncomputable def Layer.rotateCCW (l : Layer) : Layer :=
  l.rotateCW.rotateCW.rotateCW

@[simp] theorem Layer.rotate180_eq_rotateCW_rotateCW (l : Layer) :
    l.rotate180 = l.rotateCW.rotateCW := rfl

@[simp] theorem Layer.rotateCCW_eq_rotateCW_rotateCW_rotateCW (l : Layer) :
    l.rotateCCW = l.rotateCW.rotateCW.rotateCW := rfl

axiom Layer.rotateCW_four (l : Layer) :
    l.rotateCW.rotateCW.rotateCW.rotateCW = l

axiom Layer.isEmpty_rotateCW (l : Layer) :
    l.rotateCW.isEmpty = l.isEmpty

-- ============================================================
-- Shape
-- ============================================================

/-- シェイプを時計回り 90° 回転。 -/
axiom Shape.rotateCW : Shape → Shape

/-- シェイプを 180° 回転。`rotateCW` の 2 回合成として定義する。 -/
noncomputable def Shape.rotate180 (s : Shape) : Shape :=
  s.rotateCW.rotateCW

/-- シェイプを反時計回り 90° 回転。`rotateCW` の 3 回合成として定義する。 -/
noncomputable def Shape.rotateCCW (s : Shape) : Shape :=
  s.rotateCW.rotateCW.rotateCW

@[simp] theorem Shape.rotate180_eq_rotateCW_rotateCW (s : Shape) :
    s.rotate180 = s.rotateCW.rotateCW := rfl

@[simp] theorem Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW (s : Shape) :
    s.rotateCCW = s.rotateCW.rotateCW.rotateCW := rfl

axiom Shape.rotateCW_four (s : Shape) :
    s.rotateCW.rotateCW.rotateCW.rotateCW = s

axiom Shape.layerCount_rotateCW (s : Shape) :
    s.rotateCW.layerCount = s.layerCount

/-- 180° 回転はレイヤ数保存（CW の系）。 -/
theorem Shape.layerCount_rotate180 (s : Shape) :
    s.rotate180.layerCount = s.layerCount := by
  simp [Shape.rotate180_eq_rotateCW_rotateCW, Shape.layerCount_rotateCW]

/-- CCW 回転はレイヤ数保存（CW の系）。 -/
theorem Shape.layerCount_rotateCCW (s : Shape) :
    s.rotateCCW.layerCount = s.layerCount := by
  simp [Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW, Shape.layerCount_rotateCW]

/-- 180°×2 = 恒等（CW×4 の系）。 -/
theorem Shape.rotate180_rotate180 (s : Shape) :
    s.rotate180.rotate180 = s := by
  simp [Shape.rotate180_eq_rotateCW_rotateCW, Shape.rotateCW_four]

end S2IL
