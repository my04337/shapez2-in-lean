-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.Shape

/-!
# Rotate (回転)

シェイプを回転させる加工操作の定義と定理。

回転はゲーム内で最もシンプルな加工操作であり、副作用（落下・破損）を一切伴わない。
全レイヤの各象限を同じ方向に同じ量だけローテートするだけである。

## 回転方向の定義

| 方向 | 説明 | 象限の移動（コード上） |
|---|---|---|
| +90° (CW) | 時計回り 90° | NE→SE, SE→SW, SW→NW, NW→NE |
| −90° (CCW) | 反時計回り 90° | NE→NW, NW→SW, SW→SE, SE→NE |
| 180° | 半回転 | NE↔SW, SE↔NW |

## 設計方針

`Layer.rotateCW` (+90° 時計回り) を唯一の基本プリミティブとし、
他の回転はすべてその合成で定義する。

- `rotateCCW` = `rotateCW` × 3 (反時計回り 90° = 時計回り 270°)
- `rotate180` = `rotateCW` × 2 (180° = 時計回り 180°)

これにより、回転に関する全ての定理が `rotateCW` の性質に帰着でき、
証明が統一的かつ簡潔になる。
-/

-- ============================================================
-- Layer の回転
-- ============================================================

namespace Layer

/-- レイヤを時計回りに 90° 回転させる (回転機 / Rotator)

+90° (CW) の回転では、各象限の内容が時計回りに1つ隣の位置へ移動する:
- NW の内容 → NE の位置
- NE の内容 → SE の位置
- SE の内容 → SW の位置
- SW の内容 → NW の位置

例: `Cr------` (NE のみ赤サークル)
→ 回転後 `--Cr----` (SE に移動)
-/
def rotateCW (l : Layer) : Layer :=
    { ne := l.nw, se := l.ne, sw := l.se, nw := l.sw }

/-- レイヤを反時計回りに 90° 回転させる (逆回転機 / Reverse Rotator)

`rotateCW` を 3 回適用することで定義する (+270° = −90°)。 -/
def rotateCCW (l : Layer) : Layer :=
    l.rotateCW.rotateCW.rotateCW

/-- レイヤを 180° 回転させる (180 度回転機 / 180° Rotator)

`rotateCW` を 2 回適用することで定義する。 -/
def rotate180 (l : Layer) : Layer :=
    l.rotateCW.rotateCW

-- ============================================================
-- Layer の回転に関する定理
-- ============================================================

/-- `rotateCCW` は `rotateCW` の 3 回適用と等しい（定義から自明） -/
theorem rotateCCW_eq_rotateCW_rotateCW_rotateCW (l : Layer) :
        l.rotateCCW = l.rotateCW.rotateCW.rotateCW := rfl

/-- `rotate180` は `rotateCW` の 2 回適用と等しい（定義から自明） -/
theorem rotate180_eq_rotateCW_rotateCW (l : Layer) :
        l.rotate180 = l.rotateCW.rotateCW := rfl

/-- 時計回り 90° 回転を 4 回適用すると元に戻る -/
@[simp] theorem rotateCW_four (l : Layer) :
        l.rotateCW.rotateCW.rotateCW.rotateCW = l := by
    cases l; rfl

/-- 反時計回り回転の後に時計回り回転を適用すると元に戻る -/
@[simp] theorem rotateCCW_rotateCW (l : Layer) :
        l.rotateCCW.rotateCW = l := by
    simp [rotateCCW, rotateCW_four]

/-- 時計回り回転の後に反時計回り回転を適用すると元に戻る -/
@[simp] theorem rotateCW_rotateCCW (l : Layer) :
        l.rotateCW.rotateCCW = l := by
    simp [rotateCCW, rotateCW_four]

/-- 180° 回転を 2 回適用すると元に戻る -/
@[simp] theorem rotate180_rotate180 (l : Layer) :
        l.rotate180.rotate180 = l := by
    simp [rotate180, rotateCW_four]

/-- 反時計回り 90° 回転を 4 回適用すると元に戻る -/
@[simp] theorem rotateCCW_four (l : Layer) :
        l.rotateCCW.rotateCCW.rotateCCW.rotateCCW = l := by
    simp [rotateCCW]

/-- 時計回り回転と 180° 回転は可換である -/
@[simp] theorem rotateCW_rotate180_comm (l : Layer) :
        l.rotateCW.rotate180 = l.rotate180.rotateCW := by
    cases l; rfl

/-- 反時計回り回転と 180° 回転は可換である -/
@[simp] theorem rotateCCW_rotate180_comm (l : Layer) :
        l.rotateCCW.rotate180 = l.rotate180.rotateCCW := by
    cases l; rfl

/-- 時計回り回転と反時計回り回転は可換である -/
@[simp] theorem rotateCW_rotateCCW_comm (l : Layer) :
        l.rotateCW.rotateCCW = l.rotateCCW.rotateCW := by
    simp [rotateCCW]

/-- 180° 回転は反時計回り 90° 回転の 2 回適用と等しい -/
theorem rotate180_eq_rotateCCW_rotateCCW (l : Layer) :
        l.rotate180 = l.rotateCCW.rotateCCW := by
    cases l; rfl

/-- 時計回り 90° 回転の 3 回適用は反時計回り 90° 回転と等しい -/
theorem rotateCW_three_eq_rotateCCW (l : Layer) :
        l.rotateCW.rotateCW.rotateCW = l.rotateCCW := by
    rfl

/-- 回転しても空レイヤの空性は保存される -/
@[simp] theorem isEmpty_rotateCW (l : Layer) :
        l.rotateCW.isEmpty = l.isEmpty := by
    simp [rotateCW, isEmpty, Bool.and_comm, Bool.and_assoc, Bool.and_left_comm]

/-- 反時計回り回転しても空レイヤの空性は保存される -/
@[simp] theorem isEmpty_rotateCCW (l : Layer) :
        l.rotateCCW.isEmpty = l.isEmpty := by
    simp [rotateCCW, isEmpty_rotateCW]

/-- 180° 回転しても空レイヤの空性は保存される -/
@[simp] theorem isEmpty_rotate180 (l : Layer) :
        l.rotate180.isEmpty = l.isEmpty := by
    simp [rotate180, isEmpty_rotateCW]

end Layer

-- ============================================================
-- Shape の回転
-- ============================================================

namespace Shape

/-- シェイプを時計回りに 90° 回転させる (回転機 / Rotator)

全レイヤに `Layer.rotateCW` を適用する。回転は副作用（落下・破損）を伴わない。 -/
def rotateCW (s : Shape) : Shape := s.mapLayers Layer.rotateCW

/-- シェイプを反時計回りに 90° 回転させる (逆回転機 / Reverse Rotator)

全レイヤに `Layer.rotateCCW` を適用する。 -/
def rotateCCW (s : Shape) : Shape := s.mapLayers Layer.rotateCCW

/-- シェイプを 180° 回転させる (180 度回転機 / 180° Rotator)

全レイヤに `Layer.rotate180` を適用する。 -/
def rotate180 (s : Shape) : Shape := s.mapLayers Layer.rotate180

-- ============================================================
-- Shape の回転に関する定理
-- ============================================================

/-- 時計回り 90° 回転を 4 回適用すると元に戻る -/
@[simp] theorem rotateCW_four (s : Shape) :
        s.rotateCW.rotateCW.rotateCW.rotateCW = s := by
    ext; simp [rotateCW, mapLayers, List.map_map, Layer.rotateCW_four]

/-- 反時計回り回転の後に時計回り回転を適用すると元に戻る -/
@[simp] theorem rotateCCW_rotateCW (s : Shape) :
        s.rotateCCW.rotateCW = s := by
    ext; simp [rotateCCW, rotateCW, mapLayers, List.map_map, Layer.rotateCCW_rotateCW]

/-- 時計回り回転の後に反時計回り回転を適用すると元に戻る -/
@[simp] theorem rotateCW_rotateCCW (s : Shape) :
        s.rotateCW.rotateCCW = s := by
    ext; simp [rotateCW, rotateCCW, mapLayers, List.map_map, Layer.rotateCW_rotateCCW]

/-- 180° 回転を 2 回適用すると元に戻る -/
@[simp] theorem rotate180_rotate180 (s : Shape) :
        s.rotate180.rotate180 = s := by
    ext; simp [rotate180, mapLayers, List.map_map, Layer.rotate180_rotate180]

/-- 反時計回り 90° 回転を 4 回適用すると元に戻る -/
@[simp] theorem rotateCCW_four (s : Shape) :
        s.rotateCCW.rotateCCW.rotateCCW.rotateCCW = s := by
    ext; simp [rotateCCW, mapLayers, List.map_map, Layer.rotateCCW_four]

/-- 時計回り回転と 180° 回転は可換である -/
@[simp] theorem rotateCW_rotate180_comm (s : Shape) :
        s.rotateCW.rotate180 = s.rotate180.rotateCW := by
    ext; simp [rotateCW, rotate180, mapLayers, List.map_map, Layer.rotateCW_rotate180_comm]

/-- 反時計回り回転と 180° 回転は可換である -/
@[simp] theorem rotateCCW_rotate180_comm (s : Shape) :
        s.rotateCCW.rotate180 = s.rotate180.rotateCCW := by
    ext; simp [rotateCCW, rotate180, mapLayers, List.map_map, Layer.rotateCCW_rotate180_comm]

/-- 回転してもレイヤ数は変わらない -/
@[simp] theorem layerCount_rotateCW (s : Shape) :
        s.rotateCW.layerCount = s.layerCount := by
    simp [layerCount, rotateCW, mapLayers]

/-- 反時計回り回転してもレイヤ数は変わらない -/
@[simp] theorem layerCount_rotateCCW (s : Shape) :
        s.rotateCCW.layerCount = s.layerCount := by
    simp [layerCount, rotateCCW, mapLayers]

/-- 180° 回転してもレイヤ数は変わらない -/
@[simp] theorem layerCount_rotate180 (s : Shape) :
        s.rotate180.layerCount = s.layerCount := by
    simp [layerCount, rotate180, mapLayers]

end Shape
