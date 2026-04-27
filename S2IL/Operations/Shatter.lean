-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel

/-!
# S2IL.Operations.Shatter

砕け散り (B-2)。切断時および落下時の脆弱クラスタの消失。

## 公開 API

- `shatterOnCut : Shape → Shape`     — 切断時砕け散り（東西跨ぎクラスタ）
- `shatterOnFall : Shape → List QuarterPos → Shape` — 落下時砕け散り
- 対応する等変性

## 等変性の形

- `shatterOnCut` は E/W 軸依存のため **180° 等変性のみ** 成立（CW は成立しない）。
- `shatterOnFall` は位置リスト引数を回転すれば **CW 等変性** が成立。
-/

namespace S2IL

axiom Shape.shatterOnCut : Shape → Shape
axiom Shape.shatterOnFall : Shape → List QuarterPos → Shape

/-- `shatterOnCut` と 180° 回転は可換（180° は E↔W を保存するため東西跨ぎ性質は
    rotate180 下で不変）。 -/
axiom Shape.shatterOnCut.rotate180_comm (s : Shape) :
    (Shape.shatterOnCut s).rotate180 = Shape.shatterOnCut s.rotate180

/-- `shatterOnFall` と CW 回転は可換（位置リストも回転）。 -/
axiom Shape.shatterOnFall.rotateCW_comm (s : Shape) (ps : List QuarterPos) :
    (Shape.shatterOnFall s ps).rotateCW = Shape.shatterOnFall s.rotateCW (ps.map QuarterPos.rotateCW)

/-- `shatterOnFall` と 180° 回転は可換（CW の系）。 -/
theorem Shape.shatterOnFall.rotate180_comm (s : Shape) (ps : List QuarterPos) :
    (Shape.shatterOnFall s ps).rotate180 =
      Shape.shatterOnFall s.rotate180 (ps.map (QuarterPos.rotateCW ∘ QuarterPos.rotateCW)) := by
  simp [Shape.rotate180_eq_rotateCW_rotateCW, Shape.shatterOnFall.rotateCW_comm,
    List.map_map]

/-- `shatterOnFall` と CCW 回転は可換（CW の系）。 -/
theorem Shape.shatterOnFall.rotateCCW_comm (s : Shape) (ps : List QuarterPos) :
    (Shape.shatterOnFall s ps).rotateCCW =
      Shape.shatterOnFall s.rotateCCW
        (ps.map (QuarterPos.rotateCW ∘ QuarterPos.rotateCW ∘ QuarterPos.rotateCW)) := by
  simp [Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW, Shape.shatterOnFall.rotateCW_comm,
    List.map_map]

end S2IL
