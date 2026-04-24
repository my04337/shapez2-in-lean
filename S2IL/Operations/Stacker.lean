-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel
import S2IL.Operations.Settled
import S2IL.Operations.Gravity
import S2IL.Operations.Shatter

/-!
# S2IL.Operations.Stacker

積層機 (A-2-4 + B-4-1)（Phase C re-scaffold 済み）。
全操作を全関数化（architecture §1.9）。

## 公開 API

- `placeAbove : Shape → Shape → Shape`
- `shatterTopCrystals : Shape → Nat → Shape`
- `stack : Shape → Shape → GameConfig → Shape`（全関数）
- CW 等変性
-/

namespace S2IL

axiom Shape.placeAbove : Shape → Shape → Shape

/-- `shatterTopCrystals s n`: レイヤ番号 ≥ n にある結晶を含む結合クラスタを
    すべて `Quarter.empty` に置換する。 -/
axiom Shape.shatterTopCrystals : Shape → Nat → Shape

/-- 積層（全関数）。0 層入力に対しても well-defined。 -/
axiom Shape.stack : Shape → Shape → GameConfig → Shape

/-- `placeAbove` のレイヤ数は加算。 -/
axiom Shape.placeAbove.layerCount (bottom top : Shape) :
    (Shape.placeAbove bottom top).layerCount = bottom.layerCount + top.layerCount

/-- `placeAbove` と CW 回転は可換。 -/
axiom Shape.placeAbove.rotateCW_comm (bottom top : Shape) :
    Shape.rotateCW (Shape.placeAbove bottom top) =
      Shape.placeAbove (Shape.rotateCW bottom) (Shape.rotateCW top)

/-- `shatterTopCrystals` と CW 回転は可換。 -/
axiom Shape.shatterTopCrystals.rotateCW_comm (s : Shape) (n : Nat) :
    Shape.rotateCW (Shape.shatterTopCrystals s n) =
      Shape.shatterTopCrystals (Shape.rotateCW s) n

/-- `stack` と CW 回転は可換（全関数版、直接等式）。 -/
axiom Shape.stack.rotateCW_comm (bottom top : Shape) (config : GameConfig) :
    Shape.rotateCW (Shape.stack bottom top config) =
      Shape.stack (Shape.rotateCW bottom) (Shape.rotateCW top) config

end S2IL
