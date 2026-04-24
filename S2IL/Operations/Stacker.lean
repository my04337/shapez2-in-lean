-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel
import S2IL.Operations.Settled
import S2IL.Operations.Gravity
import S2IL.Operations.Shatter

/-!
# S2IL.Operations.Stacker

積層機 (A-2-4 + B-4-1)。2 つのシェイプの接続と安定化。

## 公開 API

- `placeAbove : Shape → Shape → Shape` — 上側を下側の直上に配置
- `shatterTopCrystals : Shape → Nat → Shape` — レイヤ ≥ n にかかる結晶結合クラスタの消去
- `stack : Shape → Shape → GameConfig → Option Shape`
- CW 等変性

## 単一チェーン原則

CW 等変性のみ axiom、180° / CCW は 1 行系。
-/

namespace S2IL

axiom Shape.placeAbove : Shape → Shape → Shape
/-- `shatterTopCrystals s n`: レイヤ番号 ≥ n にある結晶を含む結合クラスタを
    すべて `Quarter.empty` に置換する。stack / pinPush による `truncate` 実行時、
    廃棄されるレイヤに含まれる結晶と、それに結合している下位レイヤの結晶が
    まとめて砕ける挙動を表現する補助関数。 -/
axiom Shape.shatterTopCrystals : Shape → Nat → Shape
axiom Shape.stack : Shape → Shape → GameConfig → Option Shape

/-- `placeAbove` のレイヤ数は加算。 -/
axiom Shape.placeAbove_layerCount (bottom top : Shape) :
    (bottom.placeAbove top).layerCount = bottom.layerCount + top.layerCount

/-- `placeAbove` と CW 回転は可換。 -/
axiom Shape.placeAbove_rotateCW_comm (bottom top : Shape) :
    (bottom.placeAbove top).rotateCW = bottom.rotateCW.placeAbove top.rotateCW

/-- `shatterTopCrystals` と CW 回転は可換。 -/
axiom Shape.shatterTopCrystals_rotateCW_comm (s : Shape) (n : Nat) :
    (s.shatterTopCrystals n).rotateCW = s.rotateCW.shatterTopCrystals n

/-- `stack` と CW 回転は可換。 -/
axiom Shape.stack_rotateCW_comm (bottom top : Shape) (config : GameConfig) :
    (bottom.stack top config).map Shape.rotateCW =
      bottom.rotateCW.stack top.rotateCW config

end S2IL
