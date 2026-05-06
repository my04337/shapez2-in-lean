-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Shatter.Defs
import S2IL.Operations.Shatter.Equivariance

/-!
# S2IL.Operations.Shatter

砕け散り (B-2) の facade。

## 公開 API

- `Shape.shatterMask` — 共通 primitive：位置述語に対応する象限を空に置換する
- `Shape.shatterOnFall` — 落下時砕け散り（脆弱位置リストの結晶結合クラスタを消去）
- `Shape.shatterOnCut` — 切断時砕け散り（東西跨ぎ結晶結合クラスタを消去）
- `Shape.shatterTopCrystals` — 切り詰め時砕け散り（しきい値以上の層に絡む結晶結合クラスタ）
- `Shape.shatterTopCrystals.layerCount_le` — 切り詰め時砕け散りはレイヤ数を増やさない
- 対応する等変性（`*.rotateCW_comm` / `rotate180_comm` / `rotateCCW_comm`）

## サブモジュール（公開）

- `S2IL.Operations.Shatter.Defs` — shatter primitive と各砕け散り述語・操作
- `S2IL.Operations.Shatter.Equivariance` — CW 等変性と 1 行系

## Internal（外部 import 禁止）

- `S2IL.Operations.Shatter.Internal.Mask`

## 等変性の単一チェーン構造

- `shatterMask` で primitive 等変性を 1 本（`rotateCW_comm`）証明し、180° / CCW は CW の合成系。
- `shatterOnFall` / `shatterTopCrystals` は CW を直接証明、180° / CCW は 1 行系。
- `shatterOnCut` は E/W 軸依存（[architecture-layer-ab.md §1.4.1](../../docs/s2il/architecture-layer-ab.md)）。
  CW 等変性は不成立、180° のみ成立し直接証明する。
-/

namespace S2IL

end S2IL
