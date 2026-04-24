-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Common
import S2IL.Operations.HalfDestroyer
import S2IL.Operations.Cutter
import S2IL.Operations.Swapper
import S2IL.Operations.Rotator
import S2IL.Operations.Painter
import S2IL.Operations.ColorMixer
import S2IL.Operations.CrystalGenerator
import S2IL.Operations.Stacker
import S2IL.Operations.PinPusher
import S2IL.Operations.Gravity
import S2IL.Operations.Shatter
import S2IL.Operations.Settled

/-!
# S2IL.Operations facade

全加工操作 (Layer A-2 純粋部 + Layer B 振る舞い系) の統合入口。
Layer C からは本 facade のみを参照すればよい。

## 公開 API（主要）

- 純粋関数：`rotator` / `Shape.paint` / `mix` / `Shape.crystallize` /
  `Shape.placeAbove` / `Shape.shatterTopCrystals` / `Shape.eastHalf` / `Shape.westHalf`
  / `Shape.combineHalves` / `Shape.cut` / `Shape.halfDestroy` / `Shape.swap`
  / `Shape.liftUp` / `Shape.generatePins`
- 振る舞い系：`Shape.gravity` / `Shape.stack` / `Shape.pinPush` /
  `Shape.shatterOnCut` / `Shape.shatterOnFall`
- `Shape.IsSettled` / `Shape.isSettled`
- 各操作の `_rotateCW_comm`（CW 等変性；180° / CCW は 1 行系）

## サブモジュール（公開）

- `S2IL.Operations.Common`            — 共通ユーティリティ
- `S2IL.Operations.HalfDestroyer`     — A-2-1（Cutter の東半分系）
- `S2IL.Operations.Cutter`            — A-2-1 + B-4-2
- `S2IL.Operations.Swapper`           — A-2-1 + B-4-3
- `S2IL.Operations.Rotator`           — A-2-2
- `S2IL.Operations.Painter`           — A-2-3
- `S2IL.Operations.ColorMixer`        — A-2-3
- `S2IL.Operations.CrystalGenerator`  — A-2-6
- `S2IL.Operations.Stacker`           — A-2-4 + B-4-1
- `S2IL.Operations.PinPusher`         — A-2-5 + B-4-4
- `S2IL.Operations.Gravity`           — B-1
- `S2IL.Operations.Shatter`           — B-2
- `S2IL.Operations.Settled`           — B-3

## Internal（外部 import 禁止）

Phase B 時点では Internal ファイルなし。Phase C/D で各操作ごとの
`Operations/<Op>/Internal/` を整備する。
-/
