-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel.Transform

/-!
# Internal: 回転系の 1 行系補助補題

このファイルは `S2IL.Kernel` namespace の補助補題を集める。
**外部モジュール（`S2IL/Kernel.lean`, `S2IL/Kernel/*.lean` 以外）からは import 禁止**。

単一チェーン原則（[architecture-layer-ab.md §1.4](../../../docs/plans/architecture-layer-ab.md)）
に従い、`rotate180` / `rotateCCW` の系を `rotateCW` から 1 行で導出する補助補題を集める。

Phase B 時点では `rotate180_eq_rotateCW_rotateCW` 等の基礎系を `Transform.lean`
本体に置いている。Phase C で `QuarterPos.rotate180` / `Layer.setDir_rotate180_empty`
等の派生系を本ファイルに集約する。
-/

namespace S2IL.Kernel.Internal.Rotate180Lemmas
end S2IL.Kernel.Internal.Rotate180Lemmas
