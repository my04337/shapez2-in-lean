-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

/-!
# Test root

Layer A 単体テスト群のエントリポイント。`#guard` ベースで `lake build`
成功 = 全件 pass。各サブモジュールは対応する facade を 1 対 1 で import する
（[architecture-layer-ab.md §4](../docs/plans/architecture-layer-ab.md) Test 配置規約）。

| 階層 | 対象 |
|---|---|
| `Test.Shape.Atom`     | `Color` / `PartCode` / `RegularPartCode`（`toChar` / `ofChar?` / `mix`） |
| `Test.Shape.Types`    | `Direction` / `Quarter` / `Layer` / `Shape` / `QuarterPos` |
| `Test.Shape.GameConfig` | `vanilla4` / `vanilla5` / `stress8` / `truncate` |
| `Test.Shape.Notation` | `Quarter.toString/ofString?` / `Layer.toString/ofString?` / `Shape.toString/ofString?` |
| `Test.Kernel.Transform` | `rotateCW` / `rotate180` / `rotateCCW` の 4 周性 + bijection |
| `Test.Kernel.Bond`    | `IsBonded` / `isBonded` / 対称性 / CW 等変性 |
| `Test.Kernel.Cluster` | `ClusterRel` / `clusterSet` の基本性質 |
-/

import Test.Shape.Atom
import Test.Shape.Types
import Test.Shape.GameConfig
import Test.Shape.Notation
import Test.Kernel.Transform
import Test.Kernel.Bond
import Test.Kernel.Cluster
