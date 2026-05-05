-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import Test.Shape.Atom
import Test.Shape.Types
import Test.Shape.GameConfig
import Test.Shape.Notation
import Test.Kernel.Transform
import Test.Kernel.CrystalBond
import Test.Kernel.CrystalBondCluster
import Test.Operations.ColorMixer
import Test.Operations.CrystalGenerator
import Test.Operations.Cutter
import Test.Operations.Gravity
import Test.Operations.GravityValidation
import Test.Operations.Painter
import Test.Operations.PinPusher
import Test.Operations.Settled
import Test.Operations.Stacker
import Test.Operations.Swapper

/-!
# Test root

Layer A 単体テスト群のエントリポイント。`#guard` ベースで `lake build`
成功 = 全件 pass。各サブモジュールは対応する facade を 1 対 1 で import する
（[architecture-layer-ab.md §4](docs/s2il/architecture-layer-ab.md) Test 配置規約）。

| 階層 | 対象 |
|---|---|
| `Test.Shape.Atom`     | `Color` / `PartCode` / `RegularPartCode`（`toChar` / `ofChar?` / `mix`） |
| `Test.Shape.Types`    | `Direction` / `Quarter` / `Layer` / `Shape` / `QuarterPos` |
| `Test.Shape.GameConfig` | `vanilla4` / `vanilla5` / `stress8` / `truncate` |
| `Test.Shape.Notation` | `Quarter.toString/ofString?` / `Layer.toString/ofString?` / `Shape.toString/ofString?` |
| `Test.Kernel.Transform` | `rotateCW` / `rotate180` / `rotateCCW` の 4 周性 + bijection |
| `Test.Kernel.CrystalBond` | `IsCrystalBonded` / `isCrystalBonded` / 対称性 / CW 等変性 |
| `Test.Kernel.CrystalBondCluster` | `CrystalBondClusterRel` / `crystalBondClusterSet` の基本性質 |
| `Test.Operations.ColorMixer` | `Color.mix` 規則表 |
| `Test.Operations.CrystalGenerator` | `crystallize` の代表値・等変性 |
| `Test.Operations.Cutter` | E/W 半分操作・切断・180° 等変性 |
| `Test.Operations.Gravity` | `Shape.waveStep` の代表 I/O と Behavior A 回帰確認 |
| `Test.Operations.GravityValidation` | Gravity 公開 theorem 群の vanilla / stress Plausible 検証 |
| `Test.Operations.Painter` | `paint` の代表値・等変性 |
| `Test.Operations.PinPusher` | pin push 構成部品・等変性 |
| `Test.Operations.Settled` | `IsSettled` 公開 API と等変性 |
| `Test.Operations.Stacker` | stack 構成部品・等変性 |
| `Test.Operations.Swapper` | swap 代表値・180° 等変性 |
-/
