-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.Types
import S2IL.Shape.GameConfig
import S2IL.Shape.Arbitrary
import S2IL.Shape.Notation
import S2IL.Shape.Notation.Atom

/-!
# S2IL.Shape facade

Shape 型系（Layer A-1）の公開 API 集約点。

## 公開 API（Types 経由）

- 型: `Color` / `PartCode` / `RegularPartCode` / `Direction` / `Quarter` /
  `Layer` / `Shape` / `QuarterPos` / `GameConfig`
- 基本関数群（各 namespace 参照）

## 公開 API（Notation 経由）

- `Quarter.toString` / `Quarter.ofString?` + round-trip
- `Layer.toString`   / `Layer.ofString?`   + round-trip
- `Shape.toString`   / `Shape.ofString?`   + round-trip（正規化済み）

## 公開 API（GameConfig 経由）

- `GameConfig.vanilla4` / `vanilla5` / `stress8`
- `Shape.truncate` と関連定理

## サブモジュール（公開）

- `S2IL.Shape.Types`       — 核となる型
- `S2IL.Shape.Types.Direction` — 方角と Fin 4 算術
- `S2IL.Shape.Types.Quarter`   — 象限状態
- `S2IL.Shape.Types.Layer`     — 1 レイヤ操作
- `S2IL.Shape.Types.Shape`     — Shape 基本操作・正規化
- `S2IL.Shape.Types.QuarterPos` — 位置と点ごとの Shape 操作
- `S2IL.Shape.GameConfig`  — ゲーム設定
- `S2IL.Shape.Arbitrary`   — Plausible インスタンス
- `S2IL.Shape.Notation`    — Shape Code parse/serialize

## Internal（外部 import 禁止）

- `S2IL.Shape.Internal.Parse`
- `S2IL.Shape.Internal.Serialize`
-/
