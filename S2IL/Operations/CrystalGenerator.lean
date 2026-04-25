-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel

/-!
# S2IL.Operations.CrystalGenerator

結晶製造機 (A-2-6)。空象限とピン象限を指定色の結晶で無条件に充填する。

## セマンティクス

- 対象: `Quarter.empty` と `Quarter.pin` の **両方** を指定色の結晶に置換する
  （docs/shapez2/game-system-overview.md「隙間 (Gaps) や ピン (Pins)」に対応）
- 非対象: 既存の通常パーツと結晶は置き換わらない（色も保持）
- 支持条件なし: 接地・settled 判定を問わず全ての empty/pin を結晶化する
  （ゲーム仕様上、出力が必ず settled になるかは stack/pinPush 側の責務）

## 公開 API

- `crystallize : Shape → Color → Shape`
- 冪等性・CW 等変性

## 単一チェーン原則

CW 等変性のみ axiom、180° / CCW は 1 行系。
-/

namespace S2IL

axiom Shape.crystallize : Shape → Color → Shape

/-- `crystallize` は冪等。 -/
axiom Shape.crystallize.idempotent (s : Shape) (c : Color) :
    (Shape.crystallize s c).crystallize c = Shape.crystallize s c

/-- `crystallize` と CW 回転は可換。 -/
axiom Shape.crystallize.rotateCW_comm (s : Shape) (c : Color) :
    (Shape.crystallize s c).rotateCW = Shape.crystallize s.rotateCW c

/-- `crystallize` と 180° 回転は可換（CW の系）。 -/
theorem Shape.crystallize.rotate180_comm (s : Shape) (c : Color) :
    (Shape.crystallize s c).rotate180 = Shape.crystallize s.rotate180 c := by
  simp [Shape.rotate180_eq_rotateCW_rotateCW, Shape.crystallize.rotateCW_comm]

/-- `crystallize` と CCW 回転は可換（CW の系）。 -/
theorem Shape.crystallize.rotateCCW_comm (s : Shape) (c : Color) :
    (Shape.crystallize s c).rotateCCW = Shape.crystallize s.rotateCCW c := by
  simp [Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW, Shape.crystallize.rotateCW_comm]

end S2IL
