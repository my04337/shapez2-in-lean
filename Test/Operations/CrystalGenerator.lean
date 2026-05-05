-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations

/-!
# Test.Operations.CrystalGenerator

結晶生成機 (A-2-? + B-4-?) のテスト。
`crystallize` は空・ピンを `Quarter.crystal c` で置換、それ以外は不変。
Painter と異なり全レイヤに作用する。
-/

open S2IL

namespace Test.Operations.CrystalGenerator

-- ============================================================
-- Quarter.crystallize
-- ============================================================

#guard Quarter.empty.crystallize Color.red == Quarter.crystal Color.red
#guard Quarter.pin.crystallize Color.green == Quarter.crystal Color.green
-- 既存結晶は不変（色も維持）
#guard (Quarter.crystal Color.blue).crystallize Color.red == Quarter.crystal Color.blue
-- 交換ステーション出力は不変（色も維持）
#guard (Quarter.refined Color.uncolored).crystallize Color.red == Quarter.refined Color.uncolored
#guard (Quarter.vortexPlatform Color.white).crystallize Color.red == Quarter.vortexPlatform Color.white
#guard (Quarter.vortexPlatform Color.black).crystallize Color.red == Quarter.vortexPlatform Color.black
-- 通常パーツは不変
#guard (Quarter.colored .circle Color.uncolored).crystallize Color.red
        == Quarter.colored .circle Color.uncolored
#guard (Quarter.colored .star Color.green).crystallize Color.red
        == Quarter.colored .star Color.green

-- 冪等
example (q : Quarter) (c : Color) :
    (q.crystallize c).crystallize c = q.crystallize c :=
  Quarter.crystallize_idempotent q c

-- ============================================================
-- Layer.crystallize
-- ============================================================

private def L_mixed : Layer :=
  Layer.mk .empty .pin (.refined .uncolored) (.vortexPlatform .black)

#guard (L_mixed.crystallize Color.red) Direction.ne == Quarter.crystal Color.red
#guard (L_mixed.crystallize Color.red) Direction.se == Quarter.crystal Color.red
#guard (L_mixed.crystallize Color.red) Direction.sw == Quarter.refined Color.uncolored
#guard (L_mixed.crystallize Color.red) Direction.nw == Quarter.vortexPlatform Color.black

-- ============================================================
-- Shape.crystallize — 全レイヤに作用
-- ============================================================

private def L_top : Layer :=
  Layer.mk (.colored .rectangle .green) .empty .pin .empty

-- 0 層
#guard Shape.toString (Shape.crystallize [] Color.red) == ""

-- 1 層
example :
    Shape.crystallize [L_mixed] Color.blue = [L_mixed.crystallize Color.blue] := rfl

-- 2 層: 両方のレイヤが結晶化される（Painter との対比）
example :
    Shape.crystallize [L_mixed, L_top] Color.blue
      = [L_mixed.crystallize Color.blue, L_top.crystallize Color.blue] := rfl

-- 冪等（Shape）
example (s : Shape) (c : Color) :
    (Shape.crystallize s c).crystallize c = Shape.crystallize s c :=
  Shape.crystallize.idempotent s c

-- ============================================================
-- 等変性（型のみ確認）
-- ============================================================

example (s : Shape) (c : Color) :
    (Shape.crystallize s c).rotateCW = Shape.crystallize s.rotateCW c :=
  Shape.crystallize.rotateCW_comm s c

example (s : Shape) (c : Color) :
    (Shape.crystallize s c).rotate180 = Shape.crystallize s.rotate180 c :=
  Shape.crystallize.rotate180_comm s c

example (s : Shape) (c : Color) :
    (Shape.crystallize s c).rotateCCW = Shape.crystallize s.rotateCCW c :=
  Shape.crystallize.rotateCCW_comm s c

end Test.Operations.CrystalGenerator
