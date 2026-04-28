-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

/-!
# Test.Operations.Painter

着色機 (A-2-2 + B-4-?) のテスト。

* `Quarter.paint` — 通常パーツのみ色を上書き、それ以外は不変
* `Layer.paint`   — 各象限を `Quarter.paint`
* `Shape.paint`   — 最上位レイヤのみ着色（下層は不変）

CW 等変性は `theorem` の存在確認。
-/

import S2IL.Operations

open S2IL

namespace Test.Operations.Painter

-- ============================================================
-- Quarter.paint
-- ============================================================

#guard Quarter.empty.paint Color.red == Quarter.empty
#guard Quarter.pin.paint Color.red == Quarter.pin
#guard (Quarter.crystal Color.green).paint Color.red == Quarter.crystal Color.green
#guard (Quarter.colored .circle Color.uncolored).paint Color.red
        == Quarter.colored .circle Color.red
#guard (Quarter.colored .star Color.green).paint Color.blue
        == Quarter.colored .star Color.blue

-- 同色で上書きしても不変
#guard (Quarter.colored .windmill Color.red).paint Color.red
        == Quarter.colored .windmill Color.red

-- 冪等
example (q : Quarter) (c : Color) : (q.paint c).paint c = q.paint c :=
  Quarter.paint_idempotent q c

-- ============================================================
-- Layer.paint
-- ============================================================

private def L_mixed : Layer :=
  Layer.mk (.colored .circle .uncolored) .pin
           (.crystal .green) (.colored .star .red)

#guard (L_mixed.paint Color.blue) Direction.ne == Quarter.colored .circle Color.blue
#guard (L_mixed.paint Color.blue) Direction.se == Quarter.pin
#guard (L_mixed.paint Color.blue) Direction.sw == Quarter.crystal Color.green
#guard (L_mixed.paint Color.blue) Direction.nw == Quarter.colored .star Color.blue

example (l : Layer) (c : Color) : (l.paint c).paint c = l.paint c :=
  Layer.paint_idempotent l c

-- ============================================================
-- Shape.paint — 0 / 1 / 多レイヤ
-- ============================================================

-- 0 層: nil
#guard Shape.paint [] Color.red == ([] : Shape)

-- 1 層: そのレイヤを着色
#guard (Shape.paint [L_mixed] Color.blue).length == 1
#guard (Shape.paint [L_mixed] Color.blue).head!  == L_mixed.paint Color.blue

-- 2 層: 最上位（リスト末尾）のみ着色、最下層は不変
private def L_top    : Layer :=
  Layer.mk (.colored .rectangle .green) .empty .empty .empty
private def L_bottom : Layer :=
  Layer.mk (.colored .circle .red) .empty .empty .empty

example :
    Shape.paint [L_bottom, L_top] Color.yellow
      = [L_bottom, L_top.paint Color.yellow] := rfl

-- 3 層: L0 / L1 不変、L2 のみ着色
example :
    Shape.paint [L_bottom, L_bottom, L_top] Color.yellow
      = [L_bottom, L_bottom, L_top.paint Color.yellow] := rfl

-- 長さ保存
example (s : Shape) (c : Color) : (Shape.paint s c).length = s.length :=
  Shape.paint_length s c

-- 冪等
example (s : Shape) (c : Color) :
    Shape.paint (Shape.paint s c) c = Shape.paint s c :=
  Shape.paint.idempotent s c

-- 連続着色: 最後の色で上書き
example :
    Shape.paint (Shape.paint [L_bottom, L_top] Color.red) Color.blue
      = [L_bottom, L_top.paint Color.blue] := rfl

-- ============================================================
-- 等変性（型のみ確認）
-- ============================================================

example (s : Shape) (c : Color) :
    (Shape.paint s c).rotateCW = Shape.paint s.rotateCW c :=
  Shape.paint.rotateCW_comm s c

example (s : Shape) (c : Color) :
    (Shape.paint s c).rotate180 = Shape.paint s.rotate180 c :=
  Shape.paint.rotate180_comm s c

example (s : Shape) (c : Color) :
    (Shape.paint s c).rotateCCW = Shape.paint s.rotateCCW c :=
  Shape.paint.rotateCCW_comm s c

end Test.Operations.Painter
