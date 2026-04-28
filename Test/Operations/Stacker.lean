-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

/-!
# Test.Operations.Stacker

積層機 (A-2-4 + B-4-1) のテスト。

* `placeAbove bottom top := bottom ++ top`（純粋 List 連結）
* `shatterTopCrystals`（Phase D-9 まで axiom、ここでは存在のみ確認）
* `stack` は `gravity ∘ shatterTopCrystals ∘ truncate ∘ placeAbove` の合成
  （`noncomputable`、回転等変性のみテスト）
-/

import S2IL.Operations

open S2IL

namespace Test.Operations.Stacker

-- ============================================================
-- 共通サンプル
-- ============================================================

private def L_a : Layer :=
  Layer.mk (.colored .circle .red) (.colored .star .green)
           (.colored .windmill .blue) (.crystal .yellow)
private def L_b : Layer :=
  Layer.mk (.colored .rectangle .green) .pin .empty (.crystal .red)

private def bot : Shape := [L_a]
private def top : Shape := [L_b, L_b]

-- ============================================================
-- placeAbove: 構造的（List.append）
-- ============================================================

#guard Shape.placeAbove ([] : Shape) top == top
#guard Shape.placeAbove bot ([] : Shape) == bot
#guard Shape.placeAbove bot top == bot ++ top

-- 順序: bottom が下、top が上（List 連結）
example : Shape.placeAbove bot top = [L_a, L_b, L_b] := rfl

-- 結合則（List.append の系）
example (a b c : Shape) :
    Shape.placeAbove (Shape.placeAbove a b) c =
      Shape.placeAbove a (Shape.placeAbove b c) := by
  simp [Shape.placeAbove, List.append_assoc]

-- レイヤ数の加算
example (a b : Shape) :
    (Shape.placeAbove a b).layerCount = a.layerCount + b.layerCount :=
  Shape.placeAbove.layerCount a b

#guard (Shape.placeAbove bot top).layerCount == 3
#guard (Shape.placeAbove top bot).layerCount == 3

-- ============================================================
-- placeAbove: 等変性
-- ============================================================

example (a b : Shape) :
    (Shape.placeAbove a b).rotateCW = Shape.placeAbove a.rotateCW b.rotateCW :=
  Shape.placeAbove.rotateCW_comm a b

example (a b : Shape) :
    (Shape.placeAbove a b).rotate180 = Shape.placeAbove a.rotate180 b.rotate180 :=
  Shape.placeAbove.rotate180_comm a b

example (a b : Shape) :
    (Shape.placeAbove a b).rotateCCW = Shape.placeAbove a.rotateCCW b.rotateCCW :=
  Shape.placeAbove.rotateCCW_comm a b

-- ============================================================
-- shatterTopCrystals: 等変性（axiom 期間中の型確認）
-- ============================================================

example (s : Shape) (n : Nat) :
    (Shape.shatterTopCrystals s n).rotateCW = Shape.shatterTopCrystals s.rotateCW n :=
  Shape.shatterTopCrystals.rotateCW_comm s n

example (s : Shape) (n : Nat) :
    (Shape.shatterTopCrystals s n).rotate180 = Shape.shatterTopCrystals s.rotate180 n :=
  Shape.shatterTopCrystals.rotate180_comm s n

-- ============================================================
-- stack: 合成 def の等変性
-- ============================================================

example (a b : Shape) (cfg : GameConfig) :
    (Shape.stack a b cfg).rotateCW = Shape.stack a.rotateCW b.rotateCW cfg :=
  Shape.stack.rotateCW_comm a b cfg

example (a b : Shape) (cfg : GameConfig) :
    (Shape.stack a b cfg).rotate180 = Shape.stack a.rotate180 b.rotate180 cfg :=
  Shape.stack.rotate180_comm a b cfg

example (a b : Shape) (cfg : GameConfig) :
    (Shape.stack a b cfg).rotateCCW = Shape.stack a.rotateCCW b.rotateCCW cfg :=
  Shape.stack.rotateCCW_comm a b cfg

end Test.Operations.Stacker
