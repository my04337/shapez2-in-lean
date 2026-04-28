-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

/-!
# Test.Operations.PinPusher

ピン押し機 (A-2-5 + B-4-4) のテスト。

* `liftUp s := Layer.empty :: s`
* `generatePins lifted pinLayer := pinLayer :: lifted.tail`
* `pinLayerOf s` — 元シェイプの `bottomLayer` 非空象限の下にピンを置く
* `pinPush` は `gravity ∘ shatterTopCrystals ∘ truncate ∘ generatePins ∘ liftUp`
  の合成（`noncomputable`、回転等変性のみテスト）
-/

import S2IL.Operations

open S2IL

namespace Test.Operations.PinPusher

-- ============================================================
-- 共通サンプル
-- ============================================================

private def L_full : Layer :=
  Layer.mk (.colored .circle .red) (.colored .star .green)
           (.colored .windmill .blue) (.crystal .yellow)
private def L_partial : Layer :=
  Layer.mk (.colored .circle .red) .empty .empty (.crystal .blue)
private def L_pin : Layer :=
  Layer.mk .pin .empty Quarter.pin .empty

private def s1 : Shape := [L_full]
private def s2 : Shape := [L_full, L_partial]

-- ============================================================
-- liftUp: 最下層に空レイヤを挿入
-- ============================================================

example : Shape.liftUp s1 = [Layer.empty, L_full] := rfl
example : Shape.liftUp ([] : Shape) = [Layer.empty] := rfl

-- レイヤ数 +1
#guard (Shape.liftUp s1).layerCount == 2
#guard (Shape.liftUp s2).layerCount == 3
example (s : Shape) : (Shape.liftUp s).layerCount = s.layerCount + 1 :=
  Shape.liftUp.layerCount s

-- 等変性
example (s : Shape) : (Shape.liftUp s).rotateCW = Shape.liftUp s.rotateCW :=
  Shape.liftUp.rotateCW_comm s
example (s : Shape) : (Shape.liftUp s).rotate180 = Shape.liftUp s.rotate180 :=
  Shape.liftUp.rotate180_comm s
example (s : Shape) : (Shape.liftUp s).rotateCCW = Shape.liftUp s.rotateCCW :=
  Shape.liftUp.rotateCCW_comm s

-- ============================================================
-- generatePins: 最下層を任意レイヤで置換
-- ============================================================

-- 非空 lifted: 最下層が pinLayer に置換、残りはそのまま
example : Shape.generatePins [Layer.empty, L_full] L_pin = [L_pin, L_full] := rfl

-- 空 lifted: 単独 pinLayer を返す（[].tail = []）
example : Shape.generatePins ([] : Shape) L_pin = [L_pin] := rfl

-- 等変性: Shape × Layer 同時 CW
example (lifted : Shape) (pinLayer : Layer) :
    (Shape.generatePins lifted pinLayer).rotateCW =
      Shape.generatePins lifted.rotateCW pinLayer.rotateCW :=
  Shape.generatePins.rotateCW_comm lifted pinLayer

example (lifted : Shape) (pinLayer : Layer) :
    (Shape.generatePins lifted pinLayer).rotate180 =
      Shape.generatePins lifted.rotate180 pinLayer.rotate180 :=
  Shape.generatePins.rotate180_comm lifted pinLayer

example (lifted : Shape) (pinLayer : Layer) :
    (Shape.generatePins lifted pinLayer).rotateCCW =
      Shape.generatePins lifted.rotateCCW pinLayer.rotateCCW :=
  Shape.generatePins.rotateCCW_comm lifted pinLayer

-- ============================================================
-- pinLayerOf: 各方角ごとに非空 → pin、空 → empty
-- ============================================================

-- L_full は全方角非空 → 4 ピン
#guard Shape.pinLayerOf s1 Direction.ne == Quarter.pin
#guard Shape.pinLayerOf s1 Direction.se == Quarter.pin
#guard Shape.pinLayerOf s1 Direction.sw == Quarter.pin
#guard Shape.pinLayerOf s1 Direction.nw == Quarter.pin

-- L_partial は NE/NW のみ非空（s2 の最下層は L_full なので確認は別シェイプで）
private def s_partial : Shape := [L_partial]
#guard Shape.pinLayerOf s_partial Direction.ne == Quarter.pin
#guard Shape.pinLayerOf s_partial Direction.se == Quarter.empty
#guard Shape.pinLayerOf s_partial Direction.sw == Quarter.empty
#guard Shape.pinLayerOf s_partial Direction.nw == Quarter.pin

-- 0 層シェイプ: bottomLayer は Layer.empty なので全方角 empty
#guard Shape.pinLayerOf ([] : Shape) Direction.ne == Quarter.empty
#guard Shape.pinLayerOf ([] : Shape) Direction.sw == Quarter.empty

-- 等変性
example (s : Shape) : s.rotateCW.pinLayerOf = s.pinLayerOf.rotateCW :=
  Shape.pinLayerOf.rotateCW_comm s

-- ============================================================
-- pinPush: 合成 def の等変性
-- ============================================================

example (s : Shape) (cfg : GameConfig) :
    (Shape.pinPush s cfg).rotateCW = Shape.pinPush s.rotateCW cfg :=
  Shape.pinPush.rotateCW_comm s cfg

example (s : Shape) (cfg : GameConfig) :
    (Shape.pinPush s cfg).rotate180 = Shape.pinPush s.rotate180 cfg :=
  Shape.pinPush.rotate180_comm s cfg

example (s : Shape) (cfg : GameConfig) :
    (Shape.pinPush s cfg).rotateCCW = Shape.pinPush s.rotateCCW cfg :=
  Shape.pinPush.rotateCCW_comm s cfg

end Test.Operations.PinPusher
