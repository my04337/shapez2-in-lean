-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel

/-!
# S2IL.Operations.PinPusher

ピン押し機 (A-2-5 + B-4-4)。シェイプを 1 レイヤ持ち上げピンを生成する。

## セマンティクス（ゲーム仕様）

入力は常に settled（ベルト規定、glossary.md 参照）。処理順は:

1. `liftUp s` — 全象限を 1 レイヤ上へ移動し、L1 を空にする
2. `generatePins (liftUp s) pinLayer` — 最下層に `pinLayer` を挿入。
   `pinLayer` は元の L1 の非空象限位置にピンを配置した Layer
   （settled 入力では L1 の非空象限と接地象限が一致するため、
    glossary.md「第1レイヤの空でない各象限の下にピンを押し込む」と一致）
3. レイヤ上限超過分を `truncate` で廃棄（上位レイヤ側、crystal はクラスタごと砕ける）
4. `gravity` で安定化して出力

## 公開 API

- `liftUp : Shape → Shape`
- `generatePins : Shape → Layer → Shape`
- `pinPush : Shape → GameConfig → Option Shape`
- CW 等変性

## 単一チェーン原則

CW 等変性のみ axiom、180° / CCW は 1 行系。
-/

namespace S2IL

axiom Shape.liftUp : Shape → Shape
axiom Shape.generatePins : Shape → Layer → Shape
axiom Shape.pinPush : Shape → GameConfig → Option Shape

axiom Shape.liftUp_layerCount (s : Shape) :
    s.liftUp.layerCount = s.layerCount + 1

axiom Shape.liftUp_rotateCW_comm (s : Shape) :
    s.liftUp.rotateCW = s.rotateCW.liftUp

/-- `liftUp` と 180° 回転は可換（CW の系）。 -/
theorem Shape.liftUp_rotate180_comm (s : Shape) :
    s.liftUp.rotate180 = s.rotate180.liftUp := by
  show s.liftUp.rotateCW.rotateCW = s.rotateCW.rotateCW.liftUp
  rw [Shape.liftUp_rotateCW_comm, Shape.liftUp_rotateCW_comm]

-- NOTE: `generatePins` の CW 等変性は signature 依存のため Phase C で整備する。

axiom Shape.pinPush_rotateCW_comm (s : Shape) (config : GameConfig) :
    (s.pinPush config).map Shape.rotateCW = s.rotateCW.pinPush config

end S2IL
