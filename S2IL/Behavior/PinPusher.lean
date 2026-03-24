-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Behavior.Gravity
import S2IL.Behavior.Shatter
import S2IL.Shape.GameConfig

/-!
# PinPusher (ピン押し機)

ピン押し機の動作を定義する。

## 概要

ピン押し機は以下の手順でシェイプを加工する:

1. **レイヤ持ち上げ**: 全レイヤを1つ上に持ち上げる（最下層に空レイヤを挿入）
2. **ピン生成**: 元の第1レイヤ（持ち上げ後の第2レイヤ）の非空象限に対して、
   新しい最下層にピン (`P-`) を配置する
3. **レイヤ上限処理**: レイヤ数が上限を超えた場合:
   a. 超過レイヤの結晶クラスタを砕け散らせる
   b. レイヤ数を上限に切り詰める
   c. 落下処理を実行する

持ち上げとピン生成の段階では、結晶の砕け散りや落下は発生しない。
-/

namespace PinPusher

-- ============================================================
-- ステップ 1: レイヤ持ち上げ
-- ============================================================

/-- 全レイヤを1つ上に持ち上げる（最下層に空レイヤを挿入） -/
def liftUp (s : Shape) : Shape :=
    ⟨Layer.empty :: s.layers, by simp⟩

/-- liftUp 後のレイヤ数は元のレイヤ数 + 1 -/
theorem liftUp_layerCount (s : Shape) :
        (liftUp s).layerCount = s.layerCount + 1 := by
    simp [liftUp, Shape.layerCount]

-- ============================================================
-- ステップ 2: ピン生成
-- ============================================================

/-- 元の最下層レイヤの非空象限に対してピンを生成し、新しい最下層に配置する -/
def generatePins (lifted : Shape) (originalBottom : Layer) : Shape :=
    let pinNe := if originalBottom.ne.isEmpty then Quarter.empty else Quarter.pin
    let pinSe := if originalBottom.se.isEmpty then Quarter.empty else Quarter.pin
    let pinSw := if originalBottom.sw.isEmpty then Quarter.empty else Quarter.pin
    let pinNw := if originalBottom.nw.isEmpty then Quarter.empty else Quarter.pin
    let pinLayer : Layer := ⟨pinNe, pinSe, pinSw, pinNw⟩
    ⟨pinLayer :: lifted.layers.tail, by simp⟩


end PinPusher

namespace Shape

-- ============================================================
-- メインピン押し関数
-- ============================================================

/-- ピン押し機を適用する。
    結果が全空の場合は `none` を返す -/
def pinPush (s : Shape) (config : GameConfig) : Option Shape := do
    -- 1. レイヤ持ち上げ
    let lifted := PinPusher.liftUp s
    -- 2. ピン生成
    let withPins := PinPusher.generatePins lifted s.bottom
    -- 3. レイヤ上限チェック
    if withPins.layerCount ≤ config.maxLayers then
        withPins.normalize
    else
        -- 4. レイヤ上限超過時の処理
        -- 4a. 超過レイヤの結晶クラスタを砕け散らせる
        let afterShatter := withPins.shatterOnTruncate config.maxLayers
        -- 4b. レイヤ数を上限に切り詰める
        let truncated := afterShatter.truncate config
        -- 4c. 落下処理
        truncated.gravity

end Shape
