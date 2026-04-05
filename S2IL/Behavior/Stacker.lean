-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Behavior.Gravity
import S2IL.Behavior.Shatter
import S2IL.Shape.GameConfig

/-!
# Stacker (積層機)

2つのシェイプを積み重ねる操作の定義。

## 概要

積層機は下側 (bottom) と上側 (top) の2つのシェイプを受け取り、
上側を下側の上に配置する。処理の流れは以下の通り:

1. **単純配置**: 下側レイヤの直上に上側レイヤを連結する
2. **上側結晶の砕け散り**: 上側の全結晶を除去する（クラスタ伝播なし、下側は影響されない）
3. **落下**: 浮遊している落下単位を下方に移動させる
4. **レイヤ上限超過時の処理**:
   a. レイヤ数を上限に切り詰める
   b. 再度落下処理を実行する

## 積層 (Stacking) との連携

- 下側シェイプは落下や砕け散りの影響を受けない
- 上側シェイプの結晶は積み重ねにより **すべて** 砕け散る
- レイヤ数制限は引数で渡される `GameConfig` の `maxLayers` に従う
- **前提**: `bottom` および `top` はそれぞれレイヤ数が `config.maxLayers` 以内であること

仕様の詳細は `docs/shapez2/falling.md` セクション 8 を参照。
-/

namespace Stacker

-- ============================================================
-- ステップ 1: 単純配置 (Place Above)
-- ============================================================

/-- 上側シェイプを下側シェイプの直上に単純配置する。
    結果のレイヤは `bottom.layers ++ top.layers` -/
def placeAbove (bottom top : Shape) : Shape :=
    ⟨bottom.layers ++ top.layers, by simp [bottom.layers_ne]⟩

/-- placeAbove 後のレイヤ数は下側と上側のレイヤ数の和 -/
theorem placeAbove_layerCount (bottom top : Shape) :
        (placeAbove bottom top).layerCount = bottom.layerCount + top.layerCount := by
    simp [placeAbove, Shape.layerCount, List.length_append]

-- ============================================================
-- ステップ 2: 上側結晶の砕け散り
-- ============================================================

/-- 指定レイヤ以上の全結晶象限を除去する。
    クラスタ伝播は行わない（上側の結晶のみが対象） -/
def shatterTopCrystals (s : Shape) (fromLayer : Nat) : Shape :=
    let targets := (QuarterPos.allValid s).filter fun p =>
        p.layer ≥ fromLayer &&
        match p.getQuarter s with
        | some q => q.isFragile
        | none   => false
    s.clearPositions targets


end Stacker

namespace Shape

-- ============================================================
-- メイン積層関数
-- ============================================================

/-- 2つのシェイプを積み重ねる。
    `bottom` の上に `top` を配置し、砕け散り・落下・レイヤ制限を適用する。
    結果が全空の場合は `none` を返す。
    前提: `bottom` および `top` はそれぞれレイヤ数が `config.maxLayers` 以内であること。
    超過レイヤには工程2により結晶が存在しないため、truncate 前の shatter は不要。 -/
def stack (bottom top : Shape) (config : GameConfig)
        (_h_bottom : bottom.layerCount ≤ config.maxLayers)
        (_h_top : top.layerCount ≤ config.maxLayers) : Option Shape := do
    -- 1. 単純配置
    let combined := Stacker.placeAbove bottom top
    -- 2. 上側結晶の砕け散り（下側は影響されない）
    let afterShatter := Stacker.shatterTopCrystals combined bottom.layerCount
    -- 3. 落下
    let afterGravity ← afterShatter.gravity
    -- 4. レイヤ上限チェック
    if afterGravity.layerCount ≤ config.maxLayers then
        return afterGravity
    else
        -- 5. レイヤ上限超過時の処理
        -- 超過レイヤは上側シェイプの一部だが、工程2で結晶は砕け散り済みのため shatter 不要
        -- 5a. レイヤ数を上限に切り詰める
        let truncated := afterGravity.truncate config
        -- 5b. 再落下
        truncated.gravity

end Shape
