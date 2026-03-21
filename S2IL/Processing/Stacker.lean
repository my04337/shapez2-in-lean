-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Processing.Gravity
import S2IL.Processing.Shatter
import S2IL.GameConfig

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
   a. 超過レイヤの脆弱結晶クラスタを砕け散らせる
   b. レイヤ数を上限に切り詰める
   c. 再度落下処理を実行する

## 積層 (Stacking) との連携

- 下側シェイプは落下や砕け散りの影響を受けない
- 上側シェイプの結晶は積み重ねにより **すべて** 砕け散る
- レイヤ数制限は `GameConfig.maxLayers` に従う

仕様の詳細は `docs/shapez2/falling.md` セクション 8 を参照。
-/

namespace Stacker

-- ============================================================
-- ステップ 1: 単純配置 (Place Above)
-- ============================================================

/-- 上側シェイプを下側シェイプの直上に単純配置する。
    結果のレイヤは `bottom.layers ++ top.layers` -/
def placeAbove (bottom top : Shape) : Shape :=
    ⟨bottom.bottom, bottom.upper ++ top.layers⟩

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

-- ============================================================
-- ステップ 5a: truncate 前の砕け散り
-- ============================================================

/-- レイヤ上限超過分の象限を「落下対象」として砕け散り処理を適用する。
    超過レイヤの脆弱結晶が属する結晶結合クラスタ全体が砕け散る -/
def shatterOnTruncate (s : Shape) (maxLayers : Nat) : Shape :=
    let truncatedPositions := (QuarterPos.allValid s).filter fun p =>
        p.layer ≥ maxLayers
    s.shatterOnFall truncatedPositions

end Stacker

namespace Shape

-- ============================================================
-- メイン積層関数
-- ============================================================

/-- 2つのシェイプを積み重ねる。
    `bottom` の上に `top` を配置し、砕け散り・落下・レイヤ制限を適用する。
    結果が全空の場合は `none` を返す -/
def stack (bottom top : Shape) (config : GameConfig := inferInstance)
        : Option Shape := do
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
        -- 5a. 超過レイヤの結晶クラスタを砕け散らせる
        let afterTruncShatter := Stacker.shatterOnTruncate afterGravity config.maxLayers
        -- 5b. レイヤ数を上限に切り詰める
        let truncated := afterTruncShatter.truncate config
        -- 5c. 再落下
        truncated.gravity

end Shape
