-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity
import S2IL.Kernel.Transform.Rotate
import S2IL.Operations.Shatter.Shatter
import S2IL.Operations.Settled
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
仕様の詳細は `docs/shapez2/falling.md` セクション 8 を参照。
-/

namespace Stacker

-- ============================================================
-- ステップ 1: 単純配置 (Place Above)
-- ============================================================

/-- 上側シェイプを下側シェイプの直上に単純配置する。
    結果のレイヤは `bottom.layers ++ top.layers` -/
def placeAbove (bottom top : Shape) : Shape :=
    ⟨bottom.layers ++ top.layers,
        by simp only [ne_eq, List.append_eq_nil_iff, bottom.layers_ne, false_and, not_false_eq_true]⟩

/-- placeAbove 後のレイヤ数は下側と上側のレイヤ数の和 -/
theorem placeAbove_layerCount (bottom top : Shape) :
        (placeAbove bottom top).layerCount = bottom.layerCount + top.layerCount := by
    simp only [Shape.layerCount, placeAbove, List.length_append]

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
-- rotate180 等変性補題
-- ============================================================

/-- filter された述語リストの any と元リストの any の関係 -/
private theorem filter_any_eq (l : List QuarterPos) (pred : QuarterPos → Bool)
        (q : QuarterPos) :
        (l.filter pred).any (· == q) = (l.any (· == q) && pred q) := by
    induction l with
    | nil => simp only [List.filter, List.any_nil, List.any, Bool.false_and]
    | cons x xs ih =>
        simp only [List.filter]
        cases hpx : pred x with
        | false =>
            simp only [List.any_cons, ih]
            cases hxq : (x == q) with
            | false => simp only [Bool.false_or]
            | true =>
                have := eq_of_beq hxq; subst this
                simp only [hpx, Bool.and_false, Bool.true_or]
        | true =>
            simp only [List.any_cons, ih]
            cases hxq : (x == q) with
            | false => simp only [Bool.false_or]
            | true =>
                have := eq_of_beq hxq; subst this
                simp only [hpx, Bool.and_true, Bool.true_or, Bool.and_self]

/-- placeAbove は rotate180 と可換 -/
@[aesop norm simp] theorem placeAbove_rotate180 (bottom top : Shape) :
        (placeAbove bottom top).rotate180 =
        placeAbove bottom.rotate180 top.rotate180 := by
    ext
    simp only [placeAbove, Shape.rotate180, Shape.mapLayers, List.map_append,
        List.getElem?_map, List.getElem?_append]

/-- shatterTopCrystals は rotate180 と可換 -/
@[aesop norm simp] theorem shatterTopCrystals_rotate180 (s : Shape) (fromLayer : Nat) :
        (shatterTopCrystals s fromLayer).rotate180 =
        shatterTopCrystals s.rotate180 fromLayer := by
    simp only [shatterTopCrystals]
    rw [Shape.clearPositions_rotate180]
    apply Shape.clearPositions_ext
    intro p
    rw [Gravity.any_map_rotate180_beq, CrystalBond.allValid_rotate180,
        filter_any_eq, filter_any_eq, CrystalBond.allValid_any_rotate180]
    congr 1; congr 1
    rw [QuarterPos.getQuarter_rotate180_inv]

/-- placeAbove は rotateCW と可換 -/
@[aesop norm simp] theorem placeAbove_rotateCW (bottom top : Shape) :
        (placeAbove bottom top).rotateCW =
        placeAbove bottom.rotateCW top.rotateCW := by
    ext
    simp only [placeAbove, Shape.rotateCW, Shape.mapLayers, List.map_append,
        List.getElem?_map, List.getElem?_append]

/-- shatterTopCrystals は rotateCW と可換 -/
@[aesop norm simp] theorem shatterTopCrystals_rotateCW (s : Shape) (fromLayer : Nat) :
        (shatterTopCrystals s fromLayer).rotateCW =
        shatterTopCrystals s.rotateCW fromLayer := by
    simp only [shatterTopCrystals]
    rw [Shape.clearPositions_rotateCW]
    apply Shape.clearPositions_ext
    intro p
    rw [Gravity.any_map_rotateCW_beq, CrystalBond.allValid_rotateCW,
        filter_any_eq, filter_any_eq, CrystalBond.allValid_any_rotateCCW]
    congr 1; congr 1
    rw [QuarterPos.getQuarter_rotateCW_inv]

end Stacker

namespace Shape

-- ============================================================
-- メイン積層関数
-- ============================================================

/-- 2つのシェイプを積み重ねる。
    `bottom` の上に `top` を配置し、砕け散り・落下・レイヤ制限を適用する。
    結果が全空の場合は `none` を返す。
    超過レイヤには工程2により結晶が存在しないため、truncate 前の shatter は不要。 -/
def stack (bottom top : Shape) (config : GameConfig) : Option Shape := do
    -- 1. 単純配置
    let combined := Stacker.placeAbove bottom top
    -- 2. 上側結晶の砕け散り（下側は影響されない）
    let afterShatter := Stacker.shatterTopCrystals combined bottom.layerCount
    -- 3. 落下
    let afterGravity ← afterShatter.gravity
    -- 4. レイヤ上限チェック
    if afterGravity.layerCount ≤ config.maxLayers then
        afterGravity.gravity
    else
        -- 5. レイヤ上限超過時の処理
        -- 超過レイヤは上側シェイプの一部だが、工程2で結晶は砕け散り済みのため shatter 不要
        -- 5a. レイヤ数を上限に切り詰める
        let truncated := afterGravity.truncate config
        -- 5b. 再落下
        truncated.gravity

-- ============================================================
-- rotate180 等変性
-- ============================================================

/-- truncate は rotate180 と可換 -/
@[aesop norm simp] theorem truncate_rotate180 (s : Shape) (config : GameConfig) :
        (s.truncate config).rotate180 = s.rotate180.truncate config := by
    ext
    simp only [truncate, rotate180, mapLayers, List.map_take,
        List.getElem?_map, List.getElem?_take]

/-- truncate は rotateCW と可換 -/
@[aesop norm simp] theorem truncate_rotateCW (s : Shape) (config : GameConfig) :
        (s.truncate config).rotateCW = s.rotateCW.truncate config := by
    ext
    simp only [truncate, rotateCW, mapLayers, List.map_take,
        List.getElem?_map, List.getElem?_take]

/-- settled 入力の placeAbove + shatterTopCrystals 後の gravity と rotate180 は可換。
    波動モデルにより layerCount 制約なしで成立する。
    gravity_rotate180_comm の直接的な系として導出。 -/
theorem process_rotate180_placeAbove_settled (bottom top : Shape)
        (_h_bottom : bottom.IsSettled) (_h_top : top.IsSettled) :
        ((Stacker.shatterTopCrystals (Stacker.placeAbove bottom top) bottom.layerCount).gravity).map Shape.rotate180 =
        (Stacker.shatterTopCrystals (Stacker.placeAbove bottom top) bottom.layerCount).rotate180.gravity :=
    Shape.gravity_rotate180_comm _

/-- stack は rotate180 と可換: 回転してから積層 = 積層してから回転
    settled 入力 (bottom.IsSettled, top.IsSettled) かつ config.maxLayers ≤ 5 の場合に成立する。
    波動モデルにより gravity の等変性が layerCount 制約なしで成立するため、
    Stacker 等変性証明が大幅に簡素化された。 -/
theorem stack_rotate180_comm (bottom top : Shape) (config : GameConfig)
        (_h_config : config.maxLayers ≤ 5) (h_bottom : bottom.IsSettled) (h_top : top.IsSettled) :
        (bottom.stack top config).map Shape.rotate180 =
        bottom.rotate180.stack top.rotate180 config := by
    simp only [Shape.stack, bind]
    conv_rhs =>
        rw [Shape.layerCount_rotate180, ← Stacker.placeAbove_rotate180,
            ← Stacker.shatterTopCrystals_rotate180]
    rw [← process_rotate180_placeAbove_settled bottom top h_bottom h_top]
    cases (Stacker.shatterTopCrystals (Stacker.placeAbove bottom top)
        bottom.layerCount).gravity with
    | none => rfl
    | some ag =>
        simp only [Option.map_some, Option.bind_some]
        rw [Shape.layerCount_rotate180]
        split
        · -- レイヤ上限内: afterGravity.gravity
          exact Shape.gravity_rotate180_comm ag
        · -- レイヤ上限超過: truncate → gravity
          rw [Shape.gravity_rotate180_comm _, Shape.truncate_rotate180]

-- ============================================================
-- rotateCW 等変性
-- ============================================================

/-- settled 入力の placeAbove + shatterTopCrystals 後の gravity と rotateCW は可換。
    波動モデルにより layerCount 制約なしで成立する。
    gravity_rotateCW_comm の直接的な系として導出。 -/
theorem process_rotateCW_placeAbove_settled (bottom top : Shape)
        (_h_bottom : bottom.IsSettled) (_h_top : top.IsSettled) :
        ((Stacker.shatterTopCrystals (Stacker.placeAbove bottom top) bottom.layerCount).gravity).map Shape.rotateCW =
        (Stacker.shatterTopCrystals (Stacker.placeAbove bottom top) bottom.layerCount).rotateCW.gravity :=
    Shape.gravity_rotateCW_comm _

/-- stack は rotateCW と可換: 回転してから積層 = 積層してから回転
    settled 入力 (bottom.IsSettled, top.IsSettled) かつ config.maxLayers ≤ 5 の場合に成立する。
    rotate180 版と同じ構造: 最初の gravity は axiom process_rotateCW_placeAbove_settled による。 -/
theorem stack_rotateCW_comm (bottom top : Shape) (config : GameConfig)
        (_h_config : config.maxLayers ≤ 5) (h_bottom : bottom.IsSettled) (h_top : top.IsSettled) :
        (bottom.stack top config).map Shape.rotateCW =
        bottom.rotateCW.stack top.rotateCW config := by
    simp only [Shape.stack, bind]
    conv_rhs =>
        rw [Shape.layerCount_rotateCW, ← Stacker.placeAbove_rotateCW,
            ← Stacker.shatterTopCrystals_rotateCW]
    rw [← process_rotateCW_placeAbove_settled bottom top h_bottom h_top]
    cases (Stacker.shatterTopCrystals (Stacker.placeAbove bottom top)
        bottom.layerCount).gravity with
    | none => rfl
    | some ag =>
        simp only [Option.map_some, Option.bind_some]
        rw [Shape.layerCount_rotateCW]
        split
        · -- レイヤ上限内: afterGravity.gravity
          exact Shape.gravity_rotateCW_comm ag
        · -- レイヤ上限超過: truncate → gravity
          rw [Shape.gravity_rotateCW_comm _, Shape.truncate_rotateCW]

-- ============================================================
-- rotateCCW 等変性（rCW³ コロラリー）
-- ============================================================

/-- stack は rotateCCW と可換: rotateCCW = rotateCW³ のコロラリーとして導出。
    settled 入力 (bottom.IsSettled, top.IsSettled) かつ config.maxLayers ≤ 5 の場合に成立する。 -/
theorem stack_rotateCCW_comm (bottom top : Shape) (config : GameConfig)
        (h_config : config.maxLayers ≤ 5) (h_bottom : bottom.IsSettled) (h_top : top.IsSettled) :
        (bottom.stack top config).map Shape.rotateCCW =
        bottom.rotateCCW.stack top.rotateCCW config := by
    conv_lhs =>
        rw [show Shape.rotateCCW = Shape.rotateCW ∘ Shape.rotateCW ∘ Shape.rotateCW from
            funext rotateCCW_eq_rotateCW_rotateCW_rotateCW,
            ← Option.map_map, ← Option.map_map]
    rw [stack_rotateCW_comm _ _ _ h_config h_bottom h_top,
        stack_rotateCW_comm _ _ _ h_config
            (IsSettled_rotateCW bottom h_bottom) (IsSettled_rotateCW top h_top),
        stack_rotateCW_comm _ _ _ h_config
            (IsSettled_rotateCW _ (IsSettled_rotateCW bottom h_bottom))
            (IsSettled_rotateCW _ (IsSettled_rotateCW top h_top)),
        ← rotateCCW_eq_rotateCW_rotateCW_rotateCW,
        ← rotateCCW_eq_rotateCW_rotateCW_rotateCW]

-- ============================================================
-- IsSettled 保存定理
-- ============================================================

/-- stack の出力は安定状態。config.maxLayers ≤ 5 の場合に成立する。
    全パスが gravity を経由するため、gravity_IsSettled axiom に帰着する -/
theorem IsSettled_stack (bottom top : Shape) (config : GameConfig) (s' : Shape)
        (h : bottom.stack top config = some s') (h_config : config.maxLayers ≤ 5) :
        s'.IsSettled := by
    simp only [Shape.stack, bind] at h
    cases hg : (Stacker.shatterTopCrystals (Stacker.placeAbove bottom top) bottom.layerCount).gravity with
    | none => rw [hg] at h; cases h
    | some ag =>
        rw [hg] at h
        simp only [Option.bind_some] at h
        split at h
        · -- レイヤ上限内: afterGravity.gravity
          next h_lc =>
            exact Shape.gravity_IsSettled ag s' h (Nat.le_trans h_lc h_config)
        · -- レイヤ上限超過: truncated.gravity
          exact Shape.gravity_IsSettled _ s' h
            (Nat.le_trans (Shape.truncate_layerCount_le ag config) h_config)

end Shape
