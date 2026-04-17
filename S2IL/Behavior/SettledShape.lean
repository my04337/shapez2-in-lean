-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Behavior.SettledState
import S2IL.Behavior.PinPusher
import S2IL.Behavior.Stacker
import S2IL.Behavior.Cutter
import S2IL.Shape.Arbitrary
import Plausible

/-!
# SettledShape の操作と Arbitrary インスタンス

`Shape.SettledShape`（`{ s : Shape // s.IsSettled }`）は Gravity.lean で定義されている。
このファイルでは SettledState.lean の保存定理を利用して、SettledShape 上の操作を定義し、
Plausible 用の Arbitrary / SampleableExt インスタンスを提供する。

## 定義済み操作

| 操作 | 型シグネチャ | 利用する保存定理 |
|---|---|---|
| `rotate180` | `SettledShape → SettledShape` | `IsSettled_rotate180`（Gravity.lean） |
| `paint` | `SettledShape → Color → SettledShape` | `IsSettled_paint`（SettledState.lean） |
| `crystallize` | `Shape → Color → SettledShape` | `IsSettled_crystallize`（SettledState.lean） |
| `rotateCW` | `SettledShape → SettledShape` | `IsSettled_rotateCW`（SettledState.lean） |
| `rotateCCW` | `SettledShape → SettledShape` | `IsSettled_rotateCCW`（SettledState.lean） |
| `gravity` | `Shape → (h_lc) → Option SettledShape` | `gravity_IsSettled`（axiom, SettledState.lean） |
| `pinPush` | `SettledShape → GameConfig → (h) → Option SettledShape` | `IsSettled_pinPush`（PinPusher.lean） |
| `stack` | `SettledShape → SettledShape → GameConfig → (h) → Option SettledShape` | `IsSettled_stack`（Stacker.lean） |
| `cut` | `Shape → (h_lc) → Option SettledShape × Option SettledShape` | `IsSettled_cut_*`（Cutter.lean） |
| `halfDestroy` | `Shape → (h_lc) → Option SettledShape` | `IsSettled_halfDestroy`（Cutter.lean） |
-/

open Plausible

namespace Shape.SettledShape

-- ============================================================
-- SettledShape 上の操作定義
-- ============================================================

/-- SettledShape の着色。安定状態は paint で保存される -/
def paint (ss : SettledShape) (c : Color) : SettledShape :=
    ⟨ss.val.paint c, IsSettled_paint ss.val c ss.property⟩

/-- 任意の Shape を結晶化して SettledShape を得る。
    crystallize は入力の安定状態に依存しない -/
def crystallize (s : Shape) (c : Color) : SettledShape :=
    ⟨s.crystallize c, IsSettled_crystallize s c⟩

/-- SettledShape の時計回り 90° 回転。安定状態は rotateCW で保存される -/
def rotateCW (ss : SettledShape) : SettledShape :=
    ⟨ss.val.rotateCW, IsSettled_rotateCW ss.val ss.property⟩

/-- SettledShape の反時計回り 90° 回転。安定状態は rotateCCW で保存される -/
def rotateCCW (ss : SettledShape) : SettledShape :=
    ⟨ss.val.rotateCCW, IsSettled_rotateCCW ss.val ss.property⟩

/-- 任意の Shape に落下処理を適用し SettledShape を返す。layerCount ≤ 5 が必要 -/
def gravity (s : Shape) (h_lc : s.layerCount ≤ 5) : Option SettledShape :=
    match hg : s.gravity with
    | none => none
    | some s' => some ⟨s', gravity_IsSettled s s' hg h_lc⟩

/-- SettledShape にピン押しを適用する。config.maxLayers ≤ 5 が必要 -/
def pinPush (ss : SettledShape) (config : GameConfig)
        (h_config : config.maxLayers ≤ 5) : Option SettledShape :=
    match hg : ss.val.pinPush config with
    | none => none
    | some s' => some ⟨s', IsSettled_pinPush ss.val config s' hg h_config ss.property⟩

/-- SettledShape を積層する。config.maxLayers ≤ 5 が必要 -/
def stack (bottom top : SettledShape) (config : GameConfig)
        (h_config : config.maxLayers ≤ 5) : Option SettledShape :=
    match hg : bottom.val.stack top.val config with
    | none => none
    | some s' => some ⟨s', IsSettled_stack bottom.val top.val config s' hg h_config⟩

/-- Shape を切断し SettledShape のペアを返す。layerCount ≤ 5 が必要 -/
def cut (s : Shape) (h_lc : s.layerCount ≤ 5) : Option SettledShape × Option SettledShape :=
    let result := s.cut
    (match he : result.1 with
     | none => none
     | some s' => some ⟨s', IsSettled_cut_east s s' he h_lc⟩,
     match hw : result.2 with
     | none => none
     | some s' => some ⟨s', IsSettled_cut_west s s' hw h_lc⟩)

/-- Shape に切断処理機を適用し SettledShape を返す。layerCount ≤ 5 が必要 -/
def halfDestroy (s : Shape) (h_lc : s.layerCount ≤ 5) : Option SettledShape :=
    match hg : s.halfDestroy with
    | none => none
    | some s' => some ⟨s', IsSettled_halfDestroy s s' hg h_lc⟩

/-- Option Shape を isSettled 判定で Option SettledShape に変換する -/
private def toSettledOption (os : Option Shape) : Option SettledShape :=
    os.bind (fun s =>
        if h : s.isSettled = true then
            some ⟨s, (Shape.IsSettled_iff_isSettled s).mpr h⟩
        else
            none)

/-- SettledShape のスワップ。内部で `Shape.swap` を実行し、
    出力を isSettled 判定で SettledShape に昇格する -/
def swap (ss1 ss2 : SettledShape) : Option SettledShape × Option SettledShape :=
    let (r1, r2) := ss1.val.swap ss2.val
    (toSettledOption r1, toSettledOption r2)

-- ============================================================
-- 基本性質
-- ============================================================

/-- SettledShape の値が等しければ等しい -/
theorem eq_of_val_eq {ss1 ss2 : SettledShape} (h : ss1.val = ss2.val) : ss1 = ss2 :=
    Subtype.ext h

/-- SettledShape が等しければ値も等しい -/
theorem val_eq_of_eq {ss1 ss2 : SettledShape} (h : ss1 = ss2) : ss1.val = ss2.val :=
    congrArg Subtype.val h

-- ============================================================
-- Decidable / BEq インスタンス
-- ============================================================

/-- IsSettled の決定可能性: floatingUnits が空リストかどうかで判定 -/
instance (s : Shape) : Decidable (s.IsSettled) := by
    simp only [Shape.IsSettled]
    exact inferInstance

/-- SettledShape の等値判定: 内部の Shape で比較する -/
instance : BEq SettledShape where
    beq ss1 ss2 := ss1.val == ss2.val

/-- SettledShape の Repr -/
instance : Repr SettledShape where
    reprPrec ss n := reprPrec ss.val n

/-- SettledShape の ToString。Shape の toString に委譲する -/
instance : ToString SettledShape where
    toString ss := ss.val.toString

-- ============================================================
-- Plausible 用 Arbitrary / SampleableExt インスタンス
-- ============================================================

instance : Shrinkable SettledShape where shrink _ := []

/-- SettledShape のランダム生成器。
    ランダムな Shape を生成し、gravity（落下処理）を適用して安定化する。
    gravity が none を返す場合（全象限が空の場合）は、
    1 レイヤの全象限 empty のシェイプ（常に安定状態）をフォールバックとして使用する -/
private def settledShapeGen : Gen SettledShape := do
    let s ← Arbitrary.arbitrary (α := Shape)
    -- gravity 適用によるランダム SettledShape 生成
    -- isSettled で判定し、安定ならそのまま使用、不安定なら gravity 適用
    if h : s.isSettled = true then
        return ⟨s, (Shape.IsSettled_iff_isSettled s).mpr h⟩
    else
        -- gravity 適用を試みる
        match hg : s.gravity with
        | some s' =>
            -- gravity 出力はランタイム上安定だが、gravity_IsSettled は axiom 化済み（Plan B-1）
            -- isSettled で再判定して Decidable 経由で証明
            if h' : s'.isSettled = true then
                return ⟨s', (Shape.IsSettled_iff_isSettled s').mpr h'⟩
            else
                -- ≥6L で gravity 出力が不安定な場合のフォールバック
                return ⟨Shape.single Layer.empty,
                    by native_decide⟩
        | none =>
            -- gravity が none（normalize 後に空）→ フォールバック
            return ⟨Shape.single Layer.empty,
                by native_decide⟩

instance : Arbitrary SettledShape where arbitrary := settledShapeGen
instance : SampleableExt SettledShape where
    proxy := SettledShape; sample := inferInstance; shrink := inferInstance; interp := id

end Shape.SettledShape
