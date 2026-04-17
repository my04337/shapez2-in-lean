-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Behavior.Gravity
import S2IL.Behavior.Shatter
import S2IL.Behavior.Rotate
import S2IL.Behavior.SettledState

/-!
# Cutter (切断)

シェイプを南北方向で東西に二分する切断操作の定義。

## 切断装置

| 名称 | 動作 | 出力 |
|---|---|---|
| **切断処理機 (Half-Destroyer)** | 西側の半分を消去 | 東側の半分のみ |
| **切断機 (Cutter)** | 東西に分割 | (東側の半分, 西側の半分) |
| **スワップ機 (Swapper)** | 2つのシェイプの西側を入れ替え | 入れ替え後の2つのシェイプ |

## 切断の処理フロー

### 切断処理機・切断機

```
1. 砕け散り (shatterOnCut)
   - 東西に跨がる結晶結合クラスタを砕け散らせる
2. 東西分離
   - East Half と West Half に分離する
3. 各半分の安定化 (settleAfterCut)
   a. 浮遊判定
   b. 落下前砕け散り (shatterOnFall)
   c. 落下 (gravity)
4. 正規化
```

### スワップ機

```
1. 各シェイプの砕け散り (shatterOnCut)
2. 各シェイプの安定化 (settleAfterCut)
3. 安定化済みの西側半分を入れ替え
4. 各結果を正規化
```

## 設計方針

レイヤレベルの半分抽出 (`Layer.eastHalf`, `Layer.westHalf`) を基本プリミティブとし、
Shape レベルの操作はレイヤ関数の `map` で定義する。
安定化ヘルパー `settleAfterCut` は `shatterOnFall` + `gravity` を組み合わせる。
-/

-- ============================================================
-- レイヤレベルの半分操作
-- ============================================================

namespace Layer

/-- レイヤの東側の半分 (NE, SE) を維持し、西側 (NW, SW) を空にする -/
def eastHalf (l : Layer) : Layer :=
    { ne := l.ne, se := l.se, sw := .empty, nw := .empty }

/-- レイヤの西側の半分 (NW, SW) を維持し、東側 (NE, SE) を空にする -/
def westHalf (l : Layer) : Layer :=
    { ne := .empty, se := .empty, sw := l.sw, nw := l.nw }

/-- 2つのレイヤの東側と西側を合成する。
    `east` から NE, SE を、`west` から NW, SW を取る -/
def combineEastWest (east west : Layer) : Layer :=
    { ne := east.ne, se := east.se, sw := west.sw, nw := west.nw }

-- ============================================================
-- レイヤレベルの定理
-- ============================================================

/-- eastHalf と westHalf を合成すると元のレイヤに戻る -/
theorem combineEastWest_eastHalf_westHalf (l : Layer) :
        combineEastWest l.eastHalf l.westHalf = l := by
    cases l; rfl

/-- eastHalf の東側象限は元のレイヤと同じ -/
theorem eastHalf_ne (l : Layer) : l.eastHalf.ne = l.ne := rfl
theorem eastHalf_se (l : Layer) : l.eastHalf.se = l.se := rfl

/-- westHalf の西側象限は元のレイヤと同じ -/
theorem westHalf_sw (l : Layer) : l.westHalf.sw = l.sw := rfl
theorem westHalf_nw (l : Layer) : l.westHalf.nw = l.nw := rfl

/-- eastHalf の西側象限は空 -/
theorem eastHalf_sw (l : Layer) : l.eastHalf.sw = .empty := rfl
theorem eastHalf_nw (l : Layer) : l.eastHalf.nw = .empty := rfl

/-- westHalf の東側象限は空 -/
theorem westHalf_ne (l : Layer) : l.westHalf.ne = .empty := rfl
theorem westHalf_se (l : Layer) : l.westHalf.se = .empty := rfl

/-- eastHalf は冪等 -/
@[simp] theorem eastHalf_eastHalf (l : Layer) : l.eastHalf.eastHalf = l.eastHalf := by
    cases l; rfl

/-- westHalf は冪等 -/
@[simp] theorem westHalf_westHalf (l : Layer) : l.westHalf.westHalf = l.westHalf := by
    cases l; rfl

/-- 180° 回転で eastHalf と westHalf が入れ替わる -/
@[aesop norm simp] theorem eastHalf_rotate180 (l : Layer) :
        l.eastHalf.rotate180 = l.rotate180.westHalf := by
    cases l; rfl

@[aesop norm simp] theorem westHalf_rotate180 (l : Layer) :
        l.westHalf.rotate180 = l.rotate180.eastHalf := by
    cases l; rfl

/-- combineEastWest を 180° 回転すると東西が入れ替わる -/
@[aesop norm simp] theorem combineEastWest_rotate180 (east west : Layer) :
        (combineEastWest east west).rotate180 =
        combineEastWest west.rotate180 east.rotate180 := by
    cases east; cases west; rfl

end Layer

-- ============================================================
-- シェイプレベルの半分操作
-- ============================================================

namespace Shape

/-- シェイプの東側の半分を抽出する。全レイヤの西側象限を空にする -/
def eastHalf (s : Shape) : Shape := s.mapLayers Layer.eastHalf

/-- シェイプの西側の半分を抽出する。全レイヤの東側象限を空にする -/
def westHalf (s : Shape) : Shape := s.mapLayers Layer.westHalf

-- ============================================================
-- シェイプ半分合成のためのユーティリティ
-- ============================================================

/-- 2つのリストを合成する。短い方は空レイヤでパディング -/
private def zipLayersWithPad (eastLayers westLayers : List Layer) : List Layer :=
    let rec go : List Layer → List Layer → List Layer
        | [], [] => []
        | [], w :: ws => Layer.combineEastWest Layer.empty w :: go [] ws
        | e :: es, [] => Layer.combineEastWest e Layer.empty :: go es []
        | e :: es, w :: ws => Layer.combineEastWest e w :: go es ws
    go eastLayers westLayers

/-- 2つのシェイプの東側と西側を合成する。
    `east` から NE, SE を、`west` から NW, SW を取る。
    レイヤ数が異なる場合は短い方を空レイヤでパディング -/
def combineHalves (east west : Shape) : Shape :=
    let combined := zipLayersWithPad east.layers west.layers
    match combined with
    | []      => ⟨[Layer.empty], by simp only [ne_eq, List.cons_ne_self, not_false_eq_true]⟩  -- ありえないが安全策
    | b :: us => ⟨b :: us, List.cons_ne_nil b us⟩

-- ============================================================
-- 安定化ヘルパー
-- ============================================================

/-- 切断後の安定化。浮遊判定 → 落下前砕け散り → 落下 → 正規化。
    全パスが gravity を経由する（isEmpty 時: gravity = normalize、else 時: afterShatter.gravity） -/
def settleAfterCut (s : Shape) : Option Shape :=
    let units := Gravity.floatingUnits s
    if units.isEmpty then
        s.gravity
    else
        -- 浮遊位置を収集
        let fallingPositions := units.flatMap Gravity.FallingUnit.positions
        -- 落下前砕け散り
        let afterShatter := s.shatterOnFall fallingPositions
        -- 落下
        afterShatter.gravity

-- ============================================================
-- 切断処理機 (Half-Destroyer)
-- ============================================================

/-- 切断処理機: 西側の半分を消去し、東側の半分のみを出力する。
    1. 東西跨ぎクラスタの砕け散り (shatterOnCut)
    2. 東側の半分を抽出 (eastHalf)
    3. 安定化 (settleAfterCut) -/
def halfDestroy (s : Shape) : Option Shape :=
    let afterShatter := s.shatterOnCut
    let east := afterShatter.eastHalf
    east.settleAfterCut

-- ============================================================
-- 切断機 (Cutter)
-- ============================================================

/-- 切断機: シェイプを東西に分割する。
    1. 東西跨ぎクラスタの砕け散り (shatterOnCut)
    2. 東側と西側に分離
    3. 各半分を安定化 (settleAfterCut)
    戻り値: (東側の半分, 西側の半分) -/
def cut (s : Shape) : Option Shape × Option Shape :=
    let afterShatter := s.shatterOnCut
    let east := afterShatter.eastHalf.settleAfterCut
    let west := afterShatter.westHalf.settleAfterCut
    (east, west)

-- ============================================================
-- スワップ機 (Swapper)
-- ============================================================

/-- スワップ機: 2つのシェイプの西側の半分を入れ替える。
    1. 各シェイプに砕け散り (shatterOnCut) を適用
    2. 各シェイプを安定化 (settleAfterCut)
    3. 安定化後の西側半分を入れ替え (combineHalves)
    4. 各結果を正規化
    戻り値: (入れ替え後のシェイプ1, 入れ替え後のシェイプ2) -/
def swap (s1 s2 : Shape) : Option Shape × Option Shape :=
    -- 1. 砕け散り
    let s1AfterShatter := s1.shatterOnCut
    let s2AfterShatter := s2.shatterOnCut
    -- 2. 安定化
    match s1AfterShatter.settleAfterCut, s2AfterShatter.settleAfterCut with
    | some settled1, some settled2 =>
        -- 3. 西側を入れ替えて合成
        let result1 := combineHalves settled1 settled2
        let result2 := combineHalves settled2 settled1
        -- 4. 正規化
        (result1.normalize, result2.normalize)
    | some settled1, none =>
        -- s2 が全空になった場合: s1 の東側のみ残る
        let result1 := settled1.eastHalf
        (result1.normalize, none)
    | none, some settled2 =>
        -- s1 が全空になった場合: s2 の東側のみ残る
        let result2 := settled2.eastHalf
        (none, result2.normalize)
    | none, none =>
        (none, none)

-- ============================================================
-- 定理
-- ============================================================

/-- 同一リストの eastHalf/westHalf に zipLayersWithPad.go を適用すると元に戻る -/
private theorem zipLayersWithPad_go_eastWest (ls : List Layer) :
        zipLayersWithPad.go (ls.map Layer.eastHalf) (ls.map Layer.westHalf) = ls := by
    induction ls with
    | nil => simp only [List.map_nil, zipLayersWithPad.go]
    | cons l rest ih =>
        simp only [List.map, zipLayersWithPad.go, Layer.combineEastWest_eastHalf_westHalf, ih]

/-- eastHalf と westHalf を合成すると元のシェイプに戻る -/
theorem eastHalf_westHalf_combine (s : Shape) :
        combineHalves s.eastHalf s.westHalf = s := by
    simp only [combineHalves, zipLayersWithPad, eastHalf, westHalf, mapLayers,
               zipLayersWithPad_go_eastWest]
    cases hl : s.layers with
    | nil => exact absurd hl s.layers_ne
    | cons b us => exact Shape.ext hl.symm

/-- halfDestroy の結果は cut の東側出力と一致する -/
theorem halfDestroy_eq_cut_east (s : Shape) :
        s.halfDestroy = s.cut.1 := by
    simp only [halfDestroy, cut]

/-- 同一リストに zipLayersWithPad.go を適用すると元のリストに戻る -/
private theorem zipLayersWithPad_go_self (ls : List Layer) :
        zipLayersWithPad.go ls ls = ls := by
    induction ls with
    | nil => simp only [zipLayersWithPad.go]
    | cons l rest ih =>
        simp only [zipLayersWithPad.go, ih]
        cases l; rfl

/-- 同一シェイプを combineHalves すると元のシェイプに戻る -/
theorem combineHalves_self (s : Shape) : combineHalves s s = s := by
    simp only [combineHalves, zipLayersWithPad, zipLayersWithPad_go_self]
    cases hl : s.layers with
    | nil => exact absurd hl s.layers_ne
    | cons b us => exact Shape.ext hl.symm

/-- zipLayersWithPad.go と rotate180 の関係: 東西が入れ替わる -/
private theorem zipLayersWithPad_go_rotate180 (ls1 ls2 : List Layer) :
        (zipLayersWithPad.go ls1 ls2).map Layer.rotate180 =
        zipLayersWithPad.go (ls2.map Layer.rotate180) (ls1.map Layer.rotate180) := by
    induction ls1 generalizing ls2 with
    | nil =>
        induction ls2 with
        | nil => simp only [zipLayersWithPad.go, List.map_nil]
        | cons w ws ih =>
            simp only [zipLayersWithPad.go, List.map_nil, List.map_cons,
                        Layer.combineEastWest_rotate180, ih]; rfl
    | cons e es ih =>
        cases ls2 with
        | nil =>
            simp only [zipLayersWithPad.go, List.map_cons, List.map_nil,
                        Layer.combineEastWest_rotate180, ih]; rfl
        | cons w ws =>
            simp only [zipLayersWithPad.go, List.map_cons,
                        Layer.combineEastWest_rotate180, ih]

-- ============================================================
-- 180° 回転等変性
-- ============================================================

/-- normalize と rotate180 は可換 -/
private theorem normalize_rotate180 (s : Shape) :
        (s.normalize).map Shape.rotate180 = s.rotate180.normalize := by
    exact s.normalize_map_layers Layer.rotate180 Layer.isEmpty_rotate180

/-- Shape.eastHalf と rotate180 は westHalf に変換される -/
@[aesop norm simp] theorem eastHalf_rotate180 (s : Shape) :
        s.eastHalf.rotate180 = s.rotate180.westHalf := by
    ext; simp only [rotate180, mapLayers, eastHalf, List.map_map,
              List.getElem?_map, Option.map_eq_some_iff, Function.comp_apply,
              Layer.eastHalf_rotate180, westHalf]

/-- Shape.westHalf と rotate180 は eastHalf に変換される -/
@[aesop norm simp] theorem westHalf_rotate180 (s : Shape) :
        s.westHalf.rotate180 = s.rotate180.eastHalf := by
    ext; simp only [rotate180, mapLayers, westHalf, List.map_map,
              List.getElem?_map, Option.map_eq_some_iff, Function.comp_apply,
              Layer.westHalf_rotate180, eastHalf]

/-- settleAfterCut と rotate180 は可換
    layerCount ≤ 5 の場合に成立する -/
private theorem settleAfterCut_rotate180 (s : Shape) (h : s.layerCount ≤ 5) :
        (s.settleAfterCut).map Shape.rotate180 = s.rotate180.settleAfterCut := by
    simp only [settleAfterCut, apply_ite (Option.map Shape.rotate180)]
    rw [← Gravity.floatingUnits_isEmpty_rotate180]
    split
    · -- isEmpty = true → gravity
      exact gravity_rotate180_comm s h
    · -- isEmpty = false → gravity
      have h_sf : (s.shatterOnFall ((Gravity.floatingUnits s).flatMap
            Gravity.FallingUnit.positions)).layerCount ≤ 5 := by
        simp only [shatterOnFall, layerCount_clearPositions]; exact h
      rw [gravity_rotate180_comm _ h_sf, shatterOnFall_rotate180_comm]
      -- ゴール: (s.r180.shatterOnFall (A.map r180)).gravity = (s.r180.shatterOnFall B).gravity
      -- where A = (floatingUnits s).flatMap positions, B = (floatingUnits s.r180).flatMap positions
      -- shatterOnFall_ext で .any メンバーシップ同値に帰着
      congr 1
      apply shatterOnFall_ext
      intro p
      -- (A.map r180).any (· == p) = A.any (· == p.r180) = B.any (· == p.r180.r180) = B.any (· == p)
      rw [Gravity.any_map_rotate180_beq,
          Gravity.falling_positions_any_rotate180,
          QuarterPos.rotate180_rotate180]

/-- cut の展開 -/
private theorem cut_eq (s : Shape) :
        s.cut = (s.shatterOnCut.eastHalf.settleAfterCut,
                 s.shatterOnCut.westHalf.settleAfterCut) := rfl

/-- 切断と 180° 回転の可換性。
    切断後に 180° 回転すると、東西が入れ替わる。
    layerCount ≤ 5 の場合に成立する（6 レイヤ以上では gravity に反例が存在） -/
theorem cut_rotate180_comm (s : Shape) (h : s.layerCount ≤ 5) :
        (s.cut.1.map rotate180, s.cut.2.map rotate180) =
        (s.rotate180.cut.2, s.rotate180.cut.1) := by
    have h_sc : s.shatterOnCut.layerCount ≤ 5 := by
        simp only [shatterOnCut, layerCount_clearPositions]; exact h
    have h_eh : s.shatterOnCut.eastHalf.layerCount ≤ 5 := by
        simp only [eastHalf, mapLayers, layerCount, List.length_map]; exact h_sc
    have h_wh : s.shatterOnCut.westHalf.layerCount ≤ 5 := by
        simp only [westHalf, mapLayers, layerCount, List.length_map]; exact h_sc
    simp only [cut_eq, Prod.mk.injEq]
    exact ⟨by rw [settleAfterCut_rotate180 _ h_eh, ← shatterOnCut_rotate180_comm, eastHalf_rotate180],
           by rw [settleAfterCut_rotate180 _ h_wh, ← shatterOnCut_rotate180_comm, westHalf_rotate180]⟩

/-- 同一シェイプをスワップすると、各出力は shatterOnCut 後の安定化・正規化結果と同じ -/
theorem swap_self (s : Shape) :
        s.swap s = (s.shatterOnCut.settleAfterCut.bind normalize,
                    s.shatterOnCut.settleAfterCut.bind normalize) := by
    simp only [swap]
    cases h : s.shatterOnCut.settleAfterCut <;>
        simp_all only [Option.bind_none, combineHalves_self, Option.bind_some]

/-- combineHalves と 180° 回転の可換性。東西が入れ替わる -/
theorem combineHalves_rotate180 (a b : Shape) :
        (combineHalves a b).rotate180 = combineHalves b.rotate180 a.rotate180 := by
    cases ha : a.layers with
    | nil => exact absurd ha a.layers_ne
    | cons a0 as =>
    cases hb : b.layers with
    | nil => exact absurd hb b.layers_ne
    | cons b0 bs =>
    apply Shape.ext
    simp only [combineHalves, zipLayersWithPad, rotate180, mapLayers, ha, hb,
               List.map_cons, zipLayersWithPad.go]
    congr 1
    exact zipLayersWithPad_go_rotate180 as bs

/-- 切断処理機と 180° 回転の可換性。
    切断処理機の結果を回転させると、元シェイプを回転してから切断した西側出力と等しい。
    halfDestroy(s) は cut(s) の東側出力であるため、回転で東西が入れ替わる。
    layerCount ≤ 5 の場合に成立する -/
theorem halfDestroy_rotate180 (s : Shape) (h : s.layerCount ≤ 5) :
        (s.halfDestroy).map rotate180 = s.rotate180.cut.2 := by
    rw [halfDestroy_eq_cut_east]
    exact (Prod.mk.inj (cut_rotate180_comm s h)).1

/-- スワップと 180° 回転の可換性（主ケース: 両入力の settleAfterCut が some の場合）。
    スワップ後に 180° 回転すると、出力の東西が入れ替わる。
    layerCount ≤ 5 の場合に成立する。

    注: settleAfterCut が none を返す辺縁ケース（シェイプが完全に空になる場合）では、
    swap の eastHalf 選択が r180 非等変であるため、この形の可換性は成立しない。
    ゲーム上、Swapper 入力は常に settled であり、settleAfterCut が none を返すことは
    実用上発生しない。 -/
theorem swap_rotate180_comm (s1 s2 : Shape)
        (h1 : s1.layerCount ≤ 5) (h2 : s2.layerCount ≤ 5)
        (hs1 : s1.shatterOnCut.settleAfterCut.isSome = true)
        (hs2 : s2.shatterOnCut.settleAfterCut.isSome = true) :
        ((s1.swap s2).1.map rotate180, (s1.swap s2).2.map rotate180) =
        ((s1.rotate180.swap s2.rotate180).2, (s1.rotate180.swap s2.rotate180).1) := by
    -- settleAfterCut の結果を取り出す
    have h1_sc : s1.shatterOnCut.layerCount ≤ 5 := by
        simp only [shatterOnCut, layerCount_clearPositions]; exact h1
    have h2_sc : s2.shatterOnCut.layerCount ≤ 5 := by
        simp only [shatterOnCut, layerCount_clearPositions]; exact h2
    -- Option の some を展開
    obtain ⟨settled1, hs1_eq⟩ := Option.isSome_iff_exists.mp hs1
    obtain ⟨settled2, hs2_eq⟩ := Option.isSome_iff_exists.mp hs2
    -- settleAfterCut と r180 の可換性から、回転版も some
    have hr1 : s1.rotate180.shatterOnCut.settleAfterCut = some (settled1.rotate180) := by
        have h := settleAfterCut_rotate180 s1.shatterOnCut h1_sc
        simp only [hs1_eq, Option.map] at h
        rw [shatterOnCut_rotate180_comm] at h; exact h.symm
    have hr2 : s2.rotate180.shatterOnCut.settleAfterCut = some (settled2.rotate180) := by
        have h := settleAfterCut_rotate180 s2.shatterOnCut h2_sc
        simp only [hs2_eq, Option.map] at h
        rw [shatterOnCut_rotate180_comm] at h; exact h.symm
    -- swap の各側を展開
    have hswap : s1.swap s2 = ((combineHalves settled1 settled2).normalize,
                                (combineHalves settled2 settled1).normalize) := by
        simp only [swap, hs1_eq, hs2_eq]
    have hswap' : s1.rotate180.swap s2.rotate180 =
                  ((combineHalves settled1.rotate180 settled2.rotate180).normalize,
                   (combineHalves settled2.rotate180 settled1.rotate180).normalize) := by
        simp only [swap, hr1, hr2]
    simp only [hswap, hswap', Prod.mk.injEq]
    exact ⟨by rw [normalize_rotate180, combineHalves_rotate180],
           by rw [normalize_rotate180, combineHalves_rotate180]⟩

-- ============================================================
-- IsSettled 保存定理
-- ============================================================

/-- settleAfterCut の出力は安定状態。layerCount ≤ 5 の場合に成立する。
    全パスが gravity を経由するため、gravity_IsSettled axiom に帰着する -/
theorem IsSettled_settleAfterCut (s : Shape) (s' : Shape)
        (h : s.settleAfterCut = some s') (h_lc : s.layerCount ≤ 5) :
        s'.IsSettled := by
    simp only [settleAfterCut] at h
    split at h
    · -- isEmpty = true: s.gravity
      exact gravity_IsSettled s s' h h_lc
    · -- isEmpty = false: afterShatter.gravity
      have h_sf : (s.shatterOnFall ((Gravity.floatingUnits s).flatMap
            Gravity.FallingUnit.positions)).layerCount ≤ 5 := by
        simp only [shatterOnFall, layerCount_clearPositions]; exact h_lc
      exact gravity_IsSettled _ s' h h_sf

/-- halfDestroy の出力は安定状態 -/
theorem IsSettled_halfDestroy (s : Shape) (s' : Shape)
        (h : s.halfDestroy = some s') (h_lc : s.layerCount ≤ 5) :
        s'.IsSettled := by
    simp only [halfDestroy] at h
    have h_sc : s.shatterOnCut.layerCount ≤ 5 := by
        simp only [shatterOnCut, layerCount_clearPositions]; exact h_lc
    have h_eh : s.shatterOnCut.eastHalf.layerCount ≤ 5 := by
        simp only [eastHalf, mapLayers, layerCount, List.length_map]; exact h_sc
    exact IsSettled_settleAfterCut _ s' h h_eh

/-- cut の東側出力は安定状態 -/
theorem IsSettled_cut_east (s : Shape) (s' : Shape)
        (h : s.cut.1 = some s') (h_lc : s.layerCount ≤ 5) :
        s'.IsSettled := by
    rw [← halfDestroy_eq_cut_east] at h
    exact IsSettled_halfDestroy s s' h h_lc

/-- cut の西側出力は安定状態 -/
theorem IsSettled_cut_west (s : Shape) (s' : Shape)
        (h : s.cut.2 = some s') (h_lc : s.layerCount ≤ 5) :
        s'.IsSettled := by
    simp only [cut] at h
    have h_sc : s.shatterOnCut.layerCount ≤ 5 := by
        simp only [shatterOnCut, layerCount_clearPositions]; exact h_lc
    have h_wh : s.shatterOnCut.westHalf.layerCount ≤ 5 := by
        simp only [westHalf, mapLayers, layerCount, List.length_map]; exact h_sc
    exact IsSettled_settleAfterCut _ s' h h_wh

-- TODO: IsSettled_swap は normalize の IsSettled 保存定理（IsSettled_normalize）の
-- 追加後に実装予定。swap の出力は combineHalves → normalize で生成されるため、
-- gravity_IsSettled axiom に直接帰着できない。

end Shape
