-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.QuarterPos
import S2IL.Behavior.Rotate
import Batteries

/-!
# 回転等変性の共通補題

`QuarterPos.getDir`・`QuarterPos.setQuarter`・`Shape.clearPositions` 等の
シェイプ操作が回転操作に対して等変であることを示す補題群。

`LayerPerm` 構造体で rotate180 / rotateCW の共通構造を抽象化し、
各等変性を一度だけ証明して両方に適用する。
-/

-- ============================================================
-- LayerPerm: レイヤ単位の回転操作の抽象
-- ============================================================

/-- レイヤ単位の回転操作の抽象パラメータ。
    rotate180 と rotateCW の等変性証明を一度だけ書くための構造体。
    - `onDir`/`onLayer`/`onQPos`: 各レベルの回転関数
    - `onQPosInv`: QuarterPos の逆回転（rotate180 では自身、rotateCW では rotateCCW）
    - 公理: レイヤ保存、方角整合、getDir/setDir の可換性、逆変換のキャンセル -/
structure LayerPerm where
    /-- Direction の変換 -/
    onDir : Direction → Direction
    /-- Layer の変換 -/
    onLayer : Layer → Layer
    /-- QuarterPos の変換 -/
    onQPos : QuarterPos → QuarterPos
    /-- QuarterPos の逆変換 -/
    onQPosInv : QuarterPos → QuarterPos
    /-- 変換はレイヤインデックスを保存する -/
    qpos_layer : ∀ p : QuarterPos, (onQPos p).layer = p.layer
    /-- 変換は方角に対応する -/
    qpos_dir : ∀ p : QuarterPos, (onQPos p).dir = onDir p.dir
    /-- getDir と変換の可換性 -/
    getDir_comm : ∀ (l : Layer) (d : Direction),
        QuarterPos.getDir (onLayer l) (onDir d) = QuarterPos.getDir l d
    /-- setDir (.empty) と変換の可換性 -/
    setDir_empty_comm : ∀ (l : Layer) (d : Direction),
        (QuarterPos.setDir l d .empty |> onLayer) =
        QuarterPos.setDir (onLayer l) (onDir d) .empty
    /-- 変換と逆変換の右キャンセル: σ(σ⁻¹(p)) = p -/
    cancel_inv : ∀ p : QuarterPos, onQPos (onQPosInv p) = p
    /-- Direction の BEq は変換で保存される -/
    dir_beq : ∀ d1 d2 : Direction, (onDir d1 == onDir d2) = (d1 == d2)

-- ============================================================
-- rotate180 / rotateCW のインスタンス
-- ============================================================

/-- rotate180 の LayerPerm インスタンス（逆変換は自身 = involution） -/
abbrev LayerPerm.rotate180 : LayerPerm where
    onDir := Direction.rotate180
    onLayer := Layer.rotate180
    onQPos := QuarterPos.rotate180
    onQPosInv := QuarterPos.rotate180
    qpos_layer := fun _ => rfl
    qpos_dir := fun _ => rfl
    getDir_comm := fun _ d => by cases d <;> rfl
    setDir_empty_comm := fun _ d => by cases d <;> rfl
    cancel_inv := QuarterPos.rotate180_rotate180
    dir_beq := fun d1 d2 => by cases d1 <;> cases d2 <;> rfl

/-- rotateCW の LayerPerm インスタンス（逆変換は rotateCCW） -/
abbrev LayerPerm.rotateCW : LayerPerm where
    onDir := Direction.rotateCW
    onLayer := Layer.rotateCW
    onQPos := QuarterPos.rotateCW
    onQPosInv := QuarterPos.rotateCCW
    qpos_layer := fun _ => rfl
    qpos_dir := fun _ => rfl
    getDir_comm := fun _ d => by cases d <;> rfl
    setDir_empty_comm := fun _ d => by cases d <;> rfl
    cancel_inv := QuarterPos.rotateCCW_rotateCW
    dir_beq := fun d1 d2 => by cases d1 <;> cases d2 <;> rfl

-- ============================================================
-- BEq 保存の汎用補題（BFS 等変性の基盤）
-- ============================================================

namespace LayerPerm

/-- QuarterPos の BEq は変換で保存される -/
theorem quarterPos_beq (σ : LayerPerm) (p q : QuarterPos) :
        (σ.onQPos p == σ.onQPos q) = (p == q) := by
    show ((σ.onQPos p).layer == (σ.onQPos q).layer && (σ.onQPos p).dir == (σ.onQPos q).dir) =
         (p.layer == q.layer && p.dir == q.dir)
    simp only [σ.qpos_layer, σ.qpos_dir, σ.dir_beq]

/-- List.any は変換のマッピングで保存される -/
theorem list_any_map (σ : LayerPerm) (l : List QuarterPos) (p : QuarterPos) :
        (l.map σ.onQPos).any (· == σ.onQPos p) = l.any (· == p) := by
    rw [List.any_map]
    congr 1; funext x
    exact σ.quarterPos_beq x p

/-- List.any の cons と変換の関係 -/
theorem list_any_cons (σ : LayerPerm) (x : QuarterPos)
        (l : List QuarterPos) (p : QuarterPos) :
        ((σ.onQPos x :: l.map σ.onQPos).any (· == σ.onQPos p)) =
        ((x :: l).any (· == p)) := by
    simp only [List.any, σ.quarterPos_beq, σ.list_any_map]

/-- Direction の変換は単射 -/
theorem onDir_injective (σ : LayerPerm) {d1 d2 : Direction}
        (h : σ.onDir d1 = σ.onDir d2) : d1 = d2 := by
    have h1 : (σ.onDir d1 == σ.onDir d2) = true := beq_iff_eq.mpr h
    rw [σ.dir_beq] at h1
    exact beq_iff_eq.mp h1

end LayerPerm

-- ============================================================
-- QuarterPos / Layer レベルの具象補題
-- （下流ファイルが simp only [...] で直接参照するため維持）
-- ============================================================

namespace QuarterPos

/-- getDir と rotate180 の可換性 -/
@[aesop norm simp] theorem getDir_rotate180 (l : Layer) (d : Direction) :
        getDir (l.rotate180) (d.rotate180) = getDir l d :=
    LayerPerm.rotate180.getDir_comm l d

/-- getDir と rotateCW の可換性 -/
@[aesop norm simp] theorem getDir_rotateCW (l : Layer) (d : Direction) :
        getDir (l.rotateCW) (d.rotateCW) = getDir l d :=
    LayerPerm.rotateCW.getDir_comm l d

/-- setDir (.empty) と rotate180 の可換性 -/
@[aesop norm simp] theorem setDir_rotate180_empty (l : Layer) (d : Direction) :
        (setDir l d .empty).rotate180 =
        setDir (l.rotate180) (d.rotate180) .empty :=
    LayerPerm.rotate180.setDir_empty_comm l d

/-- setDir (.empty) と rotateCW の可換性 -/
@[aesop norm simp] theorem setDir_rotateCW_empty (l : Layer) (d : Direction) :
        (setDir l d .empty).rotateCW =
        setDir (l.rotateCW) (d.rotateCW) .empty :=
    LayerPerm.rotateCW.setDir_empty_comm l d

end QuarterPos

-- ============================================================
-- Shape.layers の変換
-- ============================================================

namespace Shape

/-- Shape.layers と rotate180 の関係 -/
@[aesop norm simp] theorem layers_rotate180 (s : Shape) :
        s.rotate180.layers = s.layers.map Layer.rotate180 := by
    simp only [Shape.rotate180, Shape.mapLayers]

/-- Shape.layers と rotateCW の関係 -/
@[aesop norm simp] theorem layers_rotateCW (s : Shape) :
        s.rotateCW.layers = s.layers.map Layer.rotateCW := by
    simp only [Shape.rotateCW, Shape.mapLayers]

end Shape

-- ============================================================
-- QuarterPos / Shape 複合の汎用等変性
-- ============================================================

namespace QuarterPos

/-- getQuarter と LayerPerm の可換性（汎用版） -/
theorem getQuarter_perm (σ : LayerPerm) (s : Shape) (p : QuarterPos) :
        (σ.onQPos p).getQuarter (s.mapLayers σ.onLayer) = p.getQuarter s := by
    simp only [getQuarter, σ.qpos_layer, Shape.mapLayers]
    rw [List.getElem?_map]
    cases s.layers[p.layer]? with
    | none => rfl
    | some l => simp only [Option.map_some, σ.qpos_dir, σ.getDir_comm]

/-- getQuarter と rotate180 の可換性 -/
@[aesop norm simp] theorem getQuarter_rotate180 (s : Shape) (pos : QuarterPos) :
        pos.rotate180.getQuarter s.rotate180 = pos.getQuarter s :=
    getQuarter_perm .rotate180 s pos

/-- getQuarter と rotateCW の可換性 -/
@[aesop norm simp] theorem getQuarter_rotateCW (s : Shape) (pos : QuarterPos) :
        pos.rotateCW.getQuarter s.rotateCW = pos.getQuarter s :=
    getQuarter_perm .rotateCW s pos

/-- getQuarter の逆方向（汎用版）:
    p から変換後のシェイプへのアクセス = 逆変換(p) から元のシェイプへのアクセス -/
theorem getQuarter_perm_inv (σ : LayerPerm) (s : Shape) (p : QuarterPos) :
        p.getQuarter (s.mapLayers σ.onLayer) = (σ.onQPosInv p).getQuarter s := by
    have h := getQuarter_perm σ s (σ.onQPosInv p)
    rw [σ.cancel_inv] at h; exact h

/-- getQuarter の rotate180 逆方向 -/
@[aesop norm simp] theorem getQuarter_rotate180_inv (s : Shape) (p : QuarterPos) :
        p.getQuarter s.rotate180 = p.rotate180.getQuarter s :=
    getQuarter_perm_inv .rotate180 s p

/-- getQuarter の rotateCW 逆方向 -/
@[aesop norm simp] theorem getQuarter_rotateCW_inv (s : Shape) (p : QuarterPos) :
        p.getQuarter s.rotateCW = p.rotateCCW.getQuarter s :=
    getQuarter_perm_inv .rotateCW s p

-- ============================================================
-- setQuarter の等変性
-- ============================================================

/-- setQuarter のレイヤが存在する場合、.layers は List.set の結果に等しい -/
theorem setQuarter_layers_eq (s : Shape) (pos : QuarterPos) (q : Quarter) (l : Layer)
        (hl : s.layers[pos.layer]? = some l) :
        (pos.setQuarter s q).layers = s.layers.set pos.layer (setDir l pos.dir q) := by
    simp only [setQuarter, hl]
    split
    · rename_i h
      exact absurd h (by simp only [List.set_eq_nil_iff]; exact s.layers_ne)
    · rfl

/-- setQuarter (.empty) と LayerPerm の可換性（汎用版） -/
theorem setQuarter_perm_empty (σ : LayerPerm) (s : Shape) (pos : QuarterPos) :
        (pos.setQuarter s .empty).mapLayers σ.onLayer =
        (σ.onQPos pos).setQuarter (s.mapLayers σ.onLayer) .empty := by
    cases hl : s.layers[pos.layer]? with
    | none =>
        have h_rhs : (s.layers.map σ.onLayer)[pos.layer]? = none := by
            rw [List.getElem?_map, hl]; rfl
        simp only [setQuarter, hl, σ.qpos_layer, Shape.mapLayers, h_rhs]
    | some l =>
        have hl_r : (s.layers.map σ.onLayer)[pos.layer]? = some (σ.onLayer l) := by
            rw [List.getElem?_map, hl]; rfl
        apply Shape.ext
        show (pos.setQuarter s .empty).layers.map σ.onLayer =
             ((σ.onQPos pos).setQuarter (s.mapLayers σ.onLayer) .empty).layers
        rw [setQuarter_layers_eq s pos .empty l hl]
        rw [setQuarter_layers_eq (s.mapLayers σ.onLayer) (σ.onQPos pos) .empty (σ.onLayer l)
                (show (s.mapLayers σ.onLayer).layers[(σ.onQPos pos).layer]? = some (σ.onLayer l) by
                    simp only [Shape.mapLayers, σ.qpos_layer]; exact hl_r)]
        simp only [σ.qpos_dir, σ.qpos_layer, List.map_set, σ.setDir_empty_comm, Shape.mapLayers]

/-- setQuarter (.empty) と rotate180 の可換性 -/
@[aesop norm simp] theorem setQuarter_rotate180_empty (s : Shape) (pos : QuarterPos) :
        (pos.setQuarter s .empty).rotate180 = (pos.rotate180).setQuarter (s.rotate180) .empty :=
    setQuarter_perm_empty .rotate180 s pos

/-- setQuarter (.empty) と rotateCW の可換性 -/
@[aesop norm simp] theorem setQuarter_rotateCW_empty (s : Shape) (pos : QuarterPos) :
        (pos.setQuarter s .empty).rotateCW = (pos.rotateCW).setQuarter (s.rotateCW) .empty :=
    setQuarter_perm_empty .rotateCW s pos

end QuarterPos

-- ============================================================
-- clearPositions の等変性
-- ============================================================

namespace Shape

/-- clearPositions と LayerPerm の可換性（汎用版） -/
theorem clearPositions_perm (σ : LayerPerm) (s : Shape) (ps : List QuarterPos) :
        (s.clearPositions ps).mapLayers σ.onLayer =
        (s.mapLayers σ.onLayer).clearPositions (ps.map σ.onQPos) := by
    induction ps generalizing s with
    | nil => rfl
    | cons p rest ih =>
        show (clearPositions (p.setQuarter s .empty) rest).mapLayers σ.onLayer =
            clearPositions ((σ.onQPos p).setQuarter (s.mapLayers σ.onLayer) .empty)
                (rest.map σ.onQPos)
        rw [ih, QuarterPos.setQuarter_perm_empty]

/-- clearPositions と rotate180 の可換性 -/
@[aesop norm simp] theorem clearPositions_rotate180 (s : Shape) (ps : List QuarterPos) :
        (s.clearPositions ps).rotate180 =
        (s.rotate180).clearPositions (ps.map QuarterPos.rotate180) :=
    clearPositions_perm .rotate180 s ps

/-- clearPositions と rotateCW の可換性 -/
@[aesop norm simp] theorem clearPositions_rotateCW (s : Shape) (ps : List QuarterPos) :
        (s.clearPositions ps).rotateCW =
        (s.rotateCW).clearPositions (ps.map QuarterPos.rotateCW) :=
    clearPositions_perm .rotateCW s ps

end Shape
