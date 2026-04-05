-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.QuarterPos
import S2IL.Behavior.Rotate
import Batteries

/-!
# Rotate180 等変性の共通補題

`QuarterPos.getDir`・`QuarterPos.setQuarter`・`Shape.clearPositions` 等の
シェイプ操作が 180° 回転に対して等変であることを示す補題群。

これらの補題は `Shatter.lean` と `Gravity.lean` の双方で利用される
共通基盤であり、重複を除去するためにこのモジュールに集約した。
-/

-- ============================================================
-- QuarterPos / Layer レベルの rotate180 補題
-- ============================================================

namespace QuarterPos

/-- getDir と rotate180 の可換性: 回転後の方角で取得 = 回転前の方角で取得 -/
theorem getDir_rotate180 (l : Layer) (d : Direction) :
        getDir (l.rotate180) (d.rotate180) = getDir l d := by
    cases d <;> rfl

/-- setDir (.empty) と rotate180 の可換性 -/
theorem setDir_rotate180_empty (l : Layer) (d : Direction) :
        (setDir l d .empty).rotate180 =
        setDir (l.rotate180) (d.rotate180) .empty := by
    cases d <;> rfl

end QuarterPos

-- ============================================================
-- Shape レベルの rotate180 補題
-- ============================================================

namespace Shape

/-- Shape.layers と rotate180 の関係 -/
theorem layers_rotate180 (s : Shape) :
        s.rotate180.layers = s.layers.map Layer.rotate180 := by
    simp only [Shape.rotate180, Shape.mapLayers]

end Shape

-- ============================================================
-- QuarterPos / Shape 複合補題
-- ============================================================

namespace QuarterPos

/-- getQuarter と rotate180 の可換性 -/
theorem getQuarter_rotate180 (s : Shape) (pos : QuarterPos) :
        pos.rotate180.getQuarter s.rotate180 = pos.getQuarter s := by
    simp only [getQuarter, rotate180, Shape.layers_rotate180]
    rw [List.getElem?_map]
    cases s.layers[pos.layer]? with
    | none => rfl
    | some l => simp only [Option.map_some, getDir_rotate180]

/-- getQuarter の rotate180 逆方向: p から s.r180 へのアクセス = p.r180 から s へのアクセス -/
theorem getQuarter_rotate180_inv (s : Shape) (p : QuarterPos) :
        p.getQuarter s.rotate180 = p.rotate180.getQuarter s := by
    have h := getQuarter_rotate180 s p.rotate180
    rw [QuarterPos.rotate180_rotate180] at h
    exact h

-- ------------------------------------------------------------
-- setQuarter / clearPositions の rotate180 等変性
-- ------------------------------------------------------------

/-- List.set は非空リストを空にしない -/
private theorem set_ne_nil_of_ne_nil {α : Type} {l : List α} (h : l ≠ []) (i : Nat) (a : α) :
        l.set i a ≠ [] := by
    cases l with
    | nil => exact absurd rfl h
    | cons x xs => cases i <;> simp only [List.set, ne_eq, reduceCtorEq, not_false_eq_true]

/-- setQuarter のレイヤが存在する場合、.layers は List.set の結果に等しい -/
theorem setQuarter_layers_eq (s : Shape) (pos : QuarterPos) (q : Quarter) (l : Layer)
        (hl : s.layers[pos.layer]? = some l) :
        (pos.setQuarter s q).layers = s.layers.set pos.layer (setDir l pos.dir q) := by
    simp only [setQuarter, hl]
    -- 内部 match の分岐を split で解決する
    split
    · -- nil case: s.layers.set ... = [] は s.layers ≠ [] と矛盾
      rename_i h
      exact absurd h (set_ne_nil_of_ne_nil s.layers_ne pos.layer _)
    · -- cons case: .layers = newLayers
      rfl

/-- setQuarter (.empty) と rotate180 の可換性 -/
theorem setQuarter_rotate180_empty (s : Shape) (pos : QuarterPos) :
        (pos.setQuarter s .empty).rotate180 = (pos.rotate180).setQuarter (s.rotate180) .empty := by
    cases hl : s.layers[pos.layer]? with
    | none =>
        -- 範囲外: 両辺とも元のシェイプを返す
        simp only [setQuarter, rotate180, Shape.layers_rotate180,
                    List.getElem?_map, hl, Option.map_none]
    | some l =>
        -- .layers を抽出して等式を証明する
        have hl_r : (s.layers.map Layer.rotate180)[pos.layer]? = some (l.rotate180) := by
            rw [List.getElem?_map, hl]; rfl
        -- layers の等式に帰着
        apply Shape.ext
        show (pos.setQuarter s .empty).layers.map Layer.rotate180 =
             ((pos.rotate180).setQuarter s.rotate180 .empty).layers
        rw [setQuarter_layers_eq s pos .empty l hl]
        rw [setQuarter_layers_eq s.rotate180 pos.rotate180 .empty (l.rotate180)
                (show s.rotate180.layers[pos.rotate180.layer]? = some (l.rotate180) by
                    simp only [Shape.rotate180, Shape.mapLayers, rotate180]
                    exact hl_r)]
        simp only [rotate180, List.map_set, setDir_rotate180_empty,
                    Shape.rotate180, Shape.mapLayers]

end QuarterPos

namespace Shape

/-- clearPositions と rotate180 の可換性 -/
theorem clearPositions_rotate180 (s : Shape) (ps : List QuarterPos) :
        (s.clearPositions ps).rotate180 =
        (s.rotate180).clearPositions (ps.map QuarterPos.rotate180) := by
    induction ps generalizing s with
    | nil => rfl
    | cons p rest ih =>
        show (clearPositions (p.setQuarter s .empty) rest).rotate180 =
            clearPositions ((p.rotate180).setQuarter (s.rotate180) .empty)
                (rest.map QuarterPos.rotate180)
        rw [ih, QuarterPos.setQuarter_rotate180_empty]

end Shape
