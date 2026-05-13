-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.Types.Direction
import S2IL.Shape.Types.Quarter

/-!
# S2IL.Shape.Types.Layer

`Layer := Fin 4 → Quarter` とレイヤ基本操作。
-/

namespace S2IL

/-- 4 象限の組（1 レイヤ）。`Direction` で関数アクセスする。 -/
abbrev Layer := Fin 4 → Quarter

namespace Layer

/-- 4 方角を指定してレイヤを構成。 -/
def mk (ne se sw nw : Quarter) : Layer := fun d =>
  match d.val with
  | 0 => ne
  | 1 => se
  | 2 => sw
  | _ => nw

@[simp] theorem mk_apply_zero (ne se sw nw : Quarter) : mk ne se sw nw 0 = ne := rfl
@[simp] theorem mk_apply_one  (ne se sw nw : Quarter) : mk ne se sw nw 1 = se := rfl
@[simp] theorem mk_apply_two  (ne se sw nw : Quarter) : mk ne se sw nw 2 = sw := rfl
@[simp] theorem mk_apply_three (ne se sw nw : Quarter) : mk ne se sw nw 3 = nw := rfl

/-- レイヤを 4 象限への分解として復元する。 -/
@[simp] theorem mk_eta (l : Layer) : mk (l 0) (l 1) (l 2) (l 3) = l := by
  funext ⟨d, hd⟩
  match d, hd with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

/-- 全象限が空のレイヤ。 -/
def empty : Layer := fun _ => Quarter.empty

/-- 全象限が空か。 -/
def isEmpty (l : Layer) : Bool :=
  (l 0).isEmpty && (l 1).isEmpty && (l 2).isEmpty && (l 3).isEmpty

/-- 時計回り 90° 回転（index を -1 シフト）。 -/
def rotateCW (l : Layer) : Layer := fun d => l (d - 1)

/-- 指定方角の象限を取得。 -/
def getDir (l : Layer) (d : Direction) : Quarter := l d

/-- 指定方角の象限を設定。 -/
def setDir (l : Layer) (d : Direction) (q : Quarter) : Layer :=
  fun d' => if d' = d then q else l d'

end Layer

end S2IL