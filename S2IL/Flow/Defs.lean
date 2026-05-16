-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations

/-!
# S2IL.Flow.Defs

Layer C-1 Shape Processing Flow の最小核。

初期実装では任意グラフではなく、型付き combinator DSL として Flow を扱う。
`Flow.eval` は既存 Layer A/B の全関数 API を呼ぶ純粋な評価関数である。
-/

namespace S2IL

/-- 加工装置の接続を表す型付きフロー。 -/
inductive Flow : Type 0 → Type 0 → Type 1 where
  /-- 入力をそのまま出力するフロー。 -/
  | id {α : Type 0} : Flow α α
  /-- 既存の全関数 API を primitive node として埋め込む。 -/
  | prim {α β : Type 0} : (α → β) → Flow α β
  /-- 2 つのフローを順に合成する。 -/
  | comp {α β γ : Type 0} : Flow α β → Flow β γ → Flow α γ
  /-- ペアの第 1 成分だけにフローを適用する。 -/
  | first {α β γ : Type 0} : Flow α β → Flow (α × γ) (β × γ)
  /-- ペアの第 2 成分だけにフローを適用する。 -/
  | second {α β γ : Type 0} : Flow α β → Flow (γ × α) (γ × β)
  /-- 同じ入力を 2 つのフローへ渡し、結果をペアにする。 -/
  | fanout {α β γ : Type 0} : Flow α β → Flow α γ → Flow α (β × γ)

namespace Flow

variable {α β γ δ : Type 0}

/-- 型付きフローを純粋関数として評価する。 -/
def eval : {α β : Type 0} → Flow α β → α → β
  | _, _, Flow.id, input => input
  | _, _, Flow.prim operation, input => operation input
  | _, _, Flow.comp firstFlow secondFlow, input => eval secondFlow (eval firstFlow input)
  | _, _, Flow.first flow, input => (eval flow input.1, input.2)
  | _, _, Flow.second flow, input => (input.1, eval flow input.2)
  | _, _, Flow.fanout leftFlow rightFlow, input => (eval leftFlow input, eval rightFlow input)

/-- `id` の評価は入力そのもの。 -/
@[simp] theorem eval_id (input : α) :
    eval (Flow.id : Flow α α) input = input := rfl

/-- primitive node の評価は埋め込まれた関数の適用。 -/
@[simp] theorem eval_prim (operation : α → β) (input : α) :
    eval (Flow.prim operation) input = operation input := rfl

/-- 合成フローの評価は後段を前段の結果へ適用すること。 -/
@[simp] theorem eval_comp (firstFlow : Flow α β) (secondFlow : Flow β γ) (input : α) :
    eval (Flow.comp firstFlow secondFlow) input = eval secondFlow (eval firstFlow input) := rfl

/-- ペア第 1 成分フローの評価。 -/
@[simp] theorem eval_first (flow : Flow α β) (input : α × γ) :
    eval (Flow.first flow) input = (eval flow input.1, input.2) := rfl

/-- ペア第 2 成分フローの評価。 -/
@[simp] theorem eval_second (flow : Flow α β) (input : γ × α) :
    eval (Flow.second flow) input = (input.1, eval flow input.2) := rfl

/-- fanout フローの評価。 -/
@[simp] theorem eval_fanout (leftFlow : Flow α β) (rightFlow : Flow α γ) (input : α) :
    eval (Flow.fanout leftFlow rightFlow) input =
      (eval leftFlow input, eval rightFlow input) := rfl

/-- ペアの左右を入れ替えるフロー。 -/
def swap : Flow (α × β) (β × α) :=
  Flow.prim (fun input => (input.2, input.1))

/-- 1 つの入力を複製してペアにするフロー。 -/
def dup : Flow α (α × α) :=
  Flow.fanout Flow.id Flow.id

/-- ペアの両成分に別々のフローを適用する。 -/
def pairMap (firstFlow : Flow α β) (secondFlow : Flow γ δ) : Flow (α × γ) (β × δ) :=
  Flow.comp (Flow.first firstFlow) (Flow.second secondFlow)

/-- ペアの第 1 成分を捨て、第 2 成分だけを残すフロー。 -/
def dropFirst : Flow (α × β) β :=
  Flow.prim (fun input => input.2)

/-- ペアの第 2 成分を捨て、第 1 成分だけを残すフロー。 -/
def dropSecond : Flow (α × β) α :=
  Flow.prim (fun input => input.1)

/-- `swap` フローの評価。 -/
@[simp] theorem eval_swap (input : α × β) :
    eval (swap : Flow (α × β) (β × α)) input = (input.2, input.1) := rfl

/-- `dup` フローの評価。 -/
@[simp] theorem eval_dup (input : α) :
    eval (dup : Flow α (α × α)) input = (input, input) := rfl

/-- `pairMap` フローの評価。 -/
@[simp] theorem eval_pairMap (firstFlow : Flow α β) (secondFlow : Flow γ δ) (input : α × γ) :
    eval (pairMap firstFlow secondFlow) input =
      (eval firstFlow input.1, eval secondFlow input.2) := rfl

/-- `dropFirst` フローの評価。 -/
@[simp] theorem eval_dropFirst (input : α × β) :
  eval (dropFirst : Flow (α × β) β) input = input.2 := rfl

/-- `dropSecond` フローの評価。 -/
@[simp] theorem eval_dropSecond (input : α × β) :
  eval (dropSecond : Flow (α × β) α) input = input.1 := rfl

/-- 入力を無視して固定値を返すフロー。 -/
def constant (value : β) : Flow α β :=
  Flow.prim (fun _ => value)

/-- 左結合の product を右結合へ変換するフロー。 -/
def assocRight : Flow ((α × β) × γ) (α × (β × γ)) :=
  Flow.prim (fun input => (input.1.1, (input.1.2, input.2)))

/-- 右結合の product を左結合へ変換するフロー。 -/
def assocLeft : Flow (α × (β × γ)) ((α × β) × γ) :=
  Flow.prim (fun input => ((input.1, input.2.1), input.2.2))

/-- `constant` フローの評価。 -/
@[simp] theorem eval_constant (value : β) (input : α) :
    eval (constant value : Flow α β) input = value := rfl

/-- `assocRight` フローの評価。 -/
@[simp] theorem eval_assocRight (input : (α × β) × γ) :
    eval (assocRight : Flow ((α × β) × γ) (α × (β × γ))) input =
      (input.1.1, (input.1.2, input.2)) := rfl

/-- `assocLeft` フローの評価。 -/
@[simp] theorem eval_assocLeft (input : α × (β × γ)) :
    eval (assocLeft : Flow (α × (β × γ)) ((α × β) × γ)) input =
      ((input.1, input.2.1), input.2.2) := rfl

/-- 時計回り 90 度回転フロー。 -/
def rotateCW : Flow Shape Shape := Flow.prim Shape.rotateCW

/-- 180 度回転フロー。 -/
def rotate180 : Flow Shape Shape := Flow.prim Shape.rotate180

/-- 反時計回り 90 度回転フロー。 -/
def rotateCCW : Flow Shape Shape := Flow.prim Shape.rotateCCW

/-- Half-Destroyer フロー。現行実装では東半分を残す。 -/
def halfDestroy : Flow Shape Shape := Flow.prim Shape.halfDestroy

/-- Cutter フロー。東半分と西半分のペアを出力する。 -/
def cut : Flow Shape (Shape × Shape) := Flow.prim Shape.cut

/-- Trash フロー。Shape を削除し、出力を持たない。 -/
def trash : Flow Shape Unit := Flow.prim Shape.trash

/-- ペアの第 1 成分 Shape を Trash に送り、第 2 成分だけを残す。 -/
def trashFirstShape : Flow (Shape × α) α :=
  Flow.comp (Flow.first trash) Flow.dropFirst

/-- ペアの第 2 成分 Shape を Trash に送り、第 1 成分だけを残す。 -/
def trashSecondShape : Flow (α × Shape) α :=
  Flow.comp (Flow.second trash) Flow.dropSecond

/-- `trash` フローの評価。 -/
@[simp] theorem eval_trash (shape : Shape) : eval trash shape = () := rfl

/-- `trashFirstShape` フローの評価。 -/
@[simp] theorem eval_trashFirstShape (input : Shape × α) :
    eval (trashFirstShape : Flow (Shape × α) α) input = input.2 := rfl

/-- `trashSecondShape` フローの評価。 -/
@[simp] theorem eval_trashSecondShape (input : α × Shape) :
    eval (trashSecondShape : Flow (α × Shape) α) input = input.1 := rfl

/-- Swapper フロー。2 つの Shape の西半分を入れ替える。 -/
def swapShapes : Flow (Shape × Shape) (Shape × Shape) :=
  Flow.prim (fun input => Shape.swap input.1 input.2)

/-- 東半分・西半分を 1 つの Shape に合成するフロー。 -/
def combineHalves : Flow (Shape × Shape) Shape :=
  Flow.prim (fun input => Shape.combineHalves input.1 input.2)

/-- Color Mixer フロー。2 色を混合する。 -/
def mix : Flow (Color × Color) Color :=
  Flow.prim (fun input => S2IL.Operations.mix input.1 input.2)

/-- Shape と Color を入力として Painter を適用するフロー。 -/
def paintWith : Flow (Shape × Color) Shape :=
  Flow.prim (fun input => Shape.paint input.1 input.2)

/-- Shape と Color を入力として Crystal Generator を適用するフロー。 -/
def crystallizeWith : Flow (Shape × Color) Shape :=
  Flow.prim (fun input => Shape.crystallize input.1 input.2)

/-- 色を固定した Painter フロー。 -/
def paint (color : Color) : Flow Shape Shape :=
  Flow.prim (fun shape => Shape.paint shape color)

/-- 色を固定した Crystal Generator フロー。 -/
def crystallize (color : Color) : Flow Shape Shape :=
  Flow.prim (fun shape => Shape.crystallize shape color)

/-- Gravity フロー。Layer B の total function をそのまま呼ぶ。 -/
def gravity : Flow Shape Shape := Flow.prim Shape.gravity

noncomputable section

/-- `GameConfig` を固定した Stacker フロー。 -/
def stack (config : GameConfig) : Flow (Shape × Shape) Shape :=
  Flow.prim (fun input => Shape.stack input.1 input.2 config)

/-- `GameConfig` を固定した Pin Pusher フロー。 -/
def pinPush (config : GameConfig) : Flow Shape Shape :=
  Flow.prim (fun shape => Shape.pinPush shape config)

end

end Flow

end S2IL
