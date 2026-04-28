-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

/-!
# Test.Operations.Settled

安定状態 (B-3) の構造判定 `IsSettled` のテスト。

`IsSettled` は `Relation.ReflTransGen` ベースの述語（Prop 層）で
`Classical.decPred` 経由で `noncomputable` の `isSettled : Bool` に
ブリッジされる。`#guard isSettled ...` は実行できないため、
本ファイルでは公開 API の型と等変性 / iff 橋渡しを `example` で確認する。

具体的なシェイプに対する settled 判定は `Shape.gravity` の脱 axiom
（Phase D-10）後に Behavior レベルで追加する。
-/

import S2IL.Operations

open S2IL

namespace Test.Operations.Settled

-- ============================================================
-- 公開 API の型
-- ============================================================

example : Shape → QuarterPos → QuarterPos → Prop := IsContact
example : Shape → QuarterPos → QuarterPos → Prop := IsUpwardGroundingContact
example : Shape → QuarterPos → QuarterPos → Prop := IsGroundingEdge
example : Shape → QuarterPos → Prop := IsGrounded
example : Shape → Prop := IsSettled

-- isSettled は noncomputable Bool
example (s : Shape) : Bool := isSettled s

-- 橋渡し
example (s : Shape) : isSettled s = true ↔ IsSettled s :=
  isSettled.iff s

-- ============================================================
-- IsContact: 同一象限同士は contact ではない（layer 差 = 0、方角隣接でもない）
-- ============================================================

private def L_full : Layer :=
  Layer.mk (.colored .circle .red) (.colored .star .green)
           (.colored .windmill .blue) (.crystal .yellow)

-- 同一 QuarterPos 同士は contact でない（垂直は layer 差 1、水平は方角異なり）
example : ¬ IsContact [L_full] ((0 : Nat), Direction.ne) ((0 : Nat), Direction.ne) := by
  intro h
  rcases h with ⟨_, h_ud, _⟩ | ⟨_, h_adj, _⟩
  · -- 0+1=0 ∨ 0+1=0 はどちらも矛盾
    rcases h_ud with h | h <;> omega
  · -- ne ne は隣接でない
    simp [Direction.isAdjacent, Direction.ne] at h_adj

-- ============================================================
-- 0 層シェイプは IsSettled: 有効位置が存在しない
-- ============================================================

example : IsSettled ([] : Shape) := by
  intro p hp _
  rw [QuarterPos.mem_allValid] at hp
  simp [Shape.layerCount] at hp

-- ============================================================
-- 等変性: CW / 180° / CCW は IsSettled を保存
-- ============================================================

example {s : Shape} (h : IsSettled s) : IsSettled s.rotateCW :=
  IsSettled.rotateCW h

example {s : Shape} (h : IsSettled s) : IsSettled s.rotate180 :=
  IsSettled.rotate180 h

example {s : Shape} (h : IsSettled s) : IsSettled s.rotateCCW :=
  IsSettled.rotateCCW h

-- 系: 0 層は CW しても settled
example : IsSettled (([] : Shape).rotateCW) :=
  IsSettled.rotateCW (by intro p hp _; rw [QuarterPos.mem_allValid] at hp; simp [Shape.layerCount] at hp)

end Test.Operations.Settled
