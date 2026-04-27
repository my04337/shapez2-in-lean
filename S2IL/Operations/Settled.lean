-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel
import Mathlib.Logic.Relation

/-!
# S2IL.Operations.Settled

Settled (安定状態、B-3) の構造的判定（Phase D 完了形）。

## 数学的設計

`docs/shapez2/falling.md §4.2` に従い、接地 (`IsGrounded`) を Mathlib
`Relation.ReflTransGen` ベースで定義する:

* **接地接触 (`IsContact`)**: 上下隣接（同方角・両非空）または同層隣接（隣接方角・
  両非空・両非ピン）
* **上方向接地接触 (`IsUpwardGroundingContact`)**: contact ∧ `a.layer + 1 = b.layer`
* **接地エッジ (`IsGroundingEdge`)**: 上方向接地接触 ∨ 構造結合 (`IsBonded`)
* **接地 (`IsGrounded s p`)**: layer 0 の非空象限 `p₀` から接地エッジで `p` に到達可能
* **安定 (`IsSettled s`)**: 全有効非空象限が接地している

ピンは `canFormBond = false` のため `IsBonded` を介した下方向伝播を持たないが、
垂直方向の上方向接地接触は持つ（`IsContact` 側に空・ピン制約は課さない）。
水平方向では両非ピンの追加制約が課される。

## 公開 API

- Prop 層: `IsContact`, `IsUpwardGroundingContact`, `IsGroundingEdge`,
  `IsGrounded`, `IsSettled`
- Bool 層: `isSettled := decide IsSettled` (noncomputable)
- 等変性: `IsSettled.rotateCW` (CW)、`rotate180` / `rotateCCW` は 1 行系

## Prop/Bool 二層規約 (§1.11)

`IsSettled` は `Relation.ReflTransGen` 経由で定義されるため決定可能性は
`Classical.decPred` を使う（`isSettled : Bool` は `noncomputable`）。
有限ホップ性は将来の Operations/Internal で計算的に取り出せる。

## 単一チェーン原則

CW 等変性のみを直接証明、180° / CCW は 1 行系。
-/

namespace S2IL

open Relation

-- ============================================================
-- 接地接触の primitive
-- ============================================================

/-- 接地接触: 同方角の上下隣接（両非空）または同層隣接方角（両非空・両非ピン）。 -/
def IsContact (s : Shape) (a b : QuarterPos) : Prop :=
  -- 垂直方向: 同方角 + |layer 差| = 1 + 両非空（ピン許容）
  (a.2 = b.2 ∧ (a.1 + 1 = b.1 ∨ b.1 + 1 = a.1) ∧
    ¬ (QuarterPos.getQuarter s a).isEmpty ∧ ¬ (QuarterPos.getQuarter s b).isEmpty)
  ∨
  -- 水平方向: 同層 + 隣接方角 + 両非空 + 両非ピン
  (a.1 = b.1 ∧ Direction.isAdjacent a.2 b.2 = true ∧
    ¬ (QuarterPos.getQuarter s a).isEmpty ∧ ¬ (QuarterPos.getQuarter s b).isEmpty ∧
    QuarterPos.getQuarter s a ≠ Quarter.pin ∧ QuarterPos.getQuarter s b ≠ Quarter.pin)

/-- 上方向接地接触: 接触かつ `a.layer + 1 = b.layer` または同層（接触は方向対称）。 -/
def IsUpwardGroundingContact (s : Shape) (a b : QuarterPos) : Prop :=
  IsContact s a b ∧ a.1 ≤ b.1

/-- 接地エッジ: 上方向接地接触 または 構造結合。 -/
def IsGroundingEdge (s : Shape) (a b : QuarterPos) : Prop :=
  IsUpwardGroundingContact s a b ∨ IsBonded s a b

/-- 接地: layer 0 の非空象限から接地エッジで到達可能。 -/
def IsGrounded (s : Shape) (p : QuarterPos) : Prop :=
  ∃ p₀ : QuarterPos, p₀.1 = 0 ∧ ¬ (QuarterPos.getQuarter s p₀).isEmpty ∧
    ReflTransGen (IsGroundingEdge s) p₀ p

/-- 安定: 全有効非空象限が接地している。 -/
def IsSettled (s : Shape) : Prop :=
  ∀ p : QuarterPos, p ∈ QuarterPos.allValid s →
    ¬ (QuarterPos.getQuarter s p).isEmpty → IsGrounded s p

-- ============================================================
-- 決定可能性と Bool 層
-- ============================================================

noncomputable instance instDecidableIsSettled : DecidablePred IsSettled :=
  Classical.decPred _

/-- `IsSettled` の Bool 版（派生）。 -/
noncomputable def isSettled (s : Shape) : Bool := decide (IsSettled s)

/-- 橋渡し。 -/
theorem isSettled.iff (s : Shape) : isSettled s = true ↔ IsSettled s := by
  simp [isSettled]

-- ============================================================
-- CW 等変性: contact / grounding edge / grounded / settled
-- ============================================================

private theorem IsContact.rotateCW (s : Shape) (a b : QuarterPos) :
    IsContact s.rotateCW a.rotateCW b.rotateCW ↔ IsContact s a b := by
  unfold IsContact
  simp only [QuarterPos.rotateCW_fst, QuarterPos.rotateCW_snd]
  rw [QuarterPos.getQuarter_rotateCW, QuarterPos.getQuarter_rotateCW]
  -- 方角の +1 同士の等式を相殺
  have hd : a.2 + 1 = b.2 + 1 ↔ a.2 = b.2 := by
    constructor
    · intro h
      have h' : a.2 + 1 - 1 = b.2 + 1 - 1 := by rw [h]
      have e1 : a.2 + 1 - 1 = a.2 := by ext; simp [Fin.sub_def, Fin.add_def]; omega
      have e2 : b.2 + 1 - 1 = b.2 := by ext; simp [Fin.sub_def, Fin.add_def]; omega
      rw [e1, e2] at h'; exact h'
    · intro h; rw [h]
  rw [hd, Direction.isAdjacent_rotateCW]

private theorem IsUpwardGroundingContact.rotateCW (s : Shape) (a b : QuarterPos) :
    IsUpwardGroundingContact s.rotateCW a.rotateCW b.rotateCW ↔
      IsUpwardGroundingContact s a b := by
  unfold IsUpwardGroundingContact
  simp only [QuarterPos.rotateCW_fst, IsContact.rotateCW]

private theorem IsGroundingEdge.rotateCW (s : Shape) (a b : QuarterPos) :
    IsGroundingEdge s.rotateCW a.rotateCW b.rotateCW ↔ IsGroundingEdge s a b := by
  unfold IsGroundingEdge
  rw [IsUpwardGroundingContact.rotateCW, IsBonded.rotateCW]

private theorem groundingEdge_reflTransGen_rotateCW (s : Shape) (p q : QuarterPos) :
    ReflTransGen (IsGroundingEdge s.rotateCW) p.rotateCW q.rotateCW ↔
      ReflTransGen (IsGroundingEdge s) p q := by
  constructor
  · -- backward direction: rotateCCW で持ち上げ、相殺
    intro h
    have hlift :
        ReflTransGen (IsGroundingEdge s) p.rotateCW.rotateCCW q.rotateCW.rotateCCW :=
      h.lift QuarterPos.rotateCCW (fun a b hab => by
        have key : IsGroundingEdge s.rotateCW a.rotateCCW.rotateCW b.rotateCCW.rotateCW
                    ↔ IsGroundingEdge s a.rotateCCW b.rotateCCW :=
          IsGroundingEdge.rotateCW s a.rotateCCW b.rotateCCW
        exact key.mp (by simpa [QuarterPos.rotateCW_rotateCCW] using hab))
    simpa [QuarterPos.rotateCCW_rotateCW] using hlift
  · intro h
    exact h.lift QuarterPos.rotateCW (fun a b hab =>
      (IsGroundingEdge.rotateCW s a b).mpr hab)

namespace IsGrounded

theorem rotateCW {s : Shape} {p : QuarterPos} (h : IsGrounded s p) :
    IsGrounded s.rotateCW p.rotateCW := by
  obtain ⟨p₀, hl, hne, hpath⟩ := h
  refine ⟨p₀.rotateCW, ?_, ?_, ?_⟩
  · simp [QuarterPos.rotateCW_fst, hl]
  · rw [QuarterPos.getQuarter_rotateCW]; exact hne
  · -- ReflTransGen.lift を使う
    exact (groundingEdge_reflTransGen_rotateCW s p₀ p).mpr hpath

end IsGrounded

namespace IsSettled

/-- `IsSettled` は CW 回転で保存される。 -/
theorem rotateCW {s : Shape} (h : IsSettled s) : IsSettled s.rotateCW := by
  intro p hp_valid hp_ne
  -- p ∈ allValid s.rotateCW = allValid s
  rw [QuarterPos.allValid_rotateCW] at hp_valid
  -- p = (p.rotateCCW).rotateCW で書き換え
  have hp_eq : p = p.rotateCCW.rotateCW := by
    rw [QuarterPos.rotateCW_rotateCCW]
  rw [hp_eq]
  apply IsGrounded.rotateCW
  apply h
  · -- p.rotateCCW ∈ allValid s
    rw [QuarterPos.mem_allValid] at hp_valid ⊢
    -- p.1 < s.length ↔ p.rotateCCW.1 < s.length（.1 不変）
    show p.rotateCCW.1 < s.length
    rw [QuarterPos.rotateCCW_fst]
    exact hp_valid
  · -- ¬ (getQuarter s p.rotateCCW).isEmpty
    -- getQuarter s.rotateCW p = getQuarter s.rotateCW p.rotateCCW.rotateCW
    --                        = getQuarter s p.rotateCCW
    rw [hp_eq] at hp_ne
    rw [QuarterPos.getQuarter_rotateCW] at hp_ne
    exact hp_ne

/-- `IsSettled` は 180° 回転で保存される（CW の系）。 -/
theorem rotate180 {s : Shape} (h : IsSettled s) : IsSettled s.rotate180 := by
  rw [Shape.rotate180_eq_rotateCW_rotateCW]
  exact rotateCW (rotateCW h)

/-- `IsSettled` は CCW 回転で保存される（CW の系）。 -/
theorem rotateCCW {s : Shape} (h : IsSettled s) : IsSettled s.rotateCCW := by
  rw [Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW]
  exact rotateCW (rotateCW (rotateCW h))

end IsSettled

end S2IL
