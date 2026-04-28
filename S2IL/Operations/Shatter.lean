-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel
import S2IL.Operations.Common

/-!
# S2IL.Operations.Shatter

砕け散り (B-2)。脆弱（=結晶）クラスタの消失（[docs/shapez2/crystal-shatter.md](../../docs/shapez2/crystal-shatter.md)）。
Phase D-9 で `Kernel.Cluster` の `ClusterRel` を基盤として 3 つの shatter 操作を脱 axiom 化。

## 公開 API

- `Shape.shatterMask`         — 共通 primitive：位置述語に対応する象限を空に置換する
- `Shape.shatterOnFall`       — 落下時砕け散り（脆弱位置リストの結合クラスタを消去）
- `Shape.shatterOnCut`        — 切断時砕け散り（東西跨ぎクラスタを消去）
- `Shape.shatterTopCrystals`  — 切り詰め時砕け散り（しきい値以上の層に絡む結晶クラスタ）
- 対応する等変性（`*.rotateCW_comm` / `rotate180_comm` / `rotateCCW_comm`）

## 等変性の単一チェーン構造

- `shatterMask` で primitive 等変性を 1 本（`rotateCW_comm`）証明し、180° / CCW は CW の合成系。
- `shatterOnFall` / `shatterTopCrystals` は CW を直接証明、180° / CCW は 1 行系。
- `shatterOnCut` は E/W 軸依存（[architecture-layer-ab.md §1.4.1](../../docs/plans/architecture-layer-ab.md)）。
  CW 等変性は不成立、180° のみ成立し直接証明する。
-/

namespace S2IL

-- ============================================================
-- Internal primitive: shatterMaskFrom (Bool 述語によるレイヤ単位置換)
-- ============================================================

/-- `shatterMaskFrom P start s`: `s` の各レイヤ（`start, start+1, ...`）の各方角 `d` について、
    `P n d` が真なら `Quarter.empty`、偽なら元の象限を保持する。 -/
private def shatterMaskFrom (P : Nat → Direction → Bool) : Nat → Shape → Shape
  | _, [] => []
  | n, l :: ls =>
    (fun d => if P n d then Quarter.empty else l d) :: shatterMaskFrom P (n + 1) ls

/-- `shatterMaskFrom` と `Shape.rotateCW` は方角 +1 シフト相当の述語入れ替えで可換。 -/
private theorem shatterMaskFrom.rotateCW_eq
    {P P' : Nat → Direction → Bool} (h : ∀ k d, P k d = P' k (d + 1)) :
    ∀ (n : Nat) (s : Shape),
      (shatterMaskFrom P n s).rotateCW = shatterMaskFrom P' n s.rotateCW := by
  intro n s
  induction s generalizing n with
  | nil => rfl
  | cons l ls ih =>
    show List.map Layer.rotateCW (shatterMaskFrom P n (l :: ls))
        = shatterMaskFrom P' n (List.map Layer.rotateCW (l :: ls))
    rw [shatterMaskFrom, List.map_cons, List.map_cons, shatterMaskFrom]
    congr 1
    · funext d
      show (if P n (d - 1) then Quarter.empty else l (d - 1))
          = (if P' n d then Quarter.empty else l (d - 1))
      have hkey : P n (d - 1) = P' n d := by
        have := h n (d - 1)
        rwa [Direction.sub_one_add_one] at this
      rw [hkey]
    · exact ih (n + 1)

/-- 述語の同値から `decide` 値の等しさを導く小ヘルパ。 -/
private theorem decide_congr {P Q : Prop} [Decidable P] [Decidable Q]
    (h : P ↔ Q) : decide P = decide Q := by
  by_cases hP : P
  · simp [hP, h.mp hP]
  · have hQ : ¬ Q := fun hQ => hP (h.mpr hQ)
    simp [hP, hQ]

-- ============================================================
-- 公開 primitive: Shape.shatterMask
-- ============================================================

/-- 位置述語 `P` が真な象限を `Quarter.empty` に置換する。
    各 shatter 操作（`shatterOnFall` / `shatterOnCut` / `shatterTopCrystals`）は
    本 primitive を異なる `P` で具体化したものとして定義される。 -/
def Shape.shatterMask (s : Shape) (P : QuarterPos → Bool) : Shape :=
  shatterMaskFrom (fun n d => P (n, d)) 0 s

/-- `shatterMask` と CW 回転は、述語の方角 +1 シフトで可換: `P p = P' p.rotateCW`。 -/
theorem Shape.shatterMask.rotateCW_comm (s : Shape) {P P' : QuarterPos → Bool}
    (h : ∀ p, P p = P' p.rotateCW) :
    (s.shatterMask P).rotateCW = s.rotateCW.shatterMask P' := by
  unfold Shape.shatterMask
  exact shatterMaskFrom.rotateCW_eq (fun k d => h (k, d)) 0 s

/-- `shatterMask` と 180° 回転は CW を 2 段重ねた系。 -/
theorem Shape.shatterMask.rotate180_comm (s : Shape) {P P' : QuarterPos → Bool}
    (h : ∀ p, P p = P' p.rotateCW.rotateCW) :
    (s.shatterMask P).rotate180 = s.rotate180.shatterMask P' := by
  show (s.shatterMask P).rotateCW.rotateCW = s.rotateCW.rotateCW.shatterMask P'
  rw [Shape.shatterMask.rotateCW_comm (P' := fun p => P' p.rotateCW) s (fun p => h p),
      Shape.shatterMask.rotateCW_comm (P' := P') s.rotateCW (fun _ => rfl)]

/-- `shatterMask` と CCW 回転は CW を 3 段重ねた系。 -/
theorem Shape.shatterMask.rotateCCW_comm (s : Shape) {P P' : QuarterPos → Bool}
    (h : ∀ p, P p = P' p.rotateCW.rotateCW.rotateCW) :
    (s.shatterMask P).rotateCCW = s.rotateCCW.shatterMask P' := by
  show (s.shatterMask P).rotateCW.rotateCW.rotateCW = s.rotateCW.rotateCW.rotateCW.shatterMask P'
  rw [Shape.shatterMask.rotateCW_comm (P' := fun p => P' p.rotateCW.rotateCW) s (fun p => h p),
      Shape.shatterMask.rotateCW_comm (P' := fun p => P' p.rotateCW) s.rotateCW (fun _ => rfl),
      Shape.shatterMask.rotateCW_comm (P' := P') s.rotateCW.rotateCW (fun _ => rfl)]

-- ============================================================
-- shatterOnFall: 落下対象の脆弱位置から到達するクラスタ
-- ============================================================

/-- 落下時砕け散り判定: 位置 `p` は、`ps` 中の脆弱な象限と結合クラスタで連結している。 -/
def IsShatteredOnFall (s : Shape) (ps : List QuarterPos) (p : QuarterPos) : Prop :=
  ∃ t ∈ ps, (QuarterPos.getQuarter s t).isFragile = true ∧ ClusterRel s t p

noncomputable instance (s : Shape) (ps : List QuarterPos) :
    DecidablePred (IsShatteredOnFall s ps) := Classical.decPred _

/-- 落下時砕け散り。`ps` は落下対象象限の位置リスト。脆弱な象限を含む結合クラスタ全体を
    `Quarter.empty` に置換する（[docs/shapez2/crystal-shatter.md §4.1](../../docs/shapez2/crystal-shatter.md)）。 -/
noncomputable def Shape.shatterOnFall (s : Shape) (ps : List QuarterPos) : Shape :=
  s.shatterMask (fun p => decide (IsShatteredOnFall s ps p))

/-- `shatterOnFall` と CW 回転は可換（位置リストも CW 回転）。 -/
theorem Shape.shatterOnFall.rotateCW_comm (s : Shape) (ps : List QuarterPos) :
    (s.shatterOnFall ps).rotateCW =
      s.rotateCW.shatterOnFall (ps.map QuarterPos.rotateCW) := by
  unfold Shape.shatterOnFall
  apply Shape.shatterMask.rotateCW_comm
  intro p
  apply decide_congr
  unfold IsShatteredOnFall
  constructor
  · rintro ⟨t, hMem, hFrag, hRel⟩
    refine ⟨t.rotateCW, List.mem_map.mpr ⟨t, hMem, rfl⟩, ?_, ?_⟩
    · rw [QuarterPos.getQuarter_rotateCW]; exact hFrag
    · exact (ClusterRel.rotateCW s t p).mpr hRel
  · rintro ⟨t', hMem', hFrag', hRel'⟩
    rcases List.mem_map.mp hMem' with ⟨t, hMem, rfl⟩
    refine ⟨t, hMem, ?_, ?_⟩
    · rw [QuarterPos.getQuarter_rotateCW] at hFrag'; exact hFrag'
    · exact (ClusterRel.rotateCW s t p).mp hRel'

/-- `shatterOnFall` と 180° 回転は可換（CW の系）。 -/
theorem Shape.shatterOnFall.rotate180_comm (s : Shape) (ps : List QuarterPos) :
    (s.shatterOnFall ps).rotate180 =
      s.rotate180.shatterOnFall (ps.map (QuarterPos.rotateCW ∘ QuarterPos.rotateCW)) := by
  show (s.shatterOnFall ps).rotateCW.rotateCW = _
  rw [Shape.shatterOnFall.rotateCW_comm, Shape.shatterOnFall.rotateCW_comm,
      List.map_map]
  rfl

/-- `shatterOnFall` と CCW 回転は可換（CW の系）。 -/
theorem Shape.shatterOnFall.rotateCCW_comm (s : Shape) (ps : List QuarterPos) :
    (s.shatterOnFall ps).rotateCCW =
      s.rotateCCW.shatterOnFall
        (ps.map (QuarterPos.rotateCW ∘ QuarterPos.rotateCW ∘ QuarterPos.rotateCW)) := by
  show (s.shatterOnFall ps).rotateCW.rotateCW.rotateCW = _
  rw [Shape.shatterOnFall.rotateCW_comm, Shape.shatterOnFall.rotateCW_comm,
      Shape.shatterOnFall.rotateCW_comm, List.map_map, List.map_map]
  rfl

-- ============================================================
-- shatterTopCrystals: しきい値以上の層に絡む結晶クラスタ
-- ============================================================

/-- 切り詰め時砕け散り判定: 位置 `p` は、層番号 `≥ threshold` にある結晶象限と
    結合クラスタで連結している。 -/
def IsShatteredOnTruncate (s : Shape) (threshold : Nat) (p : QuarterPos) : Prop :=
  ∃ t : QuarterPos, threshold ≤ t.1 ∧ (QuarterPos.getQuarter s t).isCrystal = true
                    ∧ ClusterRel s t p

noncomputable instance (s : Shape) (threshold : Nat) :
    DecidablePred (IsShatteredOnTruncate s threshold) := Classical.decPred _

/-- 切り詰め時砕け散り。`threshold` レイヤ以上に存在する結晶を含む結合クラスタを全て消去する
    （[docs/shapez2/crystal-shatter.md §4.3](../../docs/shapez2/crystal-shatter.md)）。
    Stacker / PinPusher のレイヤ上限切り詰め時に用いる。 -/
noncomputable def Shape.shatterTopCrystals (s : Shape) (threshold : Nat) : Shape :=
  s.shatterMask (fun p => decide (IsShatteredOnTruncate s threshold p))

/-- `shatterTopCrystals` と CW 回転は可換（しきい値は不変）。 -/
theorem Shape.shatterTopCrystals.rotateCW_comm (s : Shape) (threshold : Nat) :
    (s.shatterTopCrystals threshold).rotateCW =
      s.rotateCW.shatterTopCrystals threshold := by
  unfold Shape.shatterTopCrystals
  apply Shape.shatterMask.rotateCW_comm
  intro p
  apply decide_congr
  unfold IsShatteredOnTruncate
  constructor
  · rintro ⟨t, hLayer, hCry, hRel⟩
    refine ⟨t.rotateCW, ?_, ?_, ?_⟩
    · simpa [QuarterPos.rotateCW_fst] using hLayer
    · rw [QuarterPos.getQuarter_rotateCW]; exact hCry
    · exact (ClusterRel.rotateCW s t p).mpr hRel
  · rintro ⟨t', hLayer', hCry', hRel'⟩
    refine ⟨t'.rotateCCW, ?_, ?_, ?_⟩
    · simpa [QuarterPos.rotateCCW_fst] using hLayer'
    · -- (s.getQuarter t'.rotateCCW).isCrystal = (s.rotateCW.getQuarter t'.rotateCCW.rotateCW).isCrystal
      --                                       = (s.rotateCW.getQuarter t').isCrystal = hCry'
      rw [show t' = t'.rotateCCW.rotateCW from (QuarterPos.rotateCW_rotateCCW t').symm] at hCry'
      rw [QuarterPos.getQuarter_rotateCW] at hCry'
      exact hCry'
    · -- ClusterRel s t'.rotateCCW p ← ClusterRel s.rotateCW t'.rotateCCW.rotateCW p.rotateCW
      have hr : ClusterRel s.rotateCW t'.rotateCCW.rotateCW p.rotateCW := by
        rw [QuarterPos.rotateCW_rotateCCW]; exact hRel'
      exact (ClusterRel.rotateCW s t'.rotateCCW p).mp hr

/-- `shatterTopCrystals` と 180° 回転は可換（CW の系）。 -/
theorem Shape.shatterTopCrystals.rotate180_comm (s : Shape) (threshold : Nat) :
    (s.shatterTopCrystals threshold).rotate180 =
      s.rotate180.shatterTopCrystals threshold := by
  simp [Shape.rotate180_eq_rotateCW_rotateCW, Shape.shatterTopCrystals.rotateCW_comm]

/-- `shatterTopCrystals` と CCW 回転は可換（CW の系）。 -/
theorem Shape.shatterTopCrystals.rotateCCW_comm (s : Shape) (threshold : Nat) :
    (s.shatterTopCrystals threshold).rotateCCW =
      s.rotateCCW.shatterTopCrystals threshold := by
  simp [Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW,
        Shape.shatterTopCrystals.rotateCW_comm]

-- ============================================================
-- shatterOnCut: 東西跨ぎクラスタ（E/W 軸依存、180° のみ）
-- ============================================================

/-- 切断時砕け散り判定: 位置 `p` は、東半分と西半分の両方の結晶象限を含む
    結合クラスタの構成員である。 -/
def IsShatteredOnCut (s : Shape) (p : QuarterPos) : Prop :=
  ∃ t : QuarterPos, (QuarterPos.getQuarter s t).isCrystal = true
                    ∧ ClusterRel s t p
                    ∧ (∃ pE, ClusterRel s t pE ∧ Direction.isEast pE.2 = true)
                    ∧ (∃ pW, ClusterRel s t pW ∧ Direction.isWest pW.2 = true)

noncomputable instance (s : Shape) :
    DecidablePred (IsShatteredOnCut s) := Classical.decPred _

/-- 切断時砕け散り。東西跨ぎ結合クラスタの結晶を全て消去する
    （[docs/shapez2/crystal-shatter.md §4.2](../../docs/shapez2/crystal-shatter.md)）。
    `cut` / `halfDestroy` / `swap` の前段で適用される。 -/
noncomputable def Shape.shatterOnCut (s : Shape) : Shape :=
  s.shatterMask (fun p => decide (IsShatteredOnCut s p))

/-- `shatterOnCut` と 180° 回転は可換（180° は E↔W を入れ替えるが
    「クラスタが E と W の両方を含む」性質は対称的に保存される）。 -/
theorem Shape.shatterOnCut.rotate180_comm (s : Shape) :
    (s.shatterOnCut).rotate180 = s.rotate180.shatterOnCut := by
  unfold Shape.shatterOnCut
  apply Shape.shatterMask.rotate180_comm
  intro p
  apply decide_congr
  -- 180° = rotateCW^2 として goals を unfold する。
  show IsShatteredOnCut s p ↔ IsShatteredOnCut s.rotateCW.rotateCW p.rotateCW.rotateCW
  -- 180° (= rotateCW^2) で位置と方角を 2 回 CW シフト。E witness ↔ W witness の swap。
  -- 補題: Direction での E/W 入れ替え（Fin 4 の有限性で decide 可能）。
  have hEW : ∀ d : Fin 4, Direction.isEast d = true → Direction.isWest (d + 1 + 1) = true :=
    by decide
  have hWE : ∀ d : Fin 4, Direction.isWest d = true → Direction.isEast (d + 1 + 1) = true :=
    by decide
  unfold IsShatteredOnCut
  constructor
  · rintro ⟨t, hCry, hRel, ⟨pE, hRelE, hE⟩, ⟨pW, hRelW, hW⟩⟩
    refine ⟨t.rotateCW.rotateCW, ?_, ?_, ?_, ?_⟩
    · rw [QuarterPos.getQuarter_rotateCW, QuarterPos.getQuarter_rotateCW]; exact hCry
    · exact (ClusterRel.rotateCW_two s t p).mpr hRel
    · -- 旧 W witness pW を新しい E witness pW.rotateCW.rotateCW として使う。
      exact ⟨pW.rotateCW.rotateCW, (ClusterRel.rotateCW_two s t pW).mpr hRelW, hWE pW.2 hW⟩
    · -- 旧 E witness pE を新しい W witness pE.rotateCW.rotateCW として使う。
      exact ⟨pE.rotateCW.rotateCW, (ClusterRel.rotateCW_two s t pE).mpr hRelE, hEW pE.2 hE⟩
  · rintro ⟨t', hCry', hRel', ⟨pE', hRelE', hE'⟩, ⟨pW', hRelW', hW'⟩⟩
    -- 逆方向: t'.rotateCCW.rotateCCW を取り、E/W witness も逆回転して swap。
    refine ⟨t'.rotateCCW.rotateCCW, ?_, ?_, ?_, ?_⟩
    · rw [show t' = t'.rotateCCW.rotateCCW.rotateCW.rotateCW by
            simp [QuarterPos.rotateCW_rotateCCW]] at hCry'
      rw [QuarterPos.getQuarter_rotateCW, QuarterPos.getQuarter_rotateCW] at hCry'
      exact hCry'
    · have hr : ClusterRel s.rotateCW.rotateCW
                  t'.rotateCCW.rotateCCW.rotateCW.rotateCW
                  p.rotateCW.rotateCW := by
        simp [QuarterPos.rotateCW_rotateCCW]; exact hRel'
      exact (ClusterRel.rotateCW_two s t'.rotateCCW.rotateCCW p).mp hr
    · -- 旧（rotated 側）W witness pW' を逆回転して新 E witness。
      refine ⟨pW'.rotateCCW.rotateCCW, ?_, ?_⟩
      · have hr : ClusterRel s.rotateCW.rotateCW
                  t'.rotateCCW.rotateCCW.rotateCW.rotateCW
                  pW'.rotateCCW.rotateCCW.rotateCW.rotateCW := by
          simp [QuarterPos.rotateCW_rotateCCW]; exact hRelW'
        exact (ClusterRel.rotateCW_two s t'.rotateCCW.rotateCCW pW'.rotateCCW.rotateCCW).mp hr
      · -- (pW'.rotateCCW.rotateCCW).2.isEast = true ← pW'.2.isWest = true
        show Direction.isEast (pW'.2 - 1 - 1) = true
        rw [Direction.sub_two_eq_add_two]
        exact hWE pW'.2 hW'
    · refine ⟨pE'.rotateCCW.rotateCCW, ?_, ?_⟩
      · have hr : ClusterRel s.rotateCW.rotateCW
                  t'.rotateCCW.rotateCCW.rotateCW.rotateCW
                  pE'.rotateCCW.rotateCCW.rotateCW.rotateCW := by
          simp [QuarterPos.rotateCW_rotateCCW]; exact hRelE'
        exact (ClusterRel.rotateCW_two s t'.rotateCCW.rotateCCW pE'.rotateCCW.rotateCCW).mp hr
      · show Direction.isWest (pE'.2 - 1 - 1) = true
        rw [Direction.sub_two_eq_add_two]
        exact hEW pE'.2 hE'

end S2IL
