-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity.Defs
import Mathlib.Logic.Relation

/-!
# S2IL.Operations.Gravity.Internal.Collision

落下処理に伴う **接地 BFS** と **構造クラスタ** の正当性（Phase D-10D 進行中、骨格段階）。

## 役割

`Internal/Collision.lean` は Phase D-10D の主証明を担う:

1. `groundingNeighbors` (computable BFS の 1 段) と `IsGroundingEdge` (Prop の関係) の **エッジ同値性**
2. `isGroundedFast` (Bool BFS) と `IsGrounded` (Prop の到達) の **完全同値性**
3. 上記から `floatingUnits_eq_nil_of_isSettled` をブリッジ axiom から **theorem** に格上げ
4. `dropOf` 構造由来の安定性主定理 `gravity.isSettled` を構成的に証明

## 現在の進捗（D-10D 進行中）

| 補題 | 状態 |
|---|---|
| `groundingNeighbors_subset_groundingEdge` (soundness) | ✅ 証明済 |
| `groundingNeighbors_supset_groundingEdge` (completeness) | ✅ 証明済 |
| `groundingNeighbors_iff_groundingEdge` | ✅ 証明済 |
| `isGrounded_of_isGroundedFast` (BFS soundness) | ✅ 証明済（D-10D-3）|
| `isGroundedFast_of_isGrounded` (BFS completeness) | ✅ 証明済（D-10D-3、`reachClosure_closed_of_fuel_ge` に依存）|
| `isGroundedFast_iff_isGrounded` | ✅ 証明済（系）|
| `structuralCluster_canFormBond` | ✅ 証明済（D-10D-3、`hp` 仮定追加）|
| `structuralCluster_nonEmpty` | ✅ 証明済（D-10D-3）|
| `floatingPins_eq_nil_of_isSettled` | ✅ 証明済（D-10D-3）|
| `floatingClusters_eq_nil_of_isSettled` | 🚧 sorry（`partition` の構造化が要、D-10D-4 で対処）|
| `floatingUnits_eq_nil_of_isSettled` | 🚧 transitive sorry（cluster 解決後に自動）|
| `gravity_isSettled_collision` | 🚧 sorry（D-10D 後半、最大の山場）|

外部 sub-lemma:

| 補題 | 場所 | 状態 |
|---|---|---|
| `reachClosure_closed_of_fuel_ge` | `Internal/BFS.lean` | 🚧 sorry（fuel 充足 → 閉包性、D-10D-4 で対処）|

## MECE 構造

| サブセクション | 範囲 |
|---|---|
| §1 Edge correspondence | `groundingNeighbors` ↔ `IsGroundingEdge` (1 ホップ) |
| §2 BFS reachClosure invariants | `reachClosure step roots fuel` の到達集合性 |
| §3 isGroundedFast ↔ IsGrounded | §1 + §2 の合成 |
| §4 structuralCluster 構造不変 | クラスタメンバが `canFormBond` ⇒ 非空 |
| §5 floatingUnits の特徴付け | §3 + §4 から bridge を theorem 化 |
| §6 gravity.isSettled | dropOf 構造から構成的に |

設計指針: 旧 wave モデル ([_archive/pre-greenfield/Operations/Gravity/])
の `placeLDGroups_landing_groundingEdge_mono` 系は **採用しない**。
`dropOf` を 1 回計算した固定写像とし、衝突判定が同列 cross-unit の上書きを構造的に排除する
（[gravity-proof-plan.md §3.5](../../../../docs/plans/gravity-proof-plan.md)）。
-/

namespace S2IL
namespace Gravity
namespace Internal

open S2IL.Gravity
open Relation

-- ============================================================
-- Direction の隣接判定に関する小補題（§1 で利用）
-- ============================================================

/-- `Direction` 上の `(d + 1) - d = 1`。 -/
private theorem add_one_sub_self (d : Direction) : d + 1 - d = 1 := by
  ext; simp [Fin.sub_def, Fin.add_def]; omega

/-- `Direction` 上の `d - (d - 1) = 1`。 -/
private theorem self_sub_sub_one (d : Direction) : d - (d - 1) = 1 := by
  ext; simp [Fin.sub_def]; omega

/-- `Quarter.IsCrystal` から `(...).isEmpty = false` を取り出す（`Internal.Settled.lean` でも参照）。 -/
theorem crystal_isEmpty_eq_false {q : Quarter}
    (h : q.IsCrystal) : q.isEmpty = false := by
  rcases q with _ | _ | c | _ <;>
    simp_all [Quarter.IsCrystal, Quarter.isCrystal, Quarter.isEmpty]

/-- `Quarter.IsCrystal q` ならば `q ≠ .pin`。 -/
private theorem crystal_ne_pin {q : Quarter}
    (h : q.IsCrystal) : q ≠ .pin := by
  rcases q with _ | _ | c | _ <;>
    simp_all [Quarter.IsCrystal, Quarter.isCrystal]

/-- `isAdjacent d (d + 1) = true`。 -/
private theorem isAdjacent_add_one (d : Direction) :
    Direction.isAdjacent d (d + 1) = true := by
  simp only [Direction.isAdjacent, add_one_sub_self,
             decide_true, Bool.or_true]

/-- `isAdjacent d (d - 1) = true`。 -/
private theorem isAdjacent_sub_one (d : Direction) :
    Direction.isAdjacent d (d - 1) = true := by
  simp only [Direction.isAdjacent, self_sub_sub_one,
             decide_true, Bool.true_or]

/-- `isAdjacent` 成立から「`+1` 側か `-1` 側か」の場合分け。 -/
private theorem isAdjacent_cases {d₁ d₂ : Direction}
    (h : Direction.isAdjacent d₁ d₂ = true) :
    d₂ = d₁ + 1 ∨ d₂ = d₁ - 1 := by
  unfold Direction.isAdjacent at h
  rw [Bool.or_eq_true] at h
  rcases h with h1 | h2
  · -- d₁ - d₂ = 1 → d₂ = d₁ - 1
    right
    have heq : d₁ - d₂ = (1 : Direction) := decide_eq_true_eq.mp h1
    apply Fin.ext
    have hv : (d₁ - d₂).val = 1 := by rw [heq]; rfl
    simp [Fin.sub_def] at hv ⊢
    omega
  · -- d₂ - d₁ = 1 → d₂ = d₁ + 1
    left
    have heq : d₂ - d₁ = (1 : Direction) := decide_eq_true_eq.mp h2
    apply Fin.ext
    have hv : (d₂ - d₁).val = 1 := by rw [heq]; rfl
    simp [Fin.sub_def, Fin.add_def] at hv ⊢
    omega

/-- `IsGrounded` のホップで現れる位置はすべて非空。 -/
private theorem groundingEdge_isEmpty_eq_false {s : Shape} {a b : QuarterPos}
    (h : IsGroundingEdge s a b) : ¬ (QuarterPos.getQuarter s b).isEmpty := by
  rcases h with hUp | hBond
  · rcases hUp.1 with hVert | hHoriz
    · exact hVert.2.2.2
    · exact hHoriz.2.2.2.1
  · rcases hBond with hIn | hCross
    · rw [crystal_isEmpty_eq_false hIn.2.2.2]; decide
    · rw [crystal_isEmpty_eq_false hCross.2.2.2]; decide

/-- 任意の方角は `Direction.all` に含まれる。 -/
private theorem mem_direction_all (d : Direction) : d ∈ Direction.all := by
  show d ∈ ([0, 1, 2, 3] : List Direction)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rcases d with ⟨_ | _ | _ | _ | n, hv⟩
  · left; rfl
  · right; left; rfl
  · right; right; left; rfl
  · right; right; right; rfl
  · omega

/-- `Direction.all` は重複なし。 -/
private theorem direction_all_nodup : (Direction.all : List Direction).Nodup := by
  show ([0, 1, 2, 3] : List Direction).Nodup
  decide

/-- `layer0Roots s` は重複なし（`Direction.all` の filterMap に基づく）。 -/
private theorem layer0Roots_nodup (s : Shape) : (layer0Roots s).Nodup := by
  unfold layer0Roots
  refine direction_all_nodup.filterMap ?_
  -- 単射性: 同じ QuarterPos `q` を返す `d`, `d'` があれば `d = d'`
  intro d d' q hd hd'
  -- hd, hd' : q ∈ if ... then none else some (0, d) / d'
  by_cases h1 : (QuarterPos.getQuarter s (0, d)).isEmpty
  · simp [h1] at hd
  · simp [h1] at hd
    by_cases h2 : (QuarterPos.getQuarter s (0, d')).isEmpty
    · simp [h2] at hd'
    · simp [h2] at hd'
      -- hd : (0, d) = q, hd' : (0, d') = q
      have heq : ((0, d) : QuarterPos) = (0, d') := hd.trans hd'.symm
      exact (Prod.mk.injEq _ _ _ _).mp heq |>.2

/-- 非空位置は `nonEmptyPositions s` に含まれる。 -/
private theorem mem_nonEmptyPositions {s : Shape} {p : QuarterPos}
    (hne : ¬ (QuarterPos.getQuarter s p).isEmpty) :
    p ∈ nonEmptyPositions s := by
  have hp_lt : p.1 < s.length := by
    by_contra hlen
    apply hne
    show (if h : p.1 < s.length then s[p.1] p.2 else Quarter.empty).isEmpty = true
    rw [dif_neg hlen]; rfl
  unfold nonEmptyPositions
  refine List.mem_filter.mpr ⟨?_, by simpa using hne⟩
  unfold QuarterPos.allValid
  refine List.mem_flatMap.mpr ⟨p.1, List.mem_range.mpr hp_lt, ?_⟩
  refine List.mem_map.mpr ⟨p.2, mem_direction_all _, ?_⟩
  rcases p with ⟨l, d⟩; rfl

-- ============================================================
-- §1. Edge correspondence:  groundingNeighbors  ↔  IsGroundingEdge
-- ============================================================
/-- `groundingNeighborsUp` に居るなら、`(p.1+1, p.2)` の上方向接地接触で接続。 -/
private theorem up_subset_groundingEdge (s : Shape) (p q : QuarterPos)
    (hq : q ∈ groundingNeighborsUp s p) : IsGroundingEdge s p q := by
  unfold groundingNeighborsUp at hq
  split at hq
  · simp at hq
  · split at hq
    · simp at hq
    · rename_i hpne hupne
      simp at hq
      subst hq
      -- p.1 ≤ p.1 + 1 で IsUpwardGroundingContact 縦 inl
      refine .inl ⟨.inl ⟨rfl, .inl rfl, ?_, ?_⟩, by omega⟩
      · simpa using hpne
      · simpa using hupne

/-- `groundingNeighborsHoriz` に居るなら、同層 adjacent contact で接続。 -/
private theorem horiz_subset_groundingEdge (s : Shape) (p q : QuarterPos)
    (hq : q ∈ groundingNeighborsHoriz s p) : IsGroundingEdge s p q := by
  simp only [groundingNeighborsHoriz] at hq
  split at hq
  · simp at hq
  · rename_i hne_or
    rw [not_or] at hne_or
    obtain ⟨hpne_eq, hp_npin⟩ := hne_or
    have hpne : ¬ (QuarterPos.getQuarter s p).isEmpty := by simpa using hpne_eq
    simp only [List.mem_filter, horizontalAdj, List.mem_cons,
               List.not_mem_nil, or_false] at hq
    obtain ⟨hmem, hpred⟩ := hq
    -- hpred : decide (¬ qq.isEmpty ∧ qq ≠ .pin) = true
    have hpred' : ¬ (QuarterPos.getQuarter s q).isEmpty ∧
        QuarterPos.getQuarter s q ≠ Quarter.pin :=
      decide_eq_true_eq.mp hpred
    have hqne : ¬ (QuarterPos.getQuarter s q).isEmpty := hpred'.1
    have hqnpin : QuarterPos.getQuarter s q ≠ Quarter.pin := hpred'.2
    -- IsUpwardGroundingContact via horizontal IsContact
    refine .inl ⟨.inr ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · -- p.1 = q.1
      rcases hmem with hmem | hmem
      · rw [hmem]
      · rw [hmem]
    · -- isAdjacent p.2 q.2 = true
      rcases hmem with hmem | hmem
      · rw [hmem]; exact isAdjacent_add_one _
      · rw [hmem]; exact isAdjacent_sub_one _
    · -- ¬ (getQuarter s p).isEmpty
      simpa using hpne
    · -- ¬ (getQuarter s q).isEmpty
      exact hqne
    · -- getQuarter s p ≠ pin
      intro h; exact hp_npin h
    · -- getQuarter s q ≠ pin
      exact hqnpin
    · -- p.1 ≤ q.1
      rcases hmem with hmem | hmem
      · rw [hmem]
      · rw [hmem]

/-- `groundingNeighborsDown` に居るなら、下方向 cross-layer 結合で接続。 -/
private theorem down_subset_groundingEdge (s : Shape) (p q : QuarterPos)
    (hq : q ∈ groundingNeighborsDown s p) : IsGroundingEdge s p q := by
  unfold groundingNeighborsDown at hq
  split at hq
  · rename_i hcond
    obtain ⟨hpC, hp1, hqC⟩ := hcond
    simp at hq
    subst hq
    -- IsBondedCrossLayer: q.1 + 1 = p.1, q.2 = p.2, both crystal
    refine .inr (.inr ⟨.inr ?_, rfl, ?_, ?_⟩)
    · omega
    · -- (getQuarter s p).IsCrystal
      exact hpC
    · -- (getQuarter s (p.1-1, p.2)).IsCrystal
      exact hqC
  · simp at hq

/-- §1 主定理（soundness 方向）。
    BFS の 1 段で得られる隣接位置は、必ず `IsGroundingEdge` で結ばれる。 -/
theorem groundingNeighbors_subset_groundingEdge
    (s : Shape) (p q : QuarterPos) :
    q ∈ groundingNeighbors s p → IsGroundingEdge s p q := by
  intro hq
  unfold groundingNeighbors at hq
  rcases List.mem_append.mp hq with hUH | hD
  · rcases List.mem_append.mp hUH with hU | hH
    · exact up_subset_groundingEdge s p q hU
    · exact horiz_subset_groundingEdge s p q hH
  · exact down_subset_groundingEdge s p q hD

/-- §1 主定理（completeness 方向）。
    `IsGroundingEdge` で結ばれた `q` は BFS の 1 段で必ず列挙される。 -/
theorem groundingNeighbors_supset_groundingEdge
    (s : Shape) (p q : QuarterPos) :
    IsGroundingEdge s p q → q ∈ groundingNeighbors s p := by
  intro hedge
  unfold groundingNeighbors
  -- 戦略: hedge の各ブランチを groundingNeighborsUp/Horiz/Down のいずれかに割り付ける。
  rcases hedge with hUpward | hBond
  · -- IsUpwardGroundingContact: vertical or horizontal IsContact + p.1 ≤ q.1
    obtain ⟨hCtc, hle⟩ := hUpward
    rcases hCtc with hVert | hHoriz
    · -- vertical
      obtain ⟨hd, hlay, hpne, hqne⟩ := hVert
      rcases hlay with h1 | h2
      · -- p.1 + 1 = q.1 → up branch
        have hqeq : q = (p.1 + 1, p.2) :=
          Prod.ext_iff.mpr ⟨h1.symm, hd.symm⟩
        apply List.mem_append.mpr; left
        apply List.mem_append.mpr; left
        unfold groundingNeighborsUp
        rw [if_neg (by simpa using hpne)]
        rw [if_neg (by simpa [← hqeq] using hqne)]
        simp [hqeq]
      · -- q.1 + 1 = p.1 → 矛盾 (hle : p.1 ≤ q.1 だが p.1 = q.1 + 1 > q.1)
        omega
    · -- horizontal: a.1=b.1, isAdjacent a.2 b.2, both non-empty, both non-pin
      obtain ⟨hlay, hadj, hpne, hqne, hp_npin, hq_npin⟩ := hHoriz
      apply List.mem_append.mpr; left
      apply List.mem_append.mpr; right
      simp only [groundingNeighborsHoriz]
      have hcond : ¬ ((QuarterPos.getQuarter s p).isEmpty = true ∨
                      QuarterPos.getQuarter s p = .pin) := by
        rw [not_or]; exact ⟨by simpa using hpne, hp_npin⟩
      rw [if_neg hcond]
      simp only [List.mem_filter, horizontalAdj, List.mem_cons,
                 List.not_mem_nil, or_false]
      refine ⟨?_, ?_⟩
      · -- q ∈ [(p.1, p.2+1), (p.1, p.2-1)]
        rcases isAdjacent_cases hadj with hpos | hneg
        · left;  exact Prod.ext_iff.mpr ⟨hlay.symm, hpos⟩
        · right; exact Prod.ext_iff.mpr ⟨hlay.symm, hneg⟩
      · -- decide (...) = true
        exact decide_eq_true_eq.mpr ⟨by simpa using hqne, hq_npin⟩
  · -- IsBonded: InLayer or CrossLayer
    rcases hBond with hIn | hCross
    · -- InLayer: a.1=b.1, isAdjacent a.2 b.2, both crystal → horiz branch
      obtain ⟨hlay, hadj, hpC, hqC⟩ := hIn
      apply List.mem_append.mpr; left
      apply List.mem_append.mpr; right
      simp only [groundingNeighborsHoriz]
      have hp_ne : (QuarterPos.getQuarter s p).isEmpty = false :=
        crystal_isEmpty_eq_false hpC
      have hp_npin : QuarterPos.getQuarter s p ≠ .pin := crystal_ne_pin hpC
      have hq_ne : (QuarterPos.getQuarter s q).isEmpty = false :=
        crystal_isEmpty_eq_false hqC
      have hq_npin : QuarterPos.getQuarter s q ≠ .pin := crystal_ne_pin hqC
      have hcond : ¬ ((QuarterPos.getQuarter s p).isEmpty = true ∨
                      QuarterPos.getQuarter s p = .pin) := by
        rw [not_or]; refine ⟨?_, hp_npin⟩; rw [hp_ne]; decide
      rw [if_neg hcond]
      simp only [List.mem_filter, horizontalAdj, List.mem_cons,
                 List.not_mem_nil, or_false]
      refine ⟨?_, ?_⟩
      · rcases isAdjacent_cases hadj with hpos | hneg
        · left;  exact Prod.ext_iff.mpr ⟨hlay.symm, hpos⟩
        · right; exact Prod.ext_iff.mpr ⟨hlay.symm, hneg⟩
      · refine decide_eq_true_eq.mpr ⟨?_, hq_npin⟩
        rw [hq_ne]; decide
    · -- CrossLayer: (p.1+1=q.1 ∨ q.1+1=p.1) ∧ p.2=q.2 ∧ both crystal
      obtain ⟨hlay, hd, hpC, hqC⟩ := hCross
      rcases hlay with h1 | h2
      · -- p.1+1=q.1 → up branch (crystal は non-empty)
        apply List.mem_append.mpr; left
        apply List.mem_append.mpr; left
        unfold groundingNeighborsUp
        have hp_ne : (QuarterPos.getQuarter s p).isEmpty = false :=
          crystal_isEmpty_eq_false hpC
        have hqeq : q = (p.1 + 1, p.2) :=
          Prod.ext_iff.mpr ⟨h1.symm, hd.symm⟩
        have hq_ne : (QuarterPos.getQuarter s (p.1 + 1, p.2)).isEmpty = false := by
          rw [← hqeq]; exact crystal_isEmpty_eq_false hqC
        rw [if_neg (by rw [hp_ne]; decide)]
        rw [if_neg (by rw [hq_ne]; decide)]
        simp [hqeq]
      · -- q.1+1=p.1 → down branch
        apply List.mem_append.mpr; right
        unfold groundingNeighborsDown
        have hp1 : p.1 ≥ 1 := by omega
        have hq_eq : q = (p.1 - 1, p.2) :=
          Prod.ext_iff.mpr ⟨by show q.1 = p.1 - 1; omega, hd.symm⟩
        have hqC' : (QuarterPos.getQuarter s (p.1 - 1, p.2)).IsCrystal := by
          rw [← hq_eq]; exact hqC
        rw [if_pos ⟨hpC, hp1, hqC'⟩]
        simp [hq_eq]

/-- §1 系: edge レベルの Iff 同値性。 -/
theorem groundingNeighbors_iff_groundingEdge
    (s : Shape) (p q : QuarterPos) :
    q ∈ groundingNeighbors s p ↔ IsGroundingEdge s p q :=
  ⟨groundingNeighbors_subset_groundingEdge s p q,
   groundingNeighbors_supset_groundingEdge s p q⟩

-- ============================================================
-- §2. reachClosure 不変条件（足場補題は Defs.lean 側で公開する必要あり）
-- ============================================================

/-! `reachClosure` / `horizontalAdj` などは `Defs.lean` で `private def` のため、
ここから直接参照できない。Phase D-10D の本格証明に入る際は次のいずれかに切替える:

1. `Defs.lean` 側で `private` を外す（公開化）
2. `Internal/` 配下に `BFS.lean` を新設し、`reachClosure` を移管
3. `Defs.lean` 末尾に必要な API 補題（`mem_reachClosure_iff` 等）を `theorem` で公開

設計上は **2 を推奨**: BFS の汎用性と Gravity 固有の `groundingNeighbors` を分離できる。
本セッションでは骨格のみ（D-10D 後半セッションで実装）。 -/

/-- BFS が `IsGrounded` の到達集合と一致することの soundness 半分。 -/
theorem isGrounded_of_isGroundedFast
    (s : Shape) (p : QuarterPos) :
    isGroundedFast s p = true → IsGrounded s p := by
  intro h
  -- isGroundedFast 展開
  have hmem : p ∈ reachClosure
      (fun current => current.flatMap (groundingNeighbors s))
      (layer0Roots s) (s.length * 4 + 4) := by
    simpa [isGroundedFast] using h
  -- reachClosure_induction で P := IsGrounded s ·
  refine reachClosure_induction
    (step := fun current => current.flatMap (groundingNeighbors s))
    (P := IsGrounded s) ?_ (layer0Roots s) (s.length * 4 + 4) ?_ p hmem
  · -- step 保存: y ∈ current.flatMap groundingNeighbors → IsGrounded s y
    intro current y hcurrent hy
    rcases List.mem_flatMap.mp hy with ⟨x, hxc, hxy⟩
    have hgx : IsGrounded s x := hcurrent x hxc
    have hedge : IsGroundingEdge s x y :=
      groundingNeighbors_subset_groundingEdge s x y hxy
    rcases hgx with ⟨p₀, hp0, hne, hpath⟩
    exact ⟨p₀, hp0, hne, ReflTransGen.tail hpath hedge⟩
  · -- 初期値: layer0Roots の各要素は IsGrounded
    intro p₀ hp0
    -- layer0Roots: filterMap over Direction.all
    unfold layer0Roots at hp0
    rcases List.mem_filterMap.mp hp0 with ⟨d, _hdall, hd⟩
    by_cases hempty : (QuarterPos.getQuarter s (0, d)).isEmpty
    · simp [hempty] at hd
    · simp [hempty] at hd
      subst hd
      refine ⟨(0, d), rfl, ?_, ReflTransGen.refl⟩
      simpa using hempty

/-- BFS が `IsGrounded` の到達集合と一致することの completeness 半分。 -/
theorem isGroundedFast_of_isGrounded
    (s : Shape) (p : QuarterPos) :
    IsGrounded s p → isGroundedFast s p = true := by
  rintro ⟨p₀, hp0, hne, hpath⟩
  set step : List QuarterPos → List QuarterPos :=
    fun current => current.flatMap (groundingNeighbors s) with hstep_def
  set fuel : Nat := s.length * 4 + 4 with hfuel_def
  -- p₀ ∈ layer0Roots s
  have hp0_root : p₀ ∈ layer0Roots s := by
    unfold layer0Roots
    refine List.mem_filterMap.mpr ⟨p₀.2, mem_direction_all _, ?_⟩
    have hp0_eq : p₀ = (0, p₀.2) := by
      rcases p₀ with ⟨l, d⟩; cases hp0; rfl
    rw [← hp0_eq]
    simp [hne]
  -- 閉包補題（fuel 充足を nonEmptyPositions で保証）
  have hclosed : ∀ y ∈ step (reachClosure step (layer0Roots s) fuel),
      y ∈ reachClosure step (layer0Roots s) fuel := by
    refine reachClosure_closed_of_fuel_ge step (layer0Roots s) fuel
      (nonEmptyPositions s) (layer0Roots_nodup s) ?_ ?_ ?_
    · -- layer0Roots ⊆ nonEmptyPositions
      intro x hx
      unfold layer0Roots at hx
      rcases List.mem_filterMap.mp hx with ⟨d, _, hd⟩
      by_cases hempty : (QuarterPos.getQuarter s (0, d)).isEmpty
      · simp [hempty] at hd
      · simp [hempty] at hd
        subst hd
        exact mem_nonEmptyPositions (by simpa using hempty)
    · -- step は nonEmptyPositions を保つ
      intro xs y _ hy
      rcases List.mem_flatMap.mp hy with ⟨x, _, hxy⟩
      have hedge : IsGroundingEdge s x y :=
        groundingNeighbors_subset_groundingEdge s x y hxy
      exact mem_nonEmptyPositions (groundingEdge_isEmpty_eq_false hedge)
    · -- fuel ≥ |nonEmptyPositions|
      have h1 : (nonEmptyPositions s).length ≤ (QuarterPos.allValid s).length := by
        unfold nonEmptyPositions; exact List.length_filter_le _ _
      have h2 : (QuarterPos.allValid s).length = s.length * 4 := by
        unfold QuarterPos.allValid
        simp [List.length_flatMap, Direction.all]
      omega
  -- ReflTransGen 経路の induction
  have hgoal : p ∈ reachClosure step (layer0Roots s) fuel := by
    induction hpath with
    | refl =>
      exact mem_init_subset_reachClosure step (layer0Roots s) fuel _ hp0_root
    | @tail b c _ hedge ih =>
      apply hclosed
      refine List.mem_flatMap.mpr ⟨b, ih, ?_⟩
      exact groundingNeighbors_supset_groundingEdge s b c hedge
  show decide _ = true
  exact decide_eq_true_eq.mpr hgoal

-- ============================================================
-- §3. isGroundedFast ↔ IsGrounded（メイン同値）
-- ============================================================

/-- BFS と Prop 接地は同値。
    Phase D-10D の中核。完成すると Behavior.lean のブリッジ axiom が theorem 化される。 -/
theorem isGroundedFast_iff_isGrounded
    (s : Shape) (p : QuarterPos) :
    isGroundedFast s p = true ↔ IsGrounded s p :=
  ⟨isGrounded_of_isGroundedFast s p, isGroundedFast_of_isGrounded s p⟩

-- ============================================================
-- §4. structuralCluster の構造不変
-- ============================================================

/-- 構造クラスタのメンバはすべて結合能力を持つ（= 非空非ピン）。

`structuralCluster s p` は root `p` を常に含むため、root が `canFormBond` を持つ
ことを仮定しないと成立しない。 -/
theorem structuralCluster_canFormBond
    (s : Shape) (p q : QuarterPos)
    (hp : (QuarterPos.getQuarter s p).canFormBond = true)
    (hq : q ∈ structuralCluster s p) :
    (QuarterPos.getQuarter s q).canFormBond = true := by
  unfold structuralCluster at hq
  refine reachClosure_induction
    (step := fun current => current.flatMap (structuralNeighbors s))
    (P := fun x => (QuarterPos.getQuarter s x).canFormBond = true)
    ?_ [p] _ ?_ q hq
  · -- step 保存: y ∈ flatMap (structuralNeighbors s) current → canFormBond y
    intro current y _ hy
    rcases List.mem_flatMap.mp hy with ⟨x, _, hxy⟩
    -- y ∈ structuralNeighbors s x: 各ブランチで両端 canFormBond
    unfold structuralNeighbors at hxy
    by_cases hxC : (QuarterPos.getQuarter s x).canFormBond
    · simp only [hxC, Bool.not_true, Bool.false_eq_true, if_false] at hxy
      rcases List.mem_append.mp hxy with hSA | hBelow
      · rcases List.mem_append.mp hSA with hSame | hAbove
        · -- horizontalAdj filtered by canFormBond
          rcases List.mem_filter.mp hSame with ⟨_, hpred⟩
          simpa using hpred
        · -- above branch
          by_cases hAbC : (QuarterPos.getQuarter s (x.1 + 1, x.2)).canFormBond
          · rw [if_pos hAbC] at hAbove
            rw [List.mem_singleton] at hAbove
            subst hAbove; exact hAbC
          · rw [if_neg hAbC] at hAbove
            simp at hAbove
      · -- below branch
        by_cases hcond : x.1 ≥ 1 ∧ (QuarterPos.getQuarter s (x.1 - 1, x.2)).canFormBond
        · rw [if_pos hcond] at hBelow
          rw [List.mem_singleton] at hBelow
          subst hBelow; exact hcond.2
        · rw [if_neg hcond] at hBelow
          simp at hBelow
    · simp [hxC] at hxy
  · -- 初期値: P p
    intro x hx
    rcases List.mem_singleton.mp hx with rfl
    exact hp

/-- 構造クラスタのメンバはすべて非空。 -/
theorem structuralCluster_nonEmpty
    (s : Shape) (p q : QuarterPos)
    (hp : (QuarterPos.getQuarter s p).canFormBond = true)
    (hq : q ∈ structuralCluster s p) :
    ¬ (QuarterPos.getQuarter s q).isEmpty := by
  intro h
  have hbond : (QuarterPos.getQuarter s q).canFormBond = true :=
    structuralCluster_canFormBond s p q hp hq
  -- canFormBond=true ∧ isEmpty=true は矛盾
  rcases hgQ : QuarterPos.getQuarter s q with _ | _ | _ | _ <;>
    simp_all [Quarter.canFormBond, Quarter.isEmpty]

-- ============================================================
-- §5. floatingUnits = [] for IsSettled inputs
-- ============================================================

/-- partition の構造補題: 結果のクラスタは初期 acc または `xs` の元素由来。 -/
private theorem mem_structuralClustersPartition
    (s : Shape) :
    ∀ (xs : List QuarterPos) (acc : List (List QuarterPos)) (fuel : Nat)
      (cl : List QuarterPos),
      cl ∈ structuralClustersPartition s xs acc fuel →
        cl ∈ acc ∨ ∃ p ∈ xs, cl = structuralCluster s p := by
  intro xs acc fuel
  induction fuel generalizing xs acc with
  | zero =>
    intro cl hcl
    left
    simpa [structuralClustersPartition] using hcl
  | succ n ih =>
    intro cl hcl
    cases hxs : xs with
    | nil =>
      left
      rw [hxs] at hcl
      simpa [structuralClustersPartition] using hcl
    | cons p rest =>
      rw [hxs] at hcl
      simp only [structuralClustersPartition] at hcl
      rcases ih _ _ cl hcl with hAcc | ⟨q, hq_in, hq_eq⟩
      · -- cl ∈ structuralCluster s p :: acc
        rcases List.mem_cons.mp hAcc with hroot | hAcc'
        · right; exact ⟨p, List.mem_cons_self, hroot⟩
        · left; exact hAcc'
      · -- q ∈ filter (· ∉ structuralCluster s p) rest, cl = structuralCluster s q
        right
        rcases List.mem_filter.mp hq_in with ⟨hq_rest, _⟩
        exact ⟨q, List.mem_cons.mpr (Or.inr hq_rest), hq_eq⟩

/-- 浮遊クラスタは存在しない（`IsSettled` 入力）。 -/
theorem floatingClusters_eq_nil_of_isSettled
    {s : Shape} (hs : IsSettled s) :
    floatingClusters s = [] := by
  unfold floatingClusters
  apply List.filter_eq_nil_iff.mpr
  intro cl hcl
  -- cl ∈ structuralClusters s
  unfold structuralClusters at hcl
  rcases mem_structuralClustersPartition s _ _ _ cl hcl with hAcc | ⟨p, hp_in, hp_eq⟩
  · -- 初期 acc = []
    cases hAcc
  · -- p ∈ bondablePos s, cl = structuralCluster s p
    rcases List.mem_filter.mp hp_in with ⟨hp_ne, hp_bond⟩
    -- bondablePos: filter on nonEmptyPositions, condition canFormBond
    have hp_bond' : (QuarterPos.getQuarter s p).canFormBond = true := by
      simpa using hp_bond
    -- p ∈ nonEmptyPositions s → ¬ isEmpty
    unfold nonEmptyPositions at hp_ne
    rcases List.mem_filter.mp hp_ne with ⟨hp_valid, hp_nonempty⟩
    have hp_nonempty' : ¬ (QuarterPos.getQuarter s p).isEmpty := by
      simpa using hp_nonempty
    -- IsSettled gives IsGrounded
    have hgrounded : IsGrounded s p := hs p hp_valid hp_nonempty'
    have hfast : isGroundedFast s p = true :=
      (isGroundedFast_iff_isGrounded s p).mpr hgrounded
    -- p ∈ structuralCluster s p
    have hp_in_cl : p ∈ structuralCluster s p := by
      unfold structuralCluster
      apply mem_init_subset_reachClosure
      exact List.mem_singleton.mpr rfl
    -- clusterFloating cl = false
    rw [hp_eq]
    intro hfloat
    unfold clusterFloating at hfloat
    rw [List.all_eq_true] at hfloat
    have := hfloat p hp_in_cl
    simp [hfast] at this

/-- 浮遊ピンは存在しない（`IsSettled` 入力）。 -/
theorem floatingPins_eq_nil_of_isSettled
    {s : Shape} (hs : IsSettled s) :
    floatingPins s = [] := by
  unfold floatingPins
  apply List.filter_eq_nil_iff.mpr
  intro p hp
  -- hp : p ∈ nonEmptyPositions s
  unfold nonEmptyPositions at hp
  rcases List.mem_filter.mp hp with ⟨hpv, hpne⟩
  have hne : ¬ (QuarterPos.getQuarter s p).isEmpty := by simpa using hpne
  -- IsSettled gives IsGrounded
  have hgrounded : IsGrounded s p := hs p hpv hne
  have hfast : isGroundedFast s p = true :=
    (isGroundedFast_iff_isGrounded s p).mpr hgrounded
  -- predicate becomes `... && false = false`
  simp [hfast]

/-- §5 主定理: `IsSettled` 入力に対して落下単位は存在しない。
    Behavior.lean のブリッジ axiom を **theorem** に格上げするための本命補題。 -/
theorem floatingUnits_eq_nil_of_isSettled
    {s : Shape} (hs : IsSettled s) :
    floatingUnits s = [] := by
  unfold floatingUnits
  rw [floatingClusters_eq_nil_of_isSettled hs,
      floatingPins_eq_nil_of_isSettled hs]
  simp

end Internal
end Gravity
end S2IL

-- §6 (`gravity.isSettled` 主定理 + 周辺補題) は `Internal/Settled.lean` に分離。
