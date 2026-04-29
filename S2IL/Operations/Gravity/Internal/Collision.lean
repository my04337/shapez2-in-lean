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

## 現在の進捗（D-10D 着手セッション）

| 補題 | 状態 |
|---|---|
| `groundingNeighbors_subset_groundingEdge` (soundness) | ✅ 証明済 |
| `groundingNeighbors_supset_groundingEdge` (completeness) | ✅ 証明済 |
| `groundingNeighbors_iff_groundingEdge` | ✅ 証明済 |
| `isGroundedFast_of_isGrounded` (BFS completeness) | 🚧 sorry（fuel 充足性証明が要） |
| `isGrounded_of_isGroundedFast` (BFS soundness) | 🚧 sorry（reachClosure の不変条件） |
| `isGroundedFast_iff_isGrounded` | 🚧 sorry（上 2 本に依存） |
| `floatingUnits_eq_nil_of_isSettled` | 🚧 sorry（iff + structuralCluster 構造不変） |
| `gravity_isSettled_collision` | 🚧 sorry（D-10D 後半、最大の山場） |

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

/-- `Quarter.IsCrystal q` ならば `q.isEmpty = false`。 -/
private theorem crystal_isEmpty_eq_false {q : Quarter}
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
  -- 戦略:
  --   1. isGroundedFast 展開: p ∈ reachClosure step layer0Roots fuel
  --   2. layer0Roots の各要素 p₀ は p₀.1 = 0 ∧ ¬empty なので IsGrounded 自身
  --   3. reachClosure の各反復で追加される q は ∃ p ∈ current, q ∈ groundingNeighbors s p
  --      → §1.iff より IsGroundingEdge s p q → ReflTransGen 拡張
  --   4. fuel の induction で閉じる
  sorry

/-- BFS が `IsGrounded` の到達集合と一致することの completeness 半分。 -/
theorem isGroundedFast_of_isGrounded
    (s : Shape) (p : QuarterPos) :
    IsGrounded s p → isGroundedFast s p = true := by
  -- 戦略:
  --   1. IsGrounded s p から ReflTransGen IsGroundingEdge p₀ p を取り出す（n ホップ）
  --   2. n ≤ s.length * 4（非空位置総数）のため fuel 充足
  --   3. §1.iff より各ホップが groundingNeighbors の 1 段に対応
  --   4. ホップ数の induction で reachClosure に到達
  sorry

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

/-- 構造クラスタのメンバはすべて結合能力を持つ（= 非空非ピン）。 -/
theorem structuralCluster_canFormBond
    (s : Shape) (p q : QuarterPos)
    (hq : q ∈ structuralCluster s p) :
    (QuarterPos.getQuarter s q).canFormBond = true := by
  -- 戦略: structuralCluster は structuralNeighbors を BFS で拡張する。
  --   - structuralNeighbors はそもそも `qp.canFormBond = false` なら []
  --   - 開始点 p が canFormBond でないと cluster が単元集合になり、p 自身が canFormBond でない
  --     ことを別途チェックする
  -- ただし structuralCluster は p を root に常に含む。
  -- floatingClusters / structuralClusters 側で「root が canFormBond」をフィルタしている前提でのみ
  -- 本補題が成立する点に注意。
  sorry

/-- 構造クラスタのメンバはすべて非空。 -/
theorem structuralCluster_nonEmpty
    (s : Shape) (p q : QuarterPos)
    (hq : q ∈ structuralCluster s p) :
    ¬ (QuarterPos.getQuarter s q).isEmpty := by
  -- canFormBond → 非空（Quarter.canFormBond の定義）
  intro h
  have := structuralCluster_canFormBond s p q hq
  -- canFormBond と isEmpty は互いに排他: empty/pin は canFormBond=false、それ以外は true
  -- isEmpty=true は empty なので canFormBond=false と矛盾
  sorry

-- ============================================================
-- §5. floatingUnits = [] for IsSettled inputs
-- ============================================================

/-- 浮遊クラスタは存在しない（`IsSettled` 入力）。 -/
theorem floatingClusters_eq_nil_of_isSettled
    {s : Shape} (hs : IsSettled s) :
    floatingClusters s = [] := by
  -- 戦略:
  --   1. floatingClusters s = (structuralClusters s).filter (clusterFloating s)
  --   2. 任意のクラスタ cl に対し、cl の任意のメンバ q は §4 より非空
  --   3. q ∈ allValid s（structuralClusters は nonEmptyPositions から構築される、それは allValid）
  --   4. hs より IsGrounded s q → §3 より isGroundedFast s q = true
  --   5. clusterFloating s cl = false なので filter で除外される
  sorry

/-- 浮遊ピンは存在しない（`IsSettled` 入力）。 -/
theorem floatingPins_eq_nil_of_isSettled
    {s : Shape} (hs : IsSettled s) :
    floatingPins s = [] := by
  -- 戦略: 各 pin 位置 p について
  --   1. p は nonEmptyPositions に居る（pin = 非空）
  --   2. p ∈ allValid s
  --   3. hs より IsGrounded s p → §3 より isGroundedFast s p = true
  --   4. floatingPins の filter から除外される
  sorry

/-- §5 主定理: `IsSettled` 入力に対して落下単位は存在しない。
    Behavior.lean のブリッジ axiom を **theorem** に格上げするための本命補題。 -/
theorem floatingUnits_eq_nil_of_isSettled
    {s : Shape} (hs : IsSettled s) :
    floatingUnits s = [] := by
  unfold floatingUnits
  rw [floatingClusters_eq_nil_of_isSettled hs,
      floatingPins_eq_nil_of_isSettled hs]
  simp

-- ============================================================
-- §6. gravity.isSettled — 安定性主定理
-- ============================================================

/-- `gravity` の出力は `IsSettled`。Phase D-10D の最終目標。
    本セッションでは骨格のみ。証明戦略のメモを残す。 -/
theorem gravity_isSettled_collision (s : Shape) :
    IsSettled (Shape.gravity s) := by
  -- 戦略 (gravity-proof-plan.md §7 D-10D ステップ 3):
  --   gravity s = (foldl stepUnit obs0 sortedUnits).normalize
  --   1. normalize は IsSettled を保つ（末尾空除去のみ）—別補題が必要
  --   2. foldl 後の placed shape の各非空位置 q を考える
  --   3. q は次の 2 系統:
  --      (a) 落下しなかった元シェイプの位置 → obs0 由来 → s 由来で IsSettled に組込み済か
  --          ※obs0 のうち接地済の位置は最初から grounded
  --      (b) ある unit U の placeUnit による着地位置 (q' - dropOf U, q'.2)
  --          → dropOf の最大性から「直下に障害物 or layer 0」
  --          → IsContact 縦上方向（q.layer=0 なら自分が root）が成立
  --   4. (a)(b) いずれも layer 0 root から ReflTransGen で到達
  --   5. ただし fold 中の上書きで (a) の grounded 性が壊れないことの保証が必要
  --      → unit の元位置は obs0 で空、unit が新たに書き込むのは別位置
  --      → 元 grounded 位置は不変（衝突判定が排除）
  --
  -- 反例検証: §4.1 / §4.1.1 で 11 件 + interlock I-1/I-1'/I-2 が一致を確認済。
  -- I-3（同列 cluster + pin で着地スロット重なり）は本定理の構成的証明により
  -- 「dropOf を 1 回計算した固定写像」として cross-unit 上書きを排除する。
  sorry

end Internal
end Gravity
end S2IL
