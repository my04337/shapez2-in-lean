-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Behavior.CrystalBond
import S2IL.Behavior.Rotate
import S2IL.Behavior.Rotate180Lemmas
import Mathlib.Data.Finset.Image

/-!
# Shatter (砕け散り)

結晶の砕け散り (Shatter) 操作の定義。

砕け散りは **脆弱 (Fragile)** な属性を持つ **結晶 (Crystal)** が、
落下や切断によって破壊される現象である。
砕け散り対象の結晶は `Quarter.empty` に置き換わる。

## 砕け散りトリガー

### 切断 (Cutting) による砕け散り
シェイプを南北方向で二分する際、East Half (NE, SE) と West Half (NW, SW) の
**両方に跨がる結合クラスタ** が砕け散る。

### 落下 (Fall) による砕け散り
落下対象となった **脆弱な象限** が属する **結合クラスタ全体** が砕け散る。

## 設計方針

砕け散りはクラスタ全体に伝播する操作であるため、
`CrystalBond` で算出したクラスタ情報を利用して対象位置を決定した後、
それらの位置の象限を `Quarter.empty` に置き換える。

仕様の詳細は `docs/shapez2/crystal-shatter.md` を参照。
-/

namespace Shape

-- ============================================================

-- 切断時の砕け散り (Phase 5)
-- ============================================================

/-- 切断により砕け散る象限位置のリストを返す。
    東西に跨がる結合クラスタの全象限が対象となる。
    各結晶位置について自身のクラスタが東西跨ぎかを判定する。 -/
def shatterTargetsOnCut (s : Shape) : List QuarterPos :=
    let allPos := QuarterPos.allValid s
    allPos.filter fun p =>
        match p.getQuarter s with
        | some (.crystal _) =>
            let cc := CrystalBond.cluster s p
            decide (∃ q ∈ cc, q.dir.isEast = true) && decide (∃ q ∈ cc, q.dir.isWest = true)
        | _ => false

/-- 切断前の砕け散りを適用した結果のシェイプを返す -/
def shatterOnCut (s : Shape) : Shape :=
    s.clearPositions s.shatterTargetsOnCut

-- ============================================================
-- 落下時の砕け散り (Phase 6)
-- ============================================================

/-- 落下により砕け散る象限位置のリストを返す。
    落下対象の脆弱な象限が属する結合クラスタの全象限が対象となる。
    各結晶位置について自身のクラスタが脆弱な落下位置を含むかを判定する。 -/
def shatterTargetsOnFall (s : Shape) (fallingPositions : List QuarterPos)
        : List QuarterPos :=
    -- 落下対象のうち、脆弱な象限を抽出
    let fragilePositions := fallingPositions.filter fun p =>
        match p.getQuarter s with
        | some q => q.isFragile
        | none   => false
    -- 各結晶位置について、クラスタ内に脆弱な落下対象があるかを判定
    let allPos := QuarterPos.allValid s
    allPos.filter fun p =>
        match p.getQuarter s with
        | some (.crystal _) =>
            let cc := CrystalBond.cluster s p
            decide (∃ q ∈ cc, q ∈ fragilePositions)
        | _ => false

/-- 落下前の砕け散りを適用した結果のシェイプを返す -/
def shatterOnFall (s : Shape) (fallingPositions : List QuarterPos) : Shape :=
    s.clearPositions (s.shatterTargetsOnFall fallingPositions)

-- ============================================================
-- 180° 回転等変性の基盤補題
-- Rotate180Lemmas.lean に共通補題を集約済み
-- ============================================================

open QuarterPos (getQuarter_rotate180 getQuarter_rotate180_inv)

-- ============================================================
-- 180° 回転と shatterOnCut の可換性
-- ============================================================

-- ------------------------------------------------------------
-- List.any ヘルパー補題群
-- ------------------------------------------------------------

/-- List.map の any と BEq の関係: (ps.map f).any (· == p) = ps.any (fun q => f q == p) -/
private theorem any_map_beq {α : Type} [BEq α] (ps : List α) (f : α → α) (p : α) :
        (ps.map f).any (· == p) = ps.any (fun q => f q == p) := by
    induction ps with
    | nil => simp only [List.map_nil, List.any_nil]
    | cons x xs ih => simp only [List.map_cons, List.any_cons, ih]

/-- rotate180 は BEq に対して involution として振る舞う -/
private theorem beq_rotate180_iff (q p : QuarterPos) :
        (q.rotate180 == p) = (q == p.rotate180) := by
    cases h : (q == p.rotate180) with
    | true =>
        have := eq_of_beq h
        subst this
        show (p.rotate180.rotate180 == p) = true
        rw [QuarterPos.rotate180_rotate180]; exact BEq.rfl
    | false =>
        show (q.rotate180 == p) = false
        rw [Bool.eq_false_iff]
        intro h2
        have := eq_of_beq h2
        -- q.r180 = p → q = p.r180
        have hq : q = p.rotate180 := by
            have := congrArg QuarterPos.rotate180 this
            rw [QuarterPos.rotate180_rotate180] at this
            exact this
        rw [hq, show (p.rotate180 == p.rotate180) = true from BEq.rfl] at h
        exact Bool.noConfusion h

/-- rotate180 の involution 性を使った any の変換 -/
private theorem any_map_rotate180_beq (ps : List QuarterPos) (p : QuarterPos) :
        (ps.map QuarterPos.rotate180).any (· == p) =
        ps.any (· == p.rotate180) := by
    rw [any_map_beq]
    congr 1; ext q
    exact beq_rotate180_iff q p

-- ------------------------------------------------------------
-- isEast / isWest の rotate180 交換
-- ------------------------------------------------------------

/-- Direction.isEast と rotate180 の関係 -/
private theorem isEast_rotate180 (d : Direction) :
        d.rotate180.isEast = d.isWest := by
    cases d <;> rfl

/-- Direction.isWest と rotate180 の関係 -/
private theorem isWest_rotate180 (d : Direction) :
        d.rotate180.isWest = d.isEast := by
    cases d <;> rfl

-- ------------------------------------------------------------
-- crystalCluster の decide-exists の rotate180 等変性（Finset 版）
-- ------------------------------------------------------------

/-- crystalCluster 上の decide-exists は r180 で述語変換に対応する（Finset 版）。
    P q ↔ Q q.r180 なら decide (∃ q ∈ cc s.r180 p, P q) = decide (∃ q ∈ cc s p.r180, Q q)。
    Finset.image (crystalCluster_rotate180) を使って証明。 -/
private theorem crystalCluster_decide_exists_rotate180 (s : Shape) (p : QuarterPos)
        (P Q : QuarterPos → Prop) [DecidablePred P] [DecidablePred Q]
        (h_pq : ∀ q, P q ↔ Q q.rotate180) :
        decide (∃ q ∈ CrystalBond.cluster s.rotate180 p, P q) =
        decide (∃ q ∈ CrystalBond.cluster s p.rotate180, Q q) := by
    -- crystalCluster s.r180 p = (crystalCluster s p.r180).image r180
    have h_cc : CrystalBond.cluster s.rotate180 p =
        (CrystalBond.cluster s p.rotate180).image QuarterPos.rotate180 := by
      have := CrystalBond.cluster_rotate180 s p.rotate180
      simp only [QuarterPos.rotate180_rotate180] at this; exact this
    -- Prop ↔ を示して decide の等価性に帰着
    suffices h_iff : (∃ q ∈ CrystalBond.cluster s.rotate180 p, P q) ↔
                     (∃ q ∈ CrystalBond.cluster s p.rotate180, Q q) by
      cases h1 : decide (∃ q ∈ CrystalBond.cluster s.rotate180 p, P q) <;>
        cases h2 : decide (∃ q ∈ CrystalBond.cluster s p.rotate180, Q q) <;>
        simp_all only [decide_eq_true_eq, decide_eq_false_iff_not]
    rw [h_cc]
    constructor
    · rintro ⟨q, hq, hpq⟩
      rw [Finset.mem_image] at hq
      obtain ⟨r, hr, rfl⟩ := hq
      exact ⟨r, hr, by have := (h_pq r.rotate180).mp hpq; rwa [QuarterPos.rotate180_rotate180] at this⟩
    · rintro ⟨q, hq, hqq⟩
      exact ⟨q.rotate180, Finset.mem_image_of_mem _ hq,
        (h_pq q.rotate180).mpr (by rwa [QuarterPos.rotate180_rotate180])⟩

/-- shatterTargetsOnCut の判定述語は r180 で不変 -/
private theorem shatterTargetPred_rotate180 (s : Shape) (p : QuarterPos) :
        (match p.getQuarter s.rotate180 with
         | some (.crystal _) =>
            decide (∃ q ∈ CrystalBond.cluster s.rotate180 p, q.dir.isEast = true) &&
            decide (∃ q ∈ CrystalBond.cluster s.rotate180 p, q.dir.isWest = true)
         | _ => false) =
        (match p.rotate180.getQuarter s with
         | some (.crystal _) =>
            decide (∃ q ∈ CrystalBond.cluster s p.rotate180, q.dir.isEast = true) &&
            decide (∃ q ∈ CrystalBond.cluster s p.rotate180, q.dir.isWest = true)
         | _ => false) := by
    rw [getQuarter_rotate180_inv]
    cases p.rotate180.getQuarter s with
    | none => rfl
    | some q =>
        cases q with
        | crystal _ =>
            simp only
            -- isEast r180 = isWest, isWest r180 = isEast なので東西が入れ替わり && で戻る
            have h_east := crystalCluster_decide_exists_rotate180 s p
                (fun q => q.dir.isEast = true) (fun q => q.dir.isWest = true)
                (fun q => by simp only [QuarterPos.rotate180, isWest_rotate180])
            have h_west := crystalCluster_decide_exists_rotate180 s p
                (fun q => q.dir.isWest = true) (fun q => q.dir.isEast = true)
                (fun q => by simp only [QuarterPos.rotate180, isEast_rotate180])
            rw [h_east, h_west]
            exact Bool.and_comm ..
        | _ => rfl

/-- l.any (fun q => (q == p) && f q) = (l.any (· == p)) && f p
    BEq が一致する要素の述語を f p に集約する -/
private theorem any_beq_and [BEq α] [LawfulBEq α] (l : List α) (p : α) (f : α → Bool) :
        l.any (fun q => (q == p) && f q) = ((l.any (· == p)) && f p) := by
    induction l with
    | nil => simp only [List.any_nil, Bool.false_and]
    | cons x xs ih =>
        simp only [List.any_cons]
        rw [ih]
        -- goal: (x == p) && f x || xs.any (· == p) && f p
        --     = ((x == p) || xs.any (· == p)) && f p
        cases hx : (x == p) with
        | false => simp only [Bool.false_and, Bool.false_or]
        | true =>
            have hxp := eq_of_beq hx; subst hxp
            simp only [Bool.true_and, Bool.true_or, Bool.or_eq_left_iff_imp,
                Bool.and_eq_true, List.any_eq_true, beq_iff_eq, exists_eq_right,
                and_imp, imp_self, implies_true]

/-- any_beq_and の && 逆順版 -/
private theorem any_and_beq [BEq α] [LawfulBEq α] (l : List α) (p : α) (f : α → Bool) :
        l.any (fun q => f q && (q == p)) = ((l.any (· == p)) && f p) := by
    have : (fun q => f q && (q == p)) = (fun q => (q == p) && f q) := by
        funext q; exact Bool.and_comm ..
    rw [this, any_beq_and]

/-- allValid_any_rotate180: allValid の filter 後 any が r180 で等変 -/
private theorem filter_any_rotate180 (s : Shape)
        (pred_r : QuarterPos → Bool) (pred_s : QuarterPos → Bool)
        (h_pred : ∀ q, pred_r q = pred_s q.rotate180)
        (p : QuarterPos) :
        ((QuarterPos.allValid s).filter pred_r).any (· == p) =
        ((QuarterPos.allValid s).filter pred_s).any (· == p.rotate180) := by
    simp only [List.any_filter]
    rw [any_and_beq, any_and_beq]
    rw [h_pred p, CrystalBond.allValid_any_rotate180]

private theorem shatterTargetsOnCut_any_rotate180 (s : Shape) (p : QuarterPos) :
        (shatterTargetsOnCut s.rotate180).any (· == p) =
        (shatterTargetsOnCut s).any (· == p.rotate180) := by
    simp only [shatterTargetsOnCut,
        CrystalBond.allValid_rotate180]
    exact filter_any_rotate180 s _ _ (fun q => shatterTargetPred_rotate180 s q) p

/-- 砕け散り対象位置の clearPositions 結果は rotate180 で等変である -/
private theorem clearPositions_shatterTargetsOnCut_rotate180_eq (s : Shape) :
        (s.rotate180).clearPositions (s.rotate180.shatterTargetsOnCut) =
        (s.rotate180).clearPositions (s.shatterTargetsOnCut.map QuarterPos.rotate180) := by
    apply Shape.clearPositions_ext
    intro p
    rw [any_map_rotate180_beq, shatterTargetsOnCut_any_rotate180]

/-- fragilePositions の getQuarter 判定は r180 で不変 -/
private theorem fragile_pred_rotate180 (s : Shape) (p : QuarterPos) :
        (match p.rotate180.getQuarter s.rotate180 with
         | some q => q.isFragile | none => false) =
        (match p.getQuarter s with
         | some q => q.isFragile | none => false) := by
    have h := getQuarter_rotate180_inv s p.rotate180
    rw [QuarterPos.rotate180_rotate180] at h
    rw [h]

/-- fragilePositions(s.r180, ps.map r180) = fragilePositions(s, ps).map r180 -/
private theorem fragilePositions_map_rotate180 (s : Shape) (ps : List QuarterPos) :
        (ps.map QuarterPos.rotate180).filter (fun p =>
            match p.getQuarter s.rotate180 with | some q => q.isFragile | none => false) =
        (ps.filter (fun p =>
            match p.getQuarter s with | some q => q.isFragile | none => false)).map
            QuarterPos.rotate180 := by
    induction ps with
    | nil => simp only [List.map_nil, List.filter_nil]
    | cons x xs ih =>
        simp only [List.map_cons, List.filter_cons]
        rw [fragile_pred_rotate180]
        cases match x.getQuarter s with | some q => q.isFragile | none => false with
        | true => simp only [↓reduceIte, ih, List.map_cons]
        | false => simp only [Bool.false_eq_true, ↓reduceIte, ih]

/-- shatterTargetsOnFall の落下判定述語は r180 で等変 -/
private theorem shatterFallPred_rotate180 (s : Shape) (ps : List QuarterPos)
        (p : QuarterPos) :
        (match p.getQuarter s.rotate180 with
         | some (.crystal _) =>
            decide (∃ q ∈ CrystalBond.cluster s.rotate180 p,
                q ∈ (ps.map QuarterPos.rotate180).filter (fun (rr : QuarterPos) =>
                    match rr.getQuarter s.rotate180 with | some w => w.isFragile | none => false))
         | _ => false) =
        (match p.rotate180.getQuarter s with
         | some (.crystal _) =>
            decide (∃ q ∈ CrystalBond.cluster s p.rotate180,
                q ∈ ps.filter (fun (rr : QuarterPos) =>
                    match rr.getQuarter s with | some w => w.isFragile | none => false))
         | _ => false) := by
    rw [getQuarter_rotate180_inv]
    cases h : p.rotate180.getQuarter s with
    | none => rfl
    | some q =>
        cases q with
        | crystal _ =>
            simp only
            -- fragilePositions の r180 等変性
            have h_frag := fragilePositions_map_rotate180 s ps
            -- qq ∈ fragR180 ↔ qq.r180 ∈ fragOrig を示して
            -- crystalCluster_decide_exists_rotate180 に帰着
            let fragOrig := ps.filter (fun rr =>
                match rr.getQuarter s with | some w => w.isFragile | none => false)
            exact crystalCluster_decide_exists_rotate180 s p
                (fun qq => qq ∈ (ps.map QuarterPos.rotate180).filter (fun (rr : QuarterPos) =>
                    match rr.getQuarter s.rotate180 with | some w => w.isFragile | none => false))
                (fun qq => qq ∈ fragOrig)
                (fun qq => by
                    simp only [h_frag, List.mem_map]
                    constructor
                    · rintro ⟨r, hr, rfl⟩
                      rwa [QuarterPos.rotate180_rotate180]
                    · intro hq
                      exact ⟨qq.rotate180, hq, QuarterPos.rotate180_rotate180 qq⟩)
        | _ => rfl

/-- shatterTargetsOnFall の any-membership は rotate180 で等変 -/
private theorem shatterTargetsOnFall_any_rotate180 (s : Shape)
        (ps : List QuarterPos) (p : QuarterPos) :
        (shatterTargetsOnFall s.rotate180 (ps.map QuarterPos.rotate180)).any (· == p) =
        (shatterTargetsOnFall s ps).any (· == p.rotate180) := by
    simp only [shatterTargetsOnFall,
        CrystalBond.allValid_rotate180]
    exact filter_any_rotate180 s _ _ (fun q => shatterFallPred_rotate180 s ps q) p

/-- 落下砕け散り対象の clearPositions 結果は rotate180 で等変である。 -/
private theorem clearPositions_shatterTargetsOnFall_rotate180_eq (s : Shape)
        (ps : List QuarterPos) :
        (s.rotate180).clearPositions
            (s.rotate180.shatterTargetsOnFall (ps.map QuarterPos.rotate180)) =
        (s.rotate180).clearPositions
            ((s.shatterTargetsOnFall ps).map QuarterPos.rotate180) := by
    apply Shape.clearPositions_ext
    intro p
    rw [any_map_rotate180_beq, shatterTargetsOnFall_any_rotate180]

/-- 切断砕け散りと 180° 回転は可換である。
    すなわち、先に砕け散らせてから 180° 回転しても、
    先に 180° 回転してから砕け散らせても結果は同じである -/
theorem shatterOnCut_rotate180_comm (s : Shape) :
        s.shatterOnCut.rotate180 = s.rotate180.shatterOnCut := by
    simp only [shatterOnCut]
    rw [clearPositions_rotate180]
    exact (clearPositions_shatterTargetsOnCut_rotate180_eq s).symm

/-- 落下砕け散りと 180° 回転は可換である。
    落下位置も一緒に 180° 回転する必要がある -/
theorem shatterOnFall_rotate180_comm (s : Shape) (ps : List QuarterPos) :
        (s.shatterOnFall ps).rotate180 =
        s.rotate180.shatterOnFall (ps.map QuarterPos.rotate180) := by
    simp only [shatterOnFall]
    rw [clearPositions_rotate180]
    exact (clearPositions_shatterTargetsOnFall_rotate180_eq s ps).symm

-- ============================================================
-- shatterOnFall の位置集合拡張性
-- ============================================================

/-- filter 後の .any メンバーシップは元リストの .any と述語値の AND に等しい -/
private theorem filter_any_eq (l : List QuarterPos) (pred : QuarterPos → Bool)
        (q : QuarterPos) :
        (l.filter pred).any (· == q) = (l.any (· == q) && pred q) := by
    induction l with
    | nil => simp only [List.filter, List.any_nil, List.any, Bool.false_and]
    | cons x xs ih =>
        simp only [List.filter]
        cases hpx : pred x with
        | false =>
            simp only [List.any_cons, ih]
            cases hxq : (x == q) with
            | false => simp only [Bool.false_or]
            | true =>
                have := eq_of_beq hxq; subst this
                simp only [hpx, Bool.and_false, Bool.true_or]
        | true =>
            simp only [List.any_cons, ih]
            cases hxq : (x == q) with
            | false => simp only [Bool.false_or]
            | true =>
                have := eq_of_beq hxq; subst this
                simp only [hpx, Bool.and_true, Bool.true_or, Bool.and_self]

/-- shatterOnFall は位置集合の .any メンバーシップのみに依存する。
    2 つの位置リストが各位置について同じ .any 結果を返すなら、
    shatterOnFall の結果は同じである -/
theorem shatterOnFall_ext (s : Shape) (ps1 ps2 : List QuarterPos)
        (h : ∀ p, ps1.any (· == p) = ps2.any (· == p)) :
        s.shatterOnFall ps1 = s.shatterOnFall ps2 := by
    simp only [shatterOnFall, shatterTargetsOnFall]
    -- clearPositions の引数が同じことを示す
    congr 1
    -- allPos.filter の述語が各 p について同値であることを示す
    let fragPred := fun (p : QuarterPos) =>
        match p.getQuarter s with | some q => q.isFragile | none => false
    -- fragilePositions の .any メンバーシップが同値
    have h_frag : ∀ q,
            (ps1.filter fragPred).any (· == q) =
            (ps2.filter fragPred).any (· == q) := by
        intro q
        simp only [filter_any_eq]
        rw [h q]
    -- allPos.filter の述語が一致
    apply List.filter_congr
    intro p _
    -- h : ∀ p, ps1.any == = ps2.any == から List メンバーシップの同値を導く
    have h_ps_mem : ∀ q, q ∈ ps1 ↔ q ∈ ps2 := by
        intro q
        constructor
        · intro hq
          have h1 : ps1.any (· == q) = true := by
              simp only [List.any_eq_true]; exact ⟨q, hq, BEq.rfl⟩
          rw [h] at h1
          obtain ⟨x, hx, hbeq⟩ := List.any_eq_true.mp h1
          exact eq_of_beq hbeq ▸ hx
        · intro hq
          have h2 : ps2.any (· == q) = true := by
              simp only [List.any_eq_true]; exact ⟨q, hq, BEq.rfl⟩
          rw [← h] at h2
          obtain ⟨x, hx, hbeq⟩ := List.any_eq_true.mp h2
          exact eq_of_beq hbeq ▸ hx
    have h_frag_mem : ∀ q, q ∈ ps1.filter fragPred ↔ q ∈ ps2.filter fragPred := by
        intro q
        simp only [List.mem_filter]
        exact ⟨fun ⟨hm, hp⟩ => ⟨(h_ps_mem q).mp hm, hp⟩,
               fun ⟨hm, hp⟩ => ⟨(h_ps_mem q).mpr hm, hp⟩⟩
    -- match p.getQuarter s の各ケース
    cases p.getQuarter s with
    | none => rfl
    | some q =>
        cases q <;> try rfl
        case crystal c =>
            -- decide (∃ q ∈ cc, q ∈ filter1) = decide (∃ q ∈ cc, q ∈ filter2)
            show decide _ = decide _
            congr 1
            exact propext ⟨fun ⟨q, hq, hm⟩ => ⟨q, hq, (h_frag_mem q).mp hm⟩,
                   fun ⟨q, hq, hm⟩ => ⟨q, hq, (h_frag_mem q).mpr hm⟩⟩

-- ============================================================
-- 超過レイヤの砖け散り
-- ============================================================

/-- レイヤ上限超過分の象限を落下対象として砖け散り処理を適用する。
    超過レイヤの脆弱結晶が属する結晶結合クラスタ全体が砖け散る -/
def shatterOnTruncate (s : Shape) (maxLayers : Nat) : Shape :=
    let truncatedPositions := (QuarterPos.allValid s).filter fun p =>
        p.layer ≥ maxLayers
    s.shatterOnFall truncatedPositions
end Shape
