-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Behavior.CrystalBond
import S2IL.Behavior.Rotate

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
            let cc := CrystalBond.crystalCluster s p
            cc.any (fun q => q.dir.isEast) && cc.any (fun q => q.dir.isWest)
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
            let cc := CrystalBond.crystalCluster s p
            cc.any (fun q => fragilePositions.any (· == q))
        | _ => false

/-- 落下前の砕け散りを適用した結果のシェイプを返す -/
def shatterOnFall (s : Shape) (fallingPositions : List QuarterPos) : Shape :=
    s.clearPositions (s.shatterTargetsOnFall fallingPositions)

-- ============================================================
-- 180° 回転等変性の基盤補題
-- ============================================================

/-- getDir と rotate180 の可換性: 回転後の方角で取得 = 回転前の方角で取得 -/
private theorem getDir_rotate180 (l : Layer) (d : Direction) :
        QuarterPos.getDir (l.rotate180) (d.rotate180) = QuarterPos.getDir l d := by
    cases d <;> rfl

/-- setDir (.empty) と rotate180 の可換性 -/
private theorem setDir_rotate180_empty (l : Layer) (d : Direction) :
        (QuarterPos.setDir l d .empty).rotate180 = QuarterPos.setDir (l.rotate180) (d.rotate180) .empty := by
    cases d <;> rfl

/-- Shape.layers と rotate180 の関係 -/
private theorem layers_rotate180 (s : Shape) :
        s.rotate180.layers = s.layers.map Layer.rotate180 := by
    simp [Shape.rotate180, Shape.mapLayers]

/-- getQuarter と rotate180 の可換性 -/
private theorem getQuarter_rotate180 (s : Shape) (pos : QuarterPos) :
        pos.rotate180.getQuarter s.rotate180 = pos.getQuarter s := by
    simp only [QuarterPos.getQuarter, QuarterPos.rotate180, layers_rotate180]
    rw [List.getElem?_map]
    cases s.layers[pos.layer]? with
    | none => rfl
    | some l => simp [getDir_rotate180]

/-- List.map_set 補助: (l.set i a).map f = (l.map f).set i (f a) -/
private theorem list_map_set {α β : Type} (f : α → β) (l : List α) (i : Nat) (a : α) :
        (l.set i a).map f = (l.map f).set i (f a) := by
    induction l generalizing i with
    | nil => simp
    | cons x xs ih =>
        cases i with
        | zero => simp [List.set]
        | succ n => simp [List.set, ih]

/-- layers のリストから構築されるシェイプの rotate180 -/
private theorem shape_of_layers_rotate180 (xs : List Layer) (fallback : Shape) :
        (match xs with
         | [] => fallback
         | b :: us => ⟨b :: us, List.cons_ne_nil b us⟩ : Shape).rotate180 =
        match xs.map Layer.rotate180 with
         | [] => fallback.rotate180
         | b :: us => ⟨b :: us, List.cons_ne_nil b us⟩ := by
    cases xs with
    | nil => rfl
    | cons b us => ext1; simp [Shape.rotate180, Shape.mapLayers]

/-- List.set は非空リストを空にしない -/
private theorem set_ne_nil_of_ne_nil {α : Type} {l : List α} (h : l ≠ []) (i : Nat) (a : α) :
        l.set i a ≠ [] := by
    cases l with
    | nil => exact absurd rfl h
    | cons x xs => cases i <;> simp [List.set]

/-- setQuarter のレイヤが存在する場合、.layers は List.set の結果に等しい -/
private theorem setQuarter_layers_eq (s : Shape) (pos : QuarterPos) (q : Quarter) (l : Layer)
        (hl : s.layers[pos.layer]? = some l) :
        (pos.setQuarter s q).layers = s.layers.set pos.layer (QuarterPos.setDir l pos.dir q) := by
    simp only [QuarterPos.setQuarter, hl]
    -- 内部 match の分岐を split で解決する
    split
    · -- nil case: s.layers.set ... = [] は s.layers ≠ [] と矛盾
      rename_i h
      exact absurd h (set_ne_nil_of_ne_nil s.layers_ne pos.layer _)
    · -- cons case: .layers = newLayers
      rfl

/-- setQuarter (.empty) と rotate180 の可換性 -/
private theorem setQuarter_rotate180_empty (s : Shape) (pos : QuarterPos) :
        (pos.setQuarter s .empty).rotate180 = (pos.rotate180).setQuarter (s.rotate180) .empty := by
    cases hl : s.layers[pos.layer]? with
    | none =>
        -- 範囲外: 両辺とも元のシェイプを返す
        simp only [QuarterPos.setQuarter, QuarterPos.rotate180, layers_rotate180,
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
                    simp only [Shape.rotate180, Shape.mapLayers, QuarterPos.rotate180]
                    exact hl_r)]
        simp only [QuarterPos.rotate180, list_map_set, setDir_rotate180_empty,
                    Shape.rotate180, Shape.mapLayers]

/-- clearPositions と rotate180 の可換性 -/
private theorem clearPositions_rotate180 (s : Shape) (ps : List QuarterPos) :
        (s.clearPositions ps).rotate180 =
        (s.rotate180).clearPositions (ps.map QuarterPos.rotate180) := by
    induction ps generalizing s with
    | nil => rfl
    | cons p rest ih =>
        show (Shape.clearPositions (p.setQuarter s .empty) rest).rotate180 =
            Shape.clearPositions ((p.rotate180).setQuarter (s.rotate180) .empty)
                (rest.map QuarterPos.rotate180)
        rw [ih, setQuarter_rotate180_empty]

/-- isBondedInLayer は rotate180 で不変 -/
private theorem isBondedInLayer_rotate180 (s : Shape) (p1 p2 : QuarterPos) :
        CrystalBond.isBondedInLayer (s.rotate180) (p1.rotate180) (p2.rotate180) =
        CrystalBond.isBondedInLayer s p1 p2 := by
    -- getQuarter_rotate180 を QuarterPos.rotate180 展開前に適用
    simp only [CrystalBond.isBondedInLayer, getQuarter_rotate180]
    simp only [QuarterPos.rotate180, Direction.adjacent_rotate180]

/-- isBondedCrossLayer は rotate180 で不変 -/
private theorem isBondedCrossLayer_rotate180 (s : Shape) (p1 p2 : QuarterPos) :
        CrystalBond.isBondedCrossLayer (s.rotate180) (p1.rotate180) (p2.rotate180) =
        CrystalBond.isBondedCrossLayer s p1 p2 := by
    -- getQuarter_rotate180 を QuarterPos.rotate180 展開前に適用
    simp only [CrystalBond.isBondedCrossLayer, getQuarter_rotate180]
    simp only [QuarterPos.rotate180]
    -- 残り: dir.rotate180 == dir.rotate180 を dir == dir に
    congr 1
    cases p1.dir <;> cases p2.dir <;> rfl

/-- isBonded は rotate180 で不変 -/
private theorem isBonded_rotate180 (s : Shape) (p1 p2 : QuarterPos) :
        CrystalBond.isBonded (s.rotate180) (p1.rotate180) (p2.rotate180) =
        CrystalBond.isBonded s p1 p2 := by
    simp only [CrystalBond.isBonded,
               isBondedInLayer_rotate180, isBondedCrossLayer_rotate180]

-- ============================================================
-- 180° 回転と shatterOnCut の可換性
-- ============================================================

-- ------------------------------------------------------------
-- foldl の一般的メンバーシップ補題
-- ------------------------------------------------------------

/-- 条件付き連結 foldl のメンバーシップ分解 -/
private theorem foldl_concat_any {α : Type} [BEq α] [LawfulBEq α]
        (clusters : List (List α)) (pred : List α → Bool) (init : List α)
        (p : α) :
        (clusters.foldl (fun acc c => if pred c then acc ++ c else acc) init).any (· == p) =
        (init.any (· == p) || clusters.any (fun c => pred c && c.any (· == p))) := by
    induction clusters generalizing init with
    | nil => simp [List.foldl]
    | cons c rest ih =>
        simp only [List.foldl, List.any_cons]
        cases hpc : pred c with
        | false =>
            have : (false = true) = False := by simp
            simp only [this, ite_false, ih, Bool.false_and, Bool.false_or]
        | true =>
            simp only [ite_true, ih, List.any_append, Bool.true_and]
            -- init.any p || c.any p || rest.any ... = (init.any p || (c.any p || rest.any ...))
            cases hinit : init.any (· == p) <;>
            cases hc : c.any (· == p) <;>
            simp_all

/-- List.map の any と BEq の関係: (ps.map f).any (· == p) = ps.any (fun q => f q == p) -/
private theorem any_map_beq {α : Type} [BEq α] (ps : List α) (f : α → α) (p : α) :
        (ps.map f).any (· == p) = ps.any (fun q => f q == p) := by
    induction ps with
    | nil => simp
    | cons x xs ih => simp [List.any_cons, ih]

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
-- クラスタの東西跨ぎ判定の rotate180 等変性
-- ------------------------------------------------------------

/-- クラスタの東側判定は rotate180 で西側判定に対応する -/
private theorem cluster_any_isEast_rotate180 (cluster : List QuarterPos) :
        cluster.any (fun p => p.dir.isEast) =
        (cluster.map QuarterPos.rotate180).any (fun p => p.dir.isWest) := by
    induction cluster with
    | nil => simp
    | cons x xs ih =>
        simp [List.any_cons, ih, QuarterPos.rotate180, isWest_rotate180]

/-- クラスタの西側判定は rotate180 で東側判定に対応する -/
private theorem cluster_any_isWest_rotate180 (cluster : List QuarterPos) :
        cluster.any (fun p => p.dir.isWest) =
        (cluster.map QuarterPos.rotate180).any (fun p => p.dir.isEast) := by
    induction cluster with
    | nil => simp
    | cons x xs ih =>
        simp [List.any_cons, ih, QuarterPos.rotate180, isEast_rotate180]

-- ------------------------------------------------------------
-- shatterTargetsOnCut / shatterTargetsOnFall の rotate180 等変性
-- crystalCluster ベースの定義に対して直接証明する
-- ------------------------------------------------------------

/-- getQuarter の rotate180 逆方向: p から s.r180 へのアクセス = p.r180 から s へのアクセス -/
private theorem getQuarter_rotate180_inv (s : Shape) (p : QuarterPos) :
        p.getQuarter s.rotate180 = p.rotate180.getQuarter s := by
    have h := getQuarter_rotate180 s p.rotate180
    rw [QuarterPos.rotate180_rotate180] at h
    exact h

/-- crystalCluster の any は r180 で述語変換に対応する（一般版）
    f q = g q.r180 なら (cc s.r180 p).any f = (cc s p.r180).any g -/
private theorem crystalCluster_any_rotate180_general (s : Shape) (p : QuarterPos)
        (f g : QuarterPos → Bool)
        (h_fg : ∀ q, f q = g q.rotate180) :
        (CrystalBond.crystalCluster s.rotate180 p).any f =
        (CrystalBond.crystalCluster s p.rotate180).any g := by
    cases h : (CrystalBond.crystalCluster s.rotate180 p).any f with
    | true =>
        rw [List.any_eq_true] at h
        obtain ⟨q, hq_mem, hq_f⟩ := h
        have hq_any : (CrystalBond.crystalCluster s.rotate180 p).any (· == q) = true :=
            List.any_eq_true.mpr ⟨q, hq_mem, BEq.rfl⟩
        have hq_r180 : (CrystalBond.crystalCluster s p.rotate180).any (· == q.rotate180) = true := by
            have := CrystalBond.crystalCluster_mem_rotate180 s.rotate180 p q
            rw [Shape.rotate180_rotate180] at this
            rw [← this]; exact hq_any
        rw [List.any_eq_true] at hq_r180
        obtain ⟨x, hx_mem, hx_beq⟩ := hq_r180
        have hx_eq := eq_of_beq hx_beq
        symm; rw [List.any_eq_true]
        exact ⟨x, hx_mem, by subst hx_eq; rw [← h_fg]; exact hq_f⟩
    | false =>
        symm; rw [Bool.eq_false_iff]
        intro h_g
        rw [List.any_eq_true] at h_g
        obtain ⟨q', hq'_mem, hq'_g⟩ := h_g
        have hq'_any : (CrystalBond.crystalCluster s p.rotate180).any (· == q') = true :=
            List.any_eq_true.mpr ⟨q', hq'_mem, BEq.rfl⟩
        have hq'_r180 : (CrystalBond.crystalCluster s.rotate180 p).any (· == q'.rotate180) = true := by
            have := CrystalBond.crystalCluster_mem_rotate180 s p.rotate180 q'
            rw [QuarterPos.rotate180_rotate180] at this
            rw [← this]; exact hq'_any
        rw [List.any_eq_true] at hq'_r180
        obtain ⟨y, hy_mem, hy_beq⟩ := hq'_r180
        have hy_eq := eq_of_beq hy_beq
        rw [Bool.eq_false_iff] at h
        apply h
        rw [List.any_eq_true]
        exact ⟨y, hy_mem, by rw [hy_eq, h_fg, QuarterPos.rotate180_rotate180]; exact hq'_g⟩

/-- crystalCluster の any-isEast は r180 で any-isWest に対応 -/
private theorem crystalCluster_any_isEast_r180 (s : Shape) (p : QuarterPos) :
        (CrystalBond.crystalCluster s.rotate180 p).any (fun q => q.dir.isEast) =
        (CrystalBond.crystalCluster s p.rotate180).any (fun q => q.dir.isWest) :=
    crystalCluster_any_rotate180_general s p _ _ (fun q => by
        simp [QuarterPos.rotate180, isWest_rotate180])

/-- crystalCluster の any-isWest は r180 で any-isEast に対応 -/
private theorem crystalCluster_any_isWest_r180 (s : Shape) (p : QuarterPos) :
        (CrystalBond.crystalCluster s.rotate180 p).any (fun q => q.dir.isWest) =
        (CrystalBond.crystalCluster s p.rotate180).any (fun q => q.dir.isEast) :=
    crystalCluster_any_rotate180_general s p _ _ (fun q => by
        simp [QuarterPos.rotate180, isEast_rotate180])

/-- shatterTargetsOnCut の判定述語は r180 で不変 -/
private theorem shatterTargetPred_rotate180 (s : Shape) (p : QuarterPos) :
        (match p.getQuarter s.rotate180 with
         | some (.crystal _) =>
            (CrystalBond.crystalCluster s.rotate180 p).any (fun q => q.dir.isEast) &&
            (CrystalBond.crystalCluster s.rotate180 p).any (fun q => q.dir.isWest)
         | _ => false) =
        (match p.rotate180.getQuarter s with
         | some (.crystal _) =>
            (CrystalBond.crystalCluster s p.rotate180).any (fun q => q.dir.isEast) &&
            (CrystalBond.crystalCluster s p.rotate180).any (fun q => q.dir.isWest)
         | _ => false) := by
    rw [getQuarter_rotate180_inv]
    cases p.rotate180.getQuarter s with
    | none => rfl
    | some q =>
        cases q with
        | crystal _ =>
            simp only
            rw [crystalCluster_any_isEast_r180, crystalCluster_any_isWest_r180]
            exact Bool.and_comm ..
        | _ => rfl

/-- l.any (fun q => (q == p) && f q) = (l.any (· == p)) && f p
    BEq が一致する要素の述語を f p に集約する -/
private theorem any_beq_and [BEq α] [LawfulBEq α] (l : List α) (p : α) (f : α → Bool) :
        l.any (fun q => (q == p) && f q) = ((l.any (· == p)) && f p) := by
    induction l with
    | nil => simp
    | cons x xs ih =>
        simp only [List.any_cons]
        rw [ih]
        -- goal: (x == p) && f x || xs.any (· == p) && f p
        --     = ((x == p) || xs.any (· == p)) && f p
        cases hx : (x == p) with
        | false => simp
        | true =>
            have hxp := eq_of_beq hx; subst hxp
            simp [BEq.rfl]

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
    simp only [shatterTargetsOnCut, Shape.layerCount_rotate180,
        CrystalBond.allValid_rotate180_eq]
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
    | nil => simp
    | cons x xs ih =>
        simp only [List.map_cons, List.filter_cons]
        rw [fragile_pred_rotate180]
        cases match x.getQuarter s with | some q => q.isFragile | none => false with
        | true => simp [ih]
        | false => simp [ih]

/-- shatterTargetsOnFall の落下判定述語は r180 で等変 -/
private theorem shatterFallPred_rotate180 (s : Shape) (ps : List QuarterPos)
        (p : QuarterPos) :
        (match p.getQuarter s.rotate180 with
         | some (.crystal _) =>
            (CrystalBond.crystalCluster s.rotate180 p).any (fun qq =>
                ((ps.map QuarterPos.rotate180).filter (fun (rr : QuarterPos) =>
                    match rr.getQuarter s.rotate180 with | some w => w.isFragile | none => false)).any (· == qq))
         | _ => false) =
        (match p.rotate180.getQuarter s with
         | some (.crystal _) =>
            (CrystalBond.crystalCluster s p.rotate180).any (fun qq =>
                (ps.filter (fun (rr : QuarterPos) =>
                    match rr.getQuarter s with | some w => w.isFragile | none => false)).any (· == qq))
         | _ => false) := by
    rw [getQuarter_rotate180_inv]
    cases h : p.rotate180.getQuarter s with
    | none => rfl
    | some q =>
        cases q with
        | crystal _ =>
            simp only
            have h_frag := fragilePositions_map_rotate180 s ps
            suffices h_eq : (fun qq : QuarterPos =>
                    ((ps.map QuarterPos.rotate180).filter (fun (rr : QuarterPos) =>
                        match QuarterPos.getQuarter s.rotate180 rr with | some w => Quarter.isFragile w | none => false)).any (· == qq)) =
                (fun qq : QuarterPos =>
                    (ps.filter (fun (rr : QuarterPos) =>
                        match QuarterPos.getQuarter s rr with | some w => Quarter.isFragile w | none => false)).any (· == qq.rotate180)) by
                rw [h_eq]
                exact crystalCluster_any_rotate180_general s p _ _ (fun _ => rfl)
            funext qq
            rw [h_frag, any_map_rotate180_beq]
        | _ => rfl

/-- shatterTargetsOnFall の any-membership は rotate180 で等変 -/
private theorem shatterTargetsOnFall_any_rotate180 (s : Shape)
        (ps : List QuarterPos) (p : QuarterPos) :
        (shatterTargetsOnFall s.rotate180 (ps.map QuarterPos.rotate180)).any (· == p) =
        (shatterTargetsOnFall s ps).any (· == p.rotate180) := by
    simp only [shatterTargetsOnFall, Shape.layerCount_rotate180,
        CrystalBond.allValid_rotate180_eq]
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
-- 超過レイヤの砖け散り
-- ============================================================

/-- レイヤ上限超過分の象限を落下対象として砖け散り処理を適用する。
    超過レイヤの脆弱結晶が属する結晶結合クラスタ全体が砖け散る -/
def shatterOnTruncate (s : Shape) (maxLayers : Nat) : Shape :=
    let truncatedPositions := (QuarterPos.allValid s).filter fun p =>
        p.layer ≥ maxLayers
    s.shatterOnFall truncatedPositions
end Shape
