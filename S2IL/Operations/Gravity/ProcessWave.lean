-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity.GroundedMono
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.List.Flatten

/-!
# processWave 定義と終端性

`processWave` の定義およびその終端性証明で必要な `waveStep_ngs_strict_bound` を
本ファイルに集約する。従来は `Defs.lean` に `sorry` として置かれていたが、
Gravity 下流の補題（`GroundedMono`）を用いる構成的証明を可能にするため、
依存チェーン後方に移設した（2026-04-21）。

従来 `Equivariance.lean` にあった `processWave_floatingUnits_empty` /
`processWave_rotate180_comm` も `processWave` に依存するため本ファイルに移設。

構造:
- Defs (基本定義)
- Equivariance (等変補題: waveStep まで)
- CommExt (組合せ論補題)
- GroundedMono (grounding 単調性)
- **ProcessWave** (本ファイル: processWave 定義 + 終端性 + rotate180 等変)
- Facade (process rotate180/rotateCW facade)
-/

namespace Gravity

set_option maxHeartbeats 800000

/-- `waveStep` は `layerCount` を保存する。

    `waveStep_layers_eq` で `(waveStep s).layers = placeLDGroups s sortedSettling obs`
    を得た後、`placeLDGroups_length` に settling FU の位置妥当性
    (`p.layer < obs.length`) と着地距離妥当性 (`landingDistance ≤ p.layer`) を
    供給して `(waveStep s).layers.length = obs.length = s.layerCount` を導く。

    用途: `waveStep_ngs_strict_bound` の Step C0 — `allValid (waveStep s) = allValid s`
    を経由するために必要 (QuarterPos.allValid は `layerCount` にのみ依存)。 -/
theorem waveStep_layerCount_eq (s : Shape) (h : (floatingUnits s).isEmpty = false) :
        (waveStep s).layerCount = s.layerCount := by
    have h_layers := waveStep_layers_eq s h
    simp only at h_layers
    set fus := floatingUnits s with hfus
    set minML := fus.tail.foldl (fun acc u => min acc u.minLayer)
        (fus.head?.map FallingUnit.minLayer |>.getD 0) with hminML
    set settling := fus.filter (fun u => u.minLayer == minML) with hsettling
    set settlingPos := settling.flatMap FallingUnit.positions with hspos
    set obs := (s.clearPositions settlingPos).layers with hobs
    set sortedSettling := settling.mergeSort
        (fun a b => landingDistance a obs ≤ landingDistance b obs) with hsorted
    have h_obs_len : obs.length = s.layerCount := by
        show (s.clearPositions settlingPos).layers.length = s.layerCount
        exact Shape.layerCount_clearPositions s settlingPos
    have h_sorted_sub : ∀ u ∈ sortedSettling, u ∈ floatingUnits s := by
        intro u hu
        have hmem : u ∈ settling := List.mem_mergeSort.mp hu
        exact (List.mem_filter.mp hmem).1
    have h_lt : ∀ u ∈ sortedSettling, ∀ p ∈ u.positions, p.layer < obs.length := by
        intro u hu p hp
        rw [h_obs_len]
        have hfu := h_sorted_sub u hu
        have hpp : ((floatingUnits s).flatMap FallingUnit.positions).any (· == p) = true := by
            apply List.any_eq_true.mpr
            exact ⟨p, List.mem_flatMap.mpr ⟨u, hfu, hp⟩, by simp⟩
        exact (floatingUnits_positions_getQuarter s p hpp).1
    have h_le : ∀ u ∈ sortedSettling, ∀ p ∈ u.positions, landingDistance u obs ≤ p.layer := by
        intro u hu p hp
        exact le_trans (landingDistance_le_minLayer u obs) (minLayer_le_layer hp u.minLayer le_rfl)
    show (waveStep s).layers.length = s.layerCount
    rw [h_layers, ← h_obs_len]
    exact placeLDGroups_length s sortedSettling obs h_lt h_le

/-- Sub-lemma #7 (`waveStep_grounding_mono`): waveStep の grounding 単調性。

    `obs_shape := s.clearPositions settlingPos`（waveStep 内部で obs に相当する shape）の
    接地集合は、waveStep 適用後の shape の接地集合に包含される。

    `Shape.groundedPositions_placeLDGroups_subset` に以下を供給して閉じる:
    - `h_edge_landing`: cluster / pin 着地位置端点での `groundingEdge` 保存
      （cluster は canFormBond 書き込みで保存、pin は `pin_landing_groundingEdge_false_*`
      で vacuous）。**残課題: Step B3b `placeLDGroups_groundingEdge_mono` 未実装**。
    - `h_seed_landing`: cluster / pin 着地位置 layer-0 での非空象限存在
      （`placeLDGroups_landing_nonEmpty` で一括処理済み、2026-04-22 第38報）。

    本証明では `h_seed_landing` を `placeLDGroups_landing_nonEmpty` 一本で閉じ、
    残る `h_edge_landing` のみを sorry として保留する（Step B3b 完了で解消）。 -/
private theorem waveStep_grounding_mono (s : Shape)
        (h : (floatingUnits s).isEmpty = false) :
        let fus := floatingUnits s
        let minML := fus.tail.foldl (fun acc u => min acc u.minLayer)
            (fus.head?.map FallingUnit.minLayer |>.getD 0)
        let settling := fus.filter fun u => u.minLayer == minML
        let settlingPos := settling.flatMap FallingUnit.positions
        groundedPositions (s.clearPositions settlingPos) ⊆ groundedPositions (waveStep s) := by
    set fus := floatingUnits s with hfus
    set minML := fus.tail.foldl (fun acc u => min acc u.minLayer)
        (fus.head?.map FallingUnit.minLayer |>.getD 0) with hminML
    set settling := fus.filter (fun u => u.minLayer == minML) with hsettling
    set settlingPos := settling.flatMap FallingUnit.positions with hspos
    set obs_shape := s.clearPositions settlingPos with hobs_shape
    set obs := obs_shape.layers with hobs
    set sortedSettling := settling.mergeSort
        (fun a b => landingDistance a obs ≤ landingDistance b obs) with hsorted
    have h_obs_layers : obs_shape.layers = obs := rfl
    have h_layers : (waveStep s).layers = placeLDGroups s sortedSettling obs :=
        waveStep_layers_eq s h
    have h_sub : ∀ u ∈ sortedSettling, u ∈ floatingUnits s := by
        intro u hu
        have hmem : u ∈ settling := List.mem_mergeSort.mp hu
        exact (List.mem_filter.mp hmem).1
    -- settling FU の minLayer は全て minML に等しい（filter 条件から直接）
    have h_ml_eq : ∀ u ∈ sortedSettling, u.minLayer = minML := by
        intro u hu
        have hmem : u ∈ settling := List.mem_mergeSort.mp hu
        exact beq_iff_eq.mp (List.mem_filter.mp hmem).2
    -- minML は floatingUnits s 内で最小の minLayer。foldl_min_fu_* を用いて示す。
    have h_min_fu : ∀ v ∈ floatingUnits s, v.minLayer ≥ minML := by
        intro v hv
        by_cases hempty : fus = []
        · rw [← hfus] at hv; rw [hempty] at hv; simp at hv
        · obtain ⟨hd, tl, htl⟩ := List.exists_cons_of_ne_nil hempty
          have heq : minML = tl.foldl (fun acc u => min acc u.minLayer) hd.minLayer := by
              simp only [hminML, htl, List.tail_cons, List.head?_cons, Option.map_some,
                  Option.getD_some]
          rw [heq]
          rw [← hfus] at hv; rw [htl] at hv
          rcases List.mem_cons.mp hv with heq2 | hmem
          · rw [heq2]; exact foldl_min_fu_le_init tl hd.minLayer
          · exact foldl_min_fu_le_mem tl hd.minLayer hmem
    -- settlingPos の全位置は layer ≥ minML を満たす。
    have h_ps_layer : ∀ q ∈ settlingPos, q.layer ≥ minML := by
        intro q hq
        rw [List.mem_flatMap] at hq
        obtain ⟨u, hu_s, hq_u⟩ := hq
        have hu_eq : u.minLayer = minML := beq_iff_eq.mp (List.mem_filter.mp hu_s).2
        have hle := minLayer_le_layer hq_u u.minLayer le_rfl
        omega
    refine Shape.groundedPositions_placeLDGroups_subset s sortedSettling obs
        obs_shape (waveStep s) h_obs_layers h_layers ?_ ?_
    · -- h_edge_landing: Step B3b の標準化補題
      -- `placeLDGroups_landing_groundingEdge_mono` に委譲
      -- （GroundedMono.lean 末尾、sorry scaffold）。
      --
      -- 2026-04-23 第44報: sorry をこの scaffold 補題に一本化し、
      -- `waveStep_grounding_mono` 本体からは解消した。
      -- `h_min_fu` / `h_ps_layer` は `h_ml_eq` で新補題の要求形に整形する。
      intro a b h_edge h_landing
      have h_min_fu' : ∀ u ∈ sortedSettling, ∀ v ∈ floatingUnits s,
              u.minLayer ≤ v.minLayer := by
          intro u hu v hv
          rw [h_ml_eq u hu]; exact h_min_fu v hv
      have h_ps_layer' : ∀ q ∈ settlingPos, ∀ u ∈ sortedSettling,
              u.minLayer ≤ q.layer := by
          intro q hq u hu
          rw [h_ml_eq u hu]; exact h_ps_layer q hq
      -- h_nodup: sortedSettling.flatMap positions の Nodup を導出
      -- (floatingUnits s).flatMap positions は floatingUnits_flatMap_positions_nodup で Nodup
      -- sortedSettling = settling.mergeSort, settling = (floatingUnits s).filter ... なので
      -- sortedSettling は floatingUnits s のサブリストの permutation
      have h_nodup : (sortedSettling.flatMap FallingUnit.positions).Nodup := by
          have h_fu_nd : ((floatingUnits s).flatMap FallingUnit.positions).Nodup :=
              floatingUnits_flatMap_positions_nodup s
          have h_settling_sl : settling.Sublist (floatingUnits s) :=
              List.filter_sublist
          have h_settling_nd :
                  (settling.flatMap FallingUnit.positions).Nodup :=
              h_fu_nd.sublist (h_settling_sl.flatMap _)
          have h_perm : sortedSettling.Perm settling :=
              List.mergeSort_perm settling _
          have h_perm_fm :
                  (sortedSettling.flatMap FallingUnit.positions).Perm
                    (settling.flatMap FallingUnit.positions) :=
              h_perm.flatMap (fun _ _ => List.Perm.refl _)
          exact h_perm_fm.nodup_iff.mpr h_settling_nd
      -- h_sorted: sortedSettling は landingDistance · obs 昇順で整列済
      -- `List.sorted_mergeSort` は total preorder ≤ から Pairwise 昇順を返す。
      have h_sorted : sortedSettling.Pairwise
              (fun a b => landingDistance a obs ≤ landingDistance b obs) := by
          have h_trans : ∀ (a b c : FallingUnit),
                  (fun a b => decide (landingDistance a obs ≤ landingDistance b obs))
                      a b = true →
                  (fun a b => decide (landingDistance a obs ≤ landingDistance b obs))
                      b c = true →
                  (fun a b => decide (landingDistance a obs ≤ landingDistance b obs))
                      a c = true := by
              intro a b c hab hbc
              simp only [decide_eq_true_eq] at hab hbc ⊢; exact le_trans hab hbc
          have h_total : ∀ (a b : FallingUnit),
                  (decide (landingDistance a obs ≤ landingDistance b obs)
                      || decide (landingDistance b obs ≤ landingDistance a obs)) = true := by
              intro a b
              rcases le_total (landingDistance a obs) (landingDistance b obs) with h | h
              · simp [h]
              · simp [h]
          have h := List.pairwise_mergeSort (le := fun a b =>
              decide (landingDistance a obs ≤ landingDistance b obs)) h_trans h_total settling
          -- `h` : Pairwise (fun a b => (decide (…)) = true) (settling.mergeSort …)
          -- 目標: Pairwise (fun a b => landingDistance a obs ≤ …)
          refine h.imp ?_
          intro a b hab
          exact decide_eq_true_eq.mp hab
      exact placeLDGroups_landing_groundingEdge_mono s sortedSettling
          settlingPos h_sub h_min_fu' h_ps_layer' h_nodup h_sorted obs_shape (waveStep s)
          h_obs_layers h_layers a b h_edge h_landing
    · -- h_seed_landing: `placeLDGroups_landing_nonEmpty` で一括処理。
      intro p h_l0 h_in
      have h_ne : QuarterPos.getDir ((placeLDGroups s sortedSettling obs).getD p.layer
              Layer.empty) p.dir ≠ Quarter.empty :=
          placeLDGroups_landing_nonEmpty s sortedSettling obs h_sub p.layer p.dir h_in
      have h_ne' : QuarterPos.getDir ((waveStep s).layers.getD p.layer Layer.empty) p.dir
              ≠ Quarter.empty := by rw [h_layers]; exact h_ne
      have h_lt : p.layer < (waveStep s).layers.length := by
          by_contra hle
          push Not at hle
          have hnone : (waveStep s).layers[p.layer]? = none := List.getElem?_eq_none hle
          have hd : (waveStep s).layers.getD p.layer Layer.empty = Layer.empty := by
              rw [List.getD_eq_getElem?_getD, hnone]; rfl
          rw [hd] at h_ne'
          exact h_ne' (by cases p.dir <;> rfl)
      have h_getD : (waveStep s).layers.getD p.layer Layer.empty =
              (waveStep s).layers[p.layer] :=
          (List.getElem_eq_getD Layer.empty).symm
      refine ⟨QuarterPos.getDir (waveStep s).layers[p.layer] p.dir, ?_, ?_⟩
      · unfold QuarterPos.getQuarter
        rw [List.getElem?_eq_getElem h_lt]
      · have hq := h_ne'
        rw [h_getD] at hq
        generalize QuarterPos.getDir (waveStep s).layers[p.layer] p.dir = q at hq
        cases q <;> first | rfl | (exfalso; exact hq rfl)

/-- S1 strict-bound form: `NGS(waveStep s) + 1 ≤ NGS(s)`。
    これは厳密減少 `<` と同値だが、加法形は induction / telescoping 引数と
    相性が良く、今後の証明拡張（Sub-lemma #5/#6/#7 合成）に対する
    自然なアンカーとなる。

    証明構造 (Telescoping Sum):
    1. NGS(s) = NGS(obs) + Σ_{settling} ngsWeight(s, p)          [nonGroundedLayerSum_clear_add]
    2. NGS(s') ≤ NGS(obs) + Σ_{landing ∩ empty in obs} (p.layer + 1)  [waveStep_grounding_mono]
    3. Σ landing_weight + |settling|·d ≤ Σ settling_weight         [placeLDGroupsLandings_sum_succ_le]
    4. |settling|·d ≥ 1                                            [d ≥ 1, |settling| ≥ 1]
    5. 結合: NGS(s') + 1 ≤ NGS(s)

    計算検証: 2L/3L/4L 全列挙テスト + 10L 反例形状で確認済み

    構成的証明 (Telescoping Sum):
    waveStep_grounding_mono と placeLDGroupsLandings_sum_succ_le を接続。 -/
private theorem waveStep_ngs_strict_bound (s : Shape)
        (h : (floatingUnits s).isEmpty = false) :
        nonGroundedLayerSum (waveStep s) + 1 ≤ nonGroundedLayerSum s := by
    have h_gm := waveStep_grounding_mono s h
    simp only at h_gm
    set fus := floatingUnits s with hfus
    set minML := fus.tail.foldl (fun acc u => min acc u.minLayer)
        (fus.head?.map FallingUnit.minLayer |>.getD 0) with hminML
    set settling := fus.filter (fun u => u.minLayer == minML) with hsettling
    set settlingPos := settling.flatMap FallingUnit.positions with hspos
    set obs_shape := s.clearPositions settlingPos with hobs_shape
    set obs := obs_shape.layers with hobs
    set sortedSettling := settling.mergeSort
        (fun a b => landingDistance a obs ≤ landingDistance b obs) with hsorted
    set landings := placeLDGroupsLandings s sortedSettling obs with hlandings
    have h_layers : (waveStep s).layers = placeLDGroups s sortedSettling obs := waveStep_layers_eq s h
    have h_lc : (waveStep s).layerCount = s.layerCount := waveStep_layerCount_eq s h
    have h_obs_lc : obs_shape.layerCount = s.layerCount := Shape.layerCount_clearPositions s settlingPos
    have h_av_eq : QuarterPos.allValid (waveStep s) = QuarterPos.allValid s :=
        allValid_eq_of_layerCount h_lc
    have h_obs_layers : obs_shape.layers = obs := rfl
    have h_spos_valid : ∀ p ∈ settlingPos, p.layer < s.layerCount := fun p hp => by
        rw [List.mem_flatMap] at hp; obtain ⟨u, hu, hup⟩ := hp
        exact (floatingUnits_positions_getQuarter s p (List.any_eq_true.mpr ⟨p, List.mem_flatMap.mpr
            ⟨u, (List.mem_filter.mp hu).1, hup⟩, BEq.rfl⟩)).1
    have h_spos_ngrnd : ∀ p ∈ settlingPos, p ∉ groundedPositions s := fun p hp => by
        rw [List.mem_flatMap] at hp; obtain ⟨u, hu, hup⟩ := hp
        exact settling_positions_nongrounded s hu hup
    have h_spos_nodup : settlingPos.Nodup :=
        List.Sublist.flatMap (List.filter_sublist (l := fus)) _ |>.nodup
            (floatingUnits_flatMap_positions_nodup s)
    have h_spos_in_fus : ∀ p ∈ settlingPos,
            ((floatingUnits s).flatMap FallingUnit.positions).any (· == p) = true := fun p hp => by
        rw [List.mem_flatMap] at hp; obtain ⟨u, hu, hup⟩ := hp
        exact List.any_eq_true.mpr ⟨p, List.mem_flatMap.mpr
            ⟨u, (List.mem_filter.mp hu).1, hup⟩, BEq.rfl⟩
    set L_set := (QuarterPos.allValid s).filter (fun p => settlingPos.any (· == p)) with hL_set
    have h_clear_add : nonGroundedLayerSum s = nonGroundedLayerSum obs_shape
            + (L_set.map (ngsWeight s)).sum :=
        nonGroundedLayerSum_clear_add s settlingPos h_spos_ngrnd h_spos_valid
    have h_L_set_wt : (L_set.map (ngsWeight s)) = L_set.map (fun p => p.layer + 1) := by
        apply List.map_congr_left; intro p hp
        have hp_mem : settlingPos.any (· == p) = true := (List.mem_filter.mp hp).2
        rw [List.any_eq_true] at hp_mem
        obtain ⟨x, hx_mem, hxp⟩ := hp_mem
        exact ngsWeight_eq_layer_succ_of_mem_floatingUnits_positions s p
            (h_spos_in_fus p ((eq_of_beq hxp) ▸ hx_mem))
    have h_L_perm : L_set.Perm settlingPos := by
        apply (List.perm_ext_iff_of_nodup ((allValid_nodup s).filter _) h_spos_nodup).mpr
        intro q; constructor
        · intro hq
          have := (List.mem_filter.mp hq).2
          rw [List.any_eq_true] at this; obtain ⟨x, hx, hxq⟩ := this
          rwa [show x = q from eq_of_beq hxq] at hx
        · intro hq
          apply List.mem_filter.mpr
          refine ⟨?_, List.any_eq_true.mpr ⟨q, hq, BEq.rfl⟩⟩
          have := (allValid_any_iff_layer' s q).mpr (h_spos_valid q hq)
          rw [List.any_eq_true] at this; obtain ⟨x, hx, hxq⟩ := this
          rwa [show x = q from eq_of_beq hxq] at hx
    have h_sorted_perm : (sortedSettling.flatMap FallingUnit.positions).Perm settlingPos :=
        (List.mergeSort_perm settling _).flatMap (fun _ _ => List.Perm.refl _)
    have h_ngs_le : ∀ p : QuarterPos, ngsWeight (waveStep s) p ≤ p.layer + 1 := by
        intro p; unfold ngsWeight
        cases p.getQuarter (waveStep s) with
        | none => simp
        | some q => dsimp only; split <;> omega
    have h_pw : ∀ p ∈ QuarterPos.allValid s,
            ngsWeight (waveStep s) p ≤ ngsWeight obs_shape p
                + (if landings.any (· == (p.layer, p.dir)) then p.layer + 1 else 0) := by
        intro p hp
        have h_p_lt_obs : p.layer < obs_shape.layerCount := by
            rw [h_obs_lc]; exact allValid_mem_layer_lt hp
        by_cases h_in : landings.any (· == (p.layer, p.dir)) = true
        · simp only [h_in, ite_true]; have := h_ngs_le p; omega
        · simp only [Bool.not_eq_true] at h_in
          simp only [h_in, Bool.false_eq_true, ite_false, Nat.add_zero]
          have h_not_mem : (p.layer, p.dir) ∉ landings := fun hin => by
              have : landings.any (· == (p.layer, p.dir)) = true :=
                  List.any_eq_true.mpr ⟨(p.layer, p.dir), hin, BEq.rfl⟩
              rw [this] at h_in; simp at h_in
          exact ngsWeight_placeLDGroups_of_ne_le s sortedSettling obs obs_shape (waveStep s)
              h_obs_layers h_layers h_gm p h_p_lt_obs h_not_mem
    have h_ws_ngs : nonGroundedLayerSum (waveStep s) =
            ((QuarterPos.allValid s).map (ngsWeight (waveStep s))).sum := by
        rw [nonGroundedLayerSum_eq_sum, h_av_eq]
    have h_obs_av_eq : QuarterPos.allValid obs_shape = QuarterPos.allValid s :=
        allValid_eq_of_layerCount h_obs_lc
    have h_obs_ngs : nonGroundedLayerSum obs_shape =
            ((QuarterPos.allValid s).map (ngsWeight obs_shape)).sum := by
        rw [nonGroundedLayerSum_eq_sum, h_obs_av_eq]
    have h_sum_le : ((QuarterPos.allValid s).map (ngsWeight (waveStep s))).sum ≤
            ((QuarterPos.allValid s).map (fun p => ngsWeight obs_shape p
                + (if landings.any (· == (p.layer, p.dir)) then p.layer + 1 else 0))).sum := by
        apply List.sum_le_sum
        intro p hp
        exact h_pw p hp
    have h_split : ((QuarterPos.allValid s).map (fun p => ngsWeight obs_shape p
                + (if landings.any (· == (p.layer, p.dir)) then p.layer + 1 else 0))).sum =
            ((QuarterPos.allValid s).map (ngsWeight obs_shape)).sum +
            (((QuarterPos.allValid s).filter (fun p => landings.any (· == (p.layer, p.dir)))).map
                (fun p => p.layer + 1)).sum := by
        rw [sum_map_add]; congr 1
        exact sum_map_ite_eq_sum_filter _ _ _
    have h_land_bd : (((QuarterPos.allValid s).filter
                (fun p => landings.any (· == (p.layer, p.dir)))).map (fun p => p.layer + 1)).sum
            ≤ (landings.map (fun ld => ld.1 + 1)).sum :=
        landing_sum_allValid_le s landings
    have h_pLDL_bd : (landings.map (fun ld => ld.1 + 1)).sum + 1 ≤
            ((sortedSettling.flatMap FallingUnit.positions).map (fun p => p.layer + 1)).sum := by
        have h_ml : ∀ u ∈ sortedSettling, u.minLayer ≥ 1 := fun u hu =>
            floatingUnits_minLayer_ge_one s u (List.mem_filter.mp ((List.mem_mergeSort).mp hu)).1
        have h_pne : ∀ u ∈ sortedSettling, u.positions ≠ [] := fun u hu =>
            floatingUnits_positions_ne_nil s u (List.mem_filter.mp ((List.mem_mergeSort).mp hu)).1
        have h_ne : sortedSettling ≠ [] := by
            intro heq
            apply settling_nonempty fus h
            have hp : sortedSettling.Perm settling := List.mergeSort_perm settling _
            rw [heq] at hp
            exact hp.symm.eq_nil
        exact placeLDGroupsLandings_sum_succ_le s sortedSettling obs h_ne h_ml h_pne
    have h_L_sum_eq : (L_set.map (fun p => p.layer + 1)).sum
            = ((sortedSettling.flatMap FallingUnit.positions).map (fun p => p.layer + 1)).sum := by
        have h1 : (L_set.map (fun p : QuarterPos => p.layer + 1)).sum
                = (settlingPos.map (fun p : QuarterPos => p.layer + 1)).sum :=
            List.Perm.sum_eq (h_L_perm.map _)
        have h2 : ((sortedSettling.flatMap FallingUnit.positions).map
                    (fun p : QuarterPos => p.layer + 1)).sum
                = (settlingPos.map (fun p : QuarterPos => p.layer + 1)).sum :=
            List.Perm.sum_eq (h_sorted_perm.map _)
        rw [h1, ← h2]
    rw [h_ws_ngs]
    have h_clear_add' : nonGroundedLayerSum s = nonGroundedLayerSum obs_shape
            + (L_set.map (fun p => p.layer + 1)).sum := h_L_set_wt ▸ h_clear_add
    omega

/-- waveStep は nonGroundedLayerSum を厳密に減少させる。
    `waveStep_ngs_strict_bound` の `+ 1 ≤` 形式からの算術的帰結。

    計算検証: 2L/3L/4L 全列挙テスト + 10L 反例形状で確認済み -/
theorem waveStep_nonGroundedLayerSum_lt (s : Shape)
        (h : (floatingUnits s).isEmpty = false) :
        nonGroundedLayerSum (waveStep s) < nonGroundedLayerSum s := by
    have := waveStep_ngs_strict_bound s h
    omega

/-- 波動モデルによる反復落下処理。
    各波で最小 minLayer の浮遊単位をすべて着地させ、浮遊単位がなくなるまで繰り返す -/
def processWave (s : Shape) : Shape :=
    if (floatingUnits s).isEmpty then s
    else processWave (waveStep s)
  termination_by nonGroundedLayerSum s
  decreasing_by
    rename_i h_ne
    simp only [Bool.not_eq_true] at h_ne
    exact waveStep_nonGroundedLayerSum_lt s h_ne

/-- processWave の出力は浮遊単位が空（安定状態）。
    根拠: processWave は nonGroundedLayerSum が 0 になるまで反復するため、
    返値は必ず floatingUnits = [] を満たす -/
theorem processWave_floatingUnits_empty (s : Shape) :
        (floatingUnits (processWave s)) = [] := by
    suffices h : ∀ n (t : Shape), nonGroundedLayerSum t ≤ n →
            floatingUnits (processWave t) = [] from
        h _ s le_rfl
    intro n
    induction n with
    | zero =>
        intro t ht
        have h_zero : nonGroundedLayerSum t = 0 := Nat.le_zero.mp ht
        have h_ie : (floatingUnits t).isEmpty = true :=
            nonGroundedLayerSum_zero_fus_empty t h_zero
        conv_lhs => rw [show processWave t = t from by
            conv_lhs => unfold processWave; simp only [h_ie, ↓reduceIte]]
        exact List.isEmpty_iff.mp h_ie
    | succ n ih =>
        intro t ht
        cases h : (floatingUnits t).isEmpty with
        | true =>
            conv_lhs => rw [show processWave t = t from by
                conv_lhs => unfold processWave; simp only [h, ↓reduceIte]]
            exact List.isEmpty_iff.mp h
        | false =>
            conv_lhs => rw [show processWave t = processWave (waveStep t) from by
                conv_lhs => unfold processWave; simp only [h, Bool.false_eq_true, ↓reduceIte]]
            exact ih (waveStep t) (by
                have := waveStep_nonGroundedLayerSum_lt t h; omega)

/-- processWave は rotate180 で等変である（waveStep_rotate180_comm を前提） -/
theorem processWave_rotate180_comm (s : Shape) :
        processWave s.rotate180 = (processWave s).rotate180 := by
    suffices h : ∀ n (t : Shape), nonGroundedLayerSum t ≤ n →
            processWave t.rotate180 = (processWave t).rotate180 from
        h _ s le_rfl
    intro n
    induction n with
    | zero =>
        intro t ht
        have h_zero : nonGroundedLayerSum t = 0 := Nat.le_zero.mp ht
        have h_empty : (floatingUnits t).isEmpty = true :=
            nonGroundedLayerSum_zero_fus_empty t h_zero
        have h_r_empty : (floatingUnits t.rotate180).isEmpty = true := by
            rw [← floatingUnits_isEmpty_rotate180]; exact h_empty
        have lhs_eq : processWave t.rotate180 = t.rotate180 := by
            conv_lhs => unfold processWave
            simp only [h_r_empty, ↓reduceIte]
        have rhs_eq : processWave t = t := by
            conv_lhs => unfold processWave
            simp only [h_empty, ↓reduceIte]
        rw [lhs_eq, rhs_eq]
    | succ n ih =>
        intro t ht
        cases h : (floatingUnits t).isEmpty with
        | true =>
            have h_r : (floatingUnits t.rotate180).isEmpty = true := by
                rw [← floatingUnits_isEmpty_rotate180]; exact h
            have lhs_eq : processWave t.rotate180 = t.rotate180 := by
                conv_lhs => unfold processWave
                simp only [h_r, ↓reduceIte]
            have rhs_eq : processWave t = t := by
                conv_lhs => unfold processWave
                simp only [h, ↓reduceIte]
            rw [lhs_eq, rhs_eq]
        | false =>
            have h_r : (floatingUnits t.rotate180).isEmpty = false := by
                rw [← floatingUnits_isEmpty_rotate180]; exact h
            have lhs_eq : processWave t.rotate180 = processWave (waveStep t.rotate180) := by
                conv_lhs => unfold processWave
                simp only [h_r, Bool.false_eq_true, ↓reduceIte]
            have rhs_eq : processWave t = processWave (waveStep t) := by
                conv_lhs => unfold processWave
                simp only [h, Bool.false_eq_true, ↓reduceIte]
            rw [lhs_eq, rhs_eq, waveStep_rotate180_comm t]
            exact ih (waveStep t)
                (by have := waveStep_nonGroundedLayerSum_lt t h; omega)

-- ============================================================
-- 落下処理 (Gravity)
-- ============================================================

/-- 落下処理のメインロジック（波動モデル版）。
    浮遊単位がなくなるまで最小 minLayer FU を波ごとに着地させ、最後に正規化する -/
def process (s : Shape) : Option Shape :=
    (processWave s).normalize

/-- floatingUnits が空のシェイプでは process は normalize と等しい -/
theorem process_of_isEmpty_floatingUnits (s : Shape)
        (h : (floatingUnits s).isEmpty = true) : process s = s.normalize := by
    simp only [process]
    unfold processWave
    simp only [h, ↓reduceIte]

end Gravity
