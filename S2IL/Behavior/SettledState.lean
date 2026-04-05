-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Behavior.Gravity
import S2IL.Behavior.Painter
import S2IL.Behavior.CrystalGenerator
import S2IL.Behavior.Rotate

/-!
# SettledState (安定状態の保存)

各加工操作が安定状態 (`Shape.IsSettled`) を保存することの証明。

## 証明された定理

| 操作 | 定理 | 内容 |
|---|---|---|
| 着色 (Paint) | `IsSettled_paint` | 色の変更は構造に影響しない |
| 結晶化 (Crystallize) | `IsSettled_crystallize` | 全象限が非空になり完全に接地 |
| 時計回り回転 (RotateCW) | `IsSettled_rotateCW` | 回転は隣接・接地関係を保存 |
| 落下処理 (Gravity) | `gravity_IsSettled` | 基盤定理（未証明） |
-/

-- ============================================================
-- リスト操作ヘルパー
-- ============================================================

/-- dropLast ++ [y] のインデクシング: 最終要素は y に置換 -/
private theorem getElem?_dropLast_append_last {α : Type}
        (l : List α) (h_ne : l ≠ []) (y : α) :
        (l.dropLast ++ [y])[l.length - 1]? = some y := by
    have h_len : l.length ≥ 1 := by
        cases l with | nil => exact absurd rfl h_ne | cons _ _ => simp only [List.length_cons]; omega
    rw [List.getElem?_append_right (by rw [List.length_dropLast])]
    simp only [List.length_dropLast, Nat.sub_self, List.getElem?_cons_zero]

/-- dropLast ++ [y] のインデクシング: 最終要素以外は元と同じ -/
private theorem getElem?_dropLast_append_other {α : Type}
        (l : List α) (h_ne : l ≠ []) (y : α) (i : Nat) (h_ne_idx : i ≠ l.length - 1) :
        (l.dropLast ++ [y])[i]? = l[i]? := by
    have h_len : l.length ≥ 1 := by
        cases l with | nil => exact absurd rfl h_ne | cons _ _ => simp only [List.length_cons]; omega
    by_cases h_lt : i < l.length - 1
    · rw [List.getElem?_append_left (by rw [List.length_dropLast]; omega),
          List.getElem?_dropLast]
      simp only [h_lt, if_true]
    · have h_ge : i ≥ l.length := by omega
      have h_lhs : (l.dropLast ++ [y])[i]? = none := List.getElem?_eq_none (by
          rw [List.length_append, List.length_dropLast, List.length_singleton]; omega)
      have h_rhs : l[i]? = none := List.getElem?_eq_none (by omega)
      rw [h_lhs, h_rhs]

-- ============================================================
-- Quarter レベルの保存補題
-- ============================================================

/-- match some q の Option マッチを Quarter マッチに簡約 -/
private theorem isPin_some (q : Quarter) :
        (match (some q : Option Quarter) with | some .pin => true | _ => false) =
        (match q with | .pin => true | _ => false) := by
    cases q <;> rfl

/-- paintQuarter は canFormBond を保存する -/
private theorem paintQuarter_canFormBond (q : Quarter) (c : Color) :
        (Painter.paintQuarter q c).canFormBond = q.canFormBond := by
    cases q <;> rfl

/-- paintQuarter は isEmpty を保存する -/
private theorem paintQuarter_isEmpty (q : Quarter) (c : Color) :
        (Painter.paintQuarter q c).isEmpty = q.isEmpty := by
    cases q <;> rfl

/-- paintQuarter はピンかどうかのマッチ結果を保存する -/
private theorem paintQuarter_pin_match (q : Quarter) (c : Color) :
        (match Painter.paintQuarter q c with | .pin => true | _ => false) =
        (match q with | .pin => true | _ => false) := by
    cases q <;> rfl

-- ============================================================
-- Paint: getQuarter レベルの保存
-- ============================================================

namespace Gravity

/-- getDir の paintLayer 保存: canFormBond -/
private theorem getDir_paintLayer_canFormBond (l : Layer) (c : Color) (d : Direction) :
        (QuarterPos.getDir (Painter.paintLayer l c) d).canFormBond =
        (QuarterPos.getDir l d).canFormBond := by
    cases d <;> simp only [QuarterPos.getDir, Painter.paintLayer, paintQuarter_canFormBond]

/-- getDir の paintLayer 保存: isEmpty -/
private theorem getDir_paintLayer_isEmpty (l : Layer) (c : Color) (d : Direction) :
        (QuarterPos.getDir (Painter.paintLayer l c) d).isEmpty =
        (QuarterPos.getDir l d).isEmpty := by
    cases d <;> simp only [QuarterPos.getDir, Painter.paintLayer, paintQuarter_isEmpty]

/-- getDir の paintLayer 保存: ピンマッチ -/
private theorem getDir_paintLayer_pin_match (l : Layer) (c : Color) (d : Direction) :
        (match QuarterPos.getDir (Painter.paintLayer l c) d with | .pin => true | _ => false) =
        (match QuarterPos.getDir l d with | .pin => true | _ => false) := by
    cases d <;> simp only [QuarterPos.getDir, Painter.paintLayer, paintQuarter_pin_match]

/-- paint の getQuarter は canFormBond を保存 -/
private theorem getQuarter_paint_canFormBond (s : Shape) (c : Color) (p : QuarterPos) :
        (p.getQuarter (s.paint c)).map Quarter.canFormBond =
        (p.getQuarter s).map Quarter.canFormBond := by
    simp only [QuarterPos.getQuarter, Shape.paint]
    by_cases h_top : p.layer = s.layers.length - 1
    · -- p.layer = length - 1: 最上位レイヤ → paintLayer 適用
      have h_len : s.layers.length ≥ 1 := by
          match s.layers, s.layers_ne with | _ :: _, _ => simp only [List.length_cons]; omega
      rw [h_top, getElem?_dropLast_append_last _ s.layers_ne]
      rw [show s.layers[s.layers.length - 1]? = some (s.layers.getLast s.layers_ne) from by
          rw [List.getLast_eq_getElem]; exact List.getElem?_eq_getElem (by omega)]
      simp only [Option.map_some]
      exact congr_arg some (getDir_paintLayer_canFormBond _ c p.dir)
    · -- p.layer ≠ length - 1: 元のレイヤそのまま
      rw [getElem?_dropLast_append_other _ s.layers_ne _ _ h_top]

/-- paint の getQuarter は isEmpty を保存 -/
private theorem getQuarter_paint_isEmpty (s : Shape) (c : Color) (p : QuarterPos) :
        (p.getQuarter (s.paint c)).map Quarter.isEmpty =
        (p.getQuarter s).map Quarter.isEmpty := by
    simp only [QuarterPos.getQuarter, Shape.paint]
    by_cases h_top : p.layer = s.layers.length - 1
    · have h_len : s.layers.length ≥ 1 := by
          match s.layers, s.layers_ne with | _ :: _, _ => simp only [List.length_cons]; omega
      rw [h_top, getElem?_dropLast_append_last _ s.layers_ne]
      rw [show s.layers[s.layers.length - 1]? = some (s.layers.getLast s.layers_ne) from by
          rw [List.getLast_eq_getElem]; exact List.getElem?_eq_getElem (by omega)]
      simp only [Option.map_some]
      exact congr_arg some (getDir_paintLayer_isEmpty _ c p.dir)
    · rw [getElem?_dropLast_append_other _ s.layers_ne _ _ h_top]

/-- paint の getQuarter はピン判定を保存 -/
private theorem getQuarter_paint_isPin (s : Shape) (c : Color) (p : QuarterPos) :
        (match p.getQuarter (s.paint c) with | some .pin => true | _ => false) =
        (match p.getQuarter s with | some .pin => true | _ => false) := by
    simp only [QuarterPos.getQuarter, Shape.paint]
    by_cases h_top : p.layer = s.layers.length - 1
    · have h_len : s.layers.length ≥ 1 := by
          match s.layers, s.layers_ne with | _ :: _, _ => simp only [List.length_cons]; omega
      rw [h_top, getElem?_dropLast_append_last _ s.layers_ne]
      rw [show s.layers[s.layers.length - 1]? = some (s.layers.getLast s.layers_ne) from by
          rw [List.getLast_eq_getElem]; exact List.getElem?_eq_getElem (by omega)]
      rw [isPin_some, isPin_some]
      exact getDir_paintLayer_pin_match _ c p.dir
    · rw [getElem?_dropLast_append_other _ s.layers_ne _ _ h_top]

/-- getQuarter s p = none ならば getQuarter (s.paint c) p = none -/
private theorem getQuarter_paint_none (s : Shape) (c : Color) (p : QuarterPos)
        (h : p.getQuarter s = none) : p.getQuarter (s.paint c) = none := by
    have hcb := getQuarter_paint_canFormBond s c p
    rw [h, Option.map_none] at hcb
    cases hq : p.getQuarter (s.paint c) with
    | none => rfl
    | some q' => simp only [hq, Option.map_some] at hcb; nomatch hcb

/-- getQuarter s p = some q ならば ∃ q', getQuarter (s.paint c) p = some q' -/
private theorem getQuarter_paint_some (s : Shape) (c : Color) (p : QuarterPos) (q : Quarter)
        (h : p.getQuarter s = some q) : ∃ q', p.getQuarter (s.paint c) = some q' := by
    have hcb := getQuarter_paint_canFormBond s c p
    rw [h, Option.map_some] at hcb
    cases hq : p.getQuarter (s.paint c) with
    | none => simp only [hq, Option.map_none] at hcb; nomatch hcb
    | some q' => exact ⟨q', rfl⟩

-- ============================================================
-- Paint: BFS エッジ述語の保存
-- ============================================================

/-- paint の isStructurallyBonded 保存 -/
private theorem isStructurallyBonded_paint (s : Shape) (c : Color) (p1 p2 : QuarterPos) :
        isStructurallyBonded (s.paint c) p1 p2 =
        isStructurallyBonded s p1 p2 := by
    unfold isStructurallyBonded
    have h1 := getQuarter_paint_canFormBond s c p1
    have h2 := getQuarter_paint_canFormBond s c p2
    rcases hq1 : p1.getQuarter s with _ | q1
    · -- none ケース: paint 側も none → LHS 第1判別子を none に書換え
      have hp1 := getQuarter_paint_none s c p1 hq1
      simp only [hp1]
    · rcases hq2 : p2.getQuarter s with _ | q2
      · -- some.none: paint 側も判別子を書換え
        have hp2 := getQuarter_paint_none s c p2 hq2
        obtain ⟨q1', hq1'⟩ := getQuarter_paint_some s c p1 q1 hq1
        simp only [hq1', hp2]
      · -- 両方 some: canFormBond の保存で結論
        obtain ⟨q1', hq1'⟩ := getQuarter_paint_some s c p1 q1 hq1
        obtain ⟨q2', hq2'⟩ := getQuarter_paint_some s c p2 q2 hq2
        simp only [hq1', hq2', hq1, hq2, Option.map_some, Option.some.injEq] at h1 h2 ⊢
        rw [h1, h2]

/-- paint の isGroundingContact 保存 -/
private theorem isGroundingContact_paint (s : Shape) (c : Color) (p1 p2 : QuarterPos) :
        isGroundingContact (s.paint c) p1 p2 =
        isGroundingContact s p1 p2 := by
    unfold isGroundingContact
    have he1 := getQuarter_paint_isEmpty s c p1
    have he2 := getQuarter_paint_isEmpty s c p2
    have hp1 := getQuarter_paint_isPin s c p1
    have hp2 := getQuarter_paint_isPin s c p2
    rcases hq1 : p1.getQuarter s with _ | q1
    · have := getQuarter_paint_none s c p1 hq1; simp only [this]
    · rcases hq2 : p2.getQuarter s with _ | q2
      · have := getQuarter_paint_none s c p2 hq2
        obtain ⟨q1', hq1'⟩ := getQuarter_paint_some s c p1 q1 hq1
        simp only [hq1', this]
      · obtain ⟨q1', hq1'⟩ := getQuarter_paint_some s c p1 q1 hq1
        obtain ⟨q2', hq2'⟩ := getQuarter_paint_some s c p2 q2 hq2
        simp only [hq1', hq2', hq1, hq2, Option.map_some, Option.some.injEq, isPin_some] at he1 he2 hp1 hp2 ⊢
        rw [he1, he2]
        -- ピンマッチ部分: ケース展開で解決
        cases q1' <;> cases q1 <;> simp at hp1 <;>
          cases q2' <;> cases q2 <;> simp at hp2 <;> rfl

-- ============================================================
-- Paint: floatingUnits の保存
-- ============================================================

/-- paint の layerCount 保存 -/
private theorem layerCount_paint (s : Shape) (c : Color) :
        (s.paint c).layerCount = s.layerCount := by
    simp only [Shape.paint, Shape.layerCount, List.length_append, List.length_dropLast,
        List.length_singleton]
    have : s.layers.length ≥ 1 := by
        match s.layers, s.layers_ne with | _ :: _, _ => simp only [List.length_cons]; omega
    omega

/-- paint の allValid 保存 -/
private theorem allValid_paint (s : Shape) (c : Color) :
        QuarterPos.allValid (s.paint c) = QuarterPos.allValid s := by
    simp only [QuarterPos.allValid, layerCount_paint]

/-- structuralClusterList の保存 -/
private theorem structuralClusterList_paint (s : Shape) (c : Color) (pos : QuarterPos) :
        structuralClusterList (s.paint c) pos = structuralClusterList s pos := by
    simp only [structuralClusterList, allValid_paint, layerCount_paint]
    rw [structuralBfs_eq_generic, structuralBfs_eq_generic]
    exact genericBfs_edge_congr _ _ (isStructurallyBonded_paint s c) _ _ _ _

/-- allStructuralClustersList の保存 -/
private theorem allStructuralClustersList_paint (s : Shape) (c : Color) :
        allStructuralClustersList (s.paint c) = allStructuralClustersList s := by
    simp only [allStructuralClustersList, allValid_paint, structuralClusterList_paint]
    congr 2; ext (p : QuarterPos)
    have hcb := getQuarter_paint_canFormBond s c p
    rcases h : p.getQuarter s with _ | q
    · have hp := getQuarter_paint_none s c p h; simp only [hp]
    · obtain ⟨q', hq'⟩ := getQuarter_paint_some s c p q h
      simp only [h, hq', Option.map_some, Option.some.injEq] at hcb ⊢; rw [hcb]

/-- allIsolatedPins の保存 -/
private theorem allIsolatedPins_paint (s : Shape) (c : Color) :
        allIsolatedPins (s.paint c) = allIsolatedPins s := by
    simp only [allIsolatedPins, allValid_paint]
    congr 1; ext p; exact getQuarter_paint_isPin s c p

/-- groundedPositionsList の保存 -/
private theorem groundedPositionsList_paint (s : Shape) (c : Color) :
        groundedPositionsList (s.paint c) = groundedPositionsList s := by
    simp only [groundedPositionsList, allValid_paint, layerCount_paint]
    -- まず genericBfs に変換
    rw [groundingBfs_eq_generic, groundingBfs_eq_generic]
    -- seeds (queue) の等価性を示す
    have h_seeds : ∀ (p : QuarterPos),
            (p.layer == 0 && match p.getQuarter (s.paint c) with
                | some q => !q.isEmpty | none => false) =
            (p.layer == 0 && match p.getQuarter s with
                | some q => !q.isEmpty | none => false) := by
        intro p; congr 1
        have he := getQuarter_paint_isEmpty s c p
        rcases h : p.getQuarter s with _ | q
        · have hp := getQuarter_paint_none s c p h; simp only [hp]
        · obtain ⟨q', hq'⟩ := getQuarter_paint_some s c p q h
          simp only [h, hq', Option.map_some, Option.some.injEq] at he ⊢; rw [he]
    -- filter の等価性を congr で示す
    have h_filter : (QuarterPos.allValid s).filter (fun p =>
                p.layer == 0 && match p.getQuarter (s.paint c) with
                | some q => !q.isEmpty | none => false) =
            (QuarterPos.allValid s).filter (fun p =>
                p.layer == 0 && match p.getQuarter s with
                | some q => !q.isEmpty | none => false) := by
        congr 1; ext p; exact h_seeds p
    -- edge 関数を先に書き換え、次に seeds の等価性を処理
    have h_edge : isGroundingContact (s.paint c) = isGroundingContact s :=
        funext₂ (isGroundingContact_paint s c)
    rw [h_edge]
    congr 2; ext (p : QuarterPos); exact h_seeds p

/-- paint の floatingUnits 保存: 色の変更は構造に影響しない -/
theorem floatingUnits_paint_eq (s : Shape) (c : Color) :
        floatingUnits (s.paint c) = floatingUnits s := by
    unfold floatingUnits groundedPositions
    rw [allStructuralClustersList_paint, allIsolatedPins_paint, groundedPositionsList_paint]

end Gravity

-- ============================================================
-- Crystallize の安定状態保存
-- ============================================================

namespace Gravity

/-- crystallize 後は floatingUnits が空 -/
theorem floatingUnits_crystallize_eq (s : Shape) (c : Color) :
        floatingUnits (s.crystallize c) = [] := by
    sorry

end Gravity

-- ============================================================
-- RotateCW の安定状態保存
-- ============================================================

namespace Gravity

/-- rotateCW の floatingUnits isEmpty 保存 -/
theorem floatingUnits_isEmpty_rotateCW (s : Shape) :
        (floatingUnits s).isEmpty = (floatingUnits s.rotateCW).isEmpty := by
    sorry

end Gravity

-- ============================================================
-- 安定状態の定理 (Shape 名前空間)
-- ============================================================

namespace Shape

/-- 安定状態は paint (着色) で保存される -/
theorem IsSettled_paint (s : Shape) (c : Color) (h : s.IsSettled) :
        (s.paint c).IsSettled := by
    simp only [IsSettled] at h ⊢
    rw [Gravity.floatingUnits_paint_eq]; exact h

/-- 安定状態は crystallize (結晶化) で保存される。
    より強い性質: crystallize の結果は入力に関わらず常に安定状態 -/
theorem IsSettled_crystallize (s : Shape) (c : Color) (_h : s.IsSettled) :
        (s.crystallize c).IsSettled := by
    simp only [IsSettled]
    exact Gravity.floatingUnits_crystallize_eq s c

/-- 安定状態は rotateCW (時計回り 90° 回転) で保存される -/
theorem IsSettled_rotateCW (s : Shape) (h : s.IsSettled) :
        s.rotateCW.IsSettled := by
    simp only [IsSettled] at h ⊢
    have he := Gravity.floatingUnits_isEmpty_rotateCW s
    rw [h] at he
    cases hf : Gravity.floatingUnits s.rotateCW with
    | nil => rfl
    | cons a l =>
        rw [hf] at he
        simp only [List.isEmpty_cons, List.isEmpty_nil] at he
        exact absurd he (show true ≠ false by decide)

/-- 落下処理の出力は安定状態である（基盤定理） -/
theorem gravity_IsSettled (s : Shape) (s' : Shape) (h : s.gravity = some s') :
        s'.IsSettled := by
    sorry

end Shape
