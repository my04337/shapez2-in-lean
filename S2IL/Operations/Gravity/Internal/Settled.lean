-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity.Internal.Collision

/-!
# S2IL.Operations.Gravity.Internal.Settled

Phase D-10D-5: `Shape.gravity` の出力が `IsSettled` であることの構成的証明骨格。

## 役割

`Internal/Collision.lean` が「BFS / `IsGrounded` 同値」「`floatingUnits` 特徴付け」までを
担うのに対し、本ファイルは **collision foldl の停止性証明** に専念する。

## MECE 構造

| § | 補題 | 役割 |
|---|---|---|
| §6.1 | `Shape.subsumed_by` (関係)            | シェイプ拡張関係（同位置同種 ∨ 新規追加非空）       |
| §6.1 | `IsGroundingEdge.mono`                | エッジは `subsumed_by` で保存される                |
| §6.1 | `IsGrounded.mono`                     | 接地は `subsumed_by` で保存される                  |
| §6.2 | `IsSettled.normalize`                 | `IsSettled` は末尾空除去 (`Shape.normalize`) で保存 |
| §6.3 | `landingCondition_landingDistance_pos`| `landingDistance > 0` から `landingCondition`     |
| §6.4 | `placeUnit_subsumed_by`               | `acc.subsumed_by (placeUnit ... acc u d)`         |
| §6.4 | `placeUnit_grounding`                 | unit の着地像は配置後に grounded                  |
| §6.5 | `foldl_grounded_invariant`            | foldl 後の全有効非空位置が grounded               |
| §6.6 | `gravity_isSettled_collision`         | 主定理（§6.2 + §6.5 の合成）                       |

## 進捗（Phase D-10D-5、複数セッション分割）

| サブ | 状態 |
|---|---|
| §6.1 `IsGroundingEdge.mono` / `IsGrounded.mono` | ✅ D-10D-5a |
| §6.2 `IsSettled.normalize` + 補助群             | ✅ D-10D-5b |
| §6.3 `landingCondition_landingDistance_pos`     | 🚧 sorry（D-10D-5c）|
| §6.4 `placeUnit_subsumed_by` (disjoint 仮定下)  | 🚧 sorry（D-10D-5d、要 R-§6.4 反例検証）|
| §6.4 `placeUnit_grounding`                      | 🚧 sorry（D-10D-5e）|
| §6.5 `foldl_grounded_invariant`                 | 🚧 sorry（D-10D-5f）|
| §6.6 `obs0_isGrounded_of_nonEmpty` + 主定理     | 🚧 sorry（D-10D-5g）|

## 反例検証先行

§4.1 / §4.1.1 の 11 例 + interlock I-1 / I-1' / I-2 / I-3 で
`(Shape.gravity s).isSettled = true` を確認済
（[Scratch/PhaseD10B_GravityCheck.lean] / [Scratch/PhaseD10C_BehaviorCheck.lean]）。
本ファイルの各補題は反例検証済挙動の **証拠** を構成的に与える役割を担う。

## 主リスク（撤退判断材料）

- **R-§6.4**: `placeUnit` の cross-unit 上書き禁止性。`landingCondition` は最小 `d` 探索で
  「自身が床到達 or 直下が `acc` で障害物」を保証するが、unit の着地像 `(p.1 - d, p.2)` 自体が
  `acc` で空であることまでは含まない。`acc` 上に既に他 unit が書き込んだセルへ重なる場合、
  上書きで以前の grounded セルが破壊され得る。
- **代替設計**: 検証に失敗した場合、`landingCondition` を強化して
  「`d` 段下げた全 unit セルが `acc` で空」を追加条件とする (`landingCondition'`)。
-/

namespace S2IL
namespace Gravity
namespace Internal

open S2IL.Gravity
open Relation

/-- §6.1 シェイプ拡張関係: `s` の非空セルは `s'` で同種、`s` の長さは `s'` 以下。 -/
private def Shape.subsumed_by (s s' : Shape) : Prop :=
  s.length ≤ s'.length ∧
  ∀ p : QuarterPos,
    ¬ (QuarterPos.getQuarter s p).isEmpty →
      QuarterPos.getQuarter s' p = QuarterPos.getQuarter s p

/-- §6.1 反射律。 -/
private theorem Shape.subsumed_by.refl (s : Shape) : Shape.subsumed_by s s :=
  ⟨le_rfl, fun _ _ => rfl⟩

/-- §6.1 推移律。 -/
private theorem Shape.subsumed_by.trans
    {s₁ s₂ s₃ : Shape}
    (h₁₂ : Shape.subsumed_by s₁ s₂) (h₂₃ : Shape.subsumed_by s₂ s₃) :
    Shape.subsumed_by s₁ s₃ := by
  refine ⟨h₁₂.1.trans h₂₃.1, ?_⟩
  intro p hp
  have h1 := h₁₂.2 p hp
  have hp' : ¬ (QuarterPos.getQuarter s₂ p).isEmpty := by rw [h1]; exact hp
  have h2 := h₂₃.2 p hp'
  rw [h2, h1]

/-- §6.1 補助: `IsCrystal` は `subsumed_by` で保存される（結晶 ⇒ 非空 ⇒ 同種）。 -/
private theorem IsCrystal.mono_of_subsumed
    {s s' : Shape} (h : Shape.subsumed_by s s')
    {p : QuarterPos} (hc : (QuarterPos.getQuarter s p).IsCrystal) :
    (QuarterPos.getQuarter s' p).IsCrystal := by
  have hne : ¬ (QuarterPos.getQuarter s p).isEmpty := by
    rw [crystal_isEmpty_eq_false hc]; exact Bool.false_ne_true
  rw [h.2 p hne]
  exact hc

/-- §6.1 補助: 非空セルは `subsumed_by` で非空のまま。 -/
private theorem nonEmpty_mono_of_subsumed
    {s s' : Shape} (h : Shape.subsumed_by s s')
    {p : QuarterPos} (hp : ¬ (QuarterPos.getQuarter s p).isEmpty) :
    ¬ (QuarterPos.getQuarter s' p).isEmpty := by
  rw [h.2 p hp]; exact hp

/-- §6.1 補助: 非空かつ非ピンは `subsumed_by` で保存される。 -/
private theorem nonEmpty_nonPin_mono_of_subsumed
    {s s' : Shape} (h : Shape.subsumed_by s s')
    {p : QuarterPos} (hne : ¬ (QuarterPos.getQuarter s p).isEmpty)
    (hnp : QuarterPos.getQuarter s p ≠ Quarter.pin) :
    QuarterPos.getQuarter s' p ≠ Quarter.pin := by
  rw [h.2 p hne]; exact hnp

/-- §6.1 接地エッジは `subsumed_by` で保存される（両端非空が保たれるため）。 -/
private theorem IsGroundingEdge.mono
    {s s' : Shape} (h : Shape.subsumed_by s s')
    {a b : QuarterPos} (he : IsGroundingEdge s a b) :
    IsGroundingEdge s' a b := by
  rcases he with hUp | hBond
  · -- IsUpwardGroundingContact: contact + a.1 ≤ b.1
    obtain ⟨hContact, hLe⟩ := hUp
    refine Or.inl ⟨?_, hLe⟩
    rcases hContact with ⟨hcol, hadj, hneA, hneB⟩ | ⟨hrow, hadj, hneA, hneB, hnpA, hnpB⟩
    · exact Or.inl ⟨hcol, hadj,
        nonEmpty_mono_of_subsumed h hneA, nonEmpty_mono_of_subsumed h hneB⟩
    · exact Or.inr ⟨hrow, hadj,
        nonEmpty_mono_of_subsumed h hneA, nonEmpty_mono_of_subsumed h hneB,
        nonEmpty_nonPin_mono_of_subsumed h hneA hnpA,
        nonEmpty_nonPin_mono_of_subsumed h hneB hnpB⟩
  · -- IsBonded: in-layer or cross-layer; 両端結晶
    refine Or.inr ?_
    rcases hBond with ⟨hrow, hadj, hcA, hcB⟩ | ⟨hlayer, hcol, hcA, hcB⟩
    · exact Or.inl ⟨hrow, hadj,
        IsCrystal.mono_of_subsumed h hcA, IsCrystal.mono_of_subsumed h hcB⟩
    · exact Or.inr ⟨hlayer, hcol,
        IsCrystal.mono_of_subsumed h hcA, IsCrystal.mono_of_subsumed h hcB⟩

/-- §6.1 接地は `subsumed_by` で保存される（layer 0 root + ReflTransGen の lift）。 -/
private theorem IsGrounded.mono
    {s s' : Shape} (h : Shape.subsumed_by s s')
    {p : QuarterPos} (hg : IsGrounded s p) :
    IsGrounded s' p := by
  obtain ⟨p₀, hLayer, hNe, hPath⟩ := hg
  exact ⟨p₀, hLayer, nonEmpty_mono_of_subsumed h hNe,
    Relation.ReflTransGen.mono (fun a b hab => IsGroundingEdge.mono h hab) hPath⟩

/-- §6.2 補助: `normalize` は元シェイプの prefix である（末尾空のみ除去）。 -/
private theorem normalize_isPrefix (t : Shape) : t.normalize <+: t := by
  refine ⟨(List.takeWhile Layer.isEmpty t.reverse).reverse, ?_⟩
  show (List.dropWhile Layer.isEmpty t.reverse).reverse ++
        (List.takeWhile Layer.isEmpty t.reverse).reverse = t
  rw [← List.reverse_append, List.takeWhile_append_dropWhile, List.reverse_reverse]

/-- §6.2 補助: `takeWhile p` の元は `p` を満たす。 -/
private theorem mem_takeWhile_imp {α : Type*} {p : α → Bool} :
    ∀ {xs : List α} {x : α}, x ∈ xs.takeWhile p → p x = true
  | a :: as, x, h => by
      by_cases hp : p a
      · simp [hp] at h
        rcases h with rfl | h
        · exact hp
        · exact mem_takeWhile_imp h
      · simp [hp] at h

/-- §6.2 補助: `t` の非空レイヤインデックスは `t.normalize.length` 未満。 -/
private theorem normalize_length_of_nonEmpty
    (t : Shape) {i : Nat} (hi : i < t.length) (hne : (t[i]'hi).isEmpty = false) :
    i < t.normalize.length := by
  by_contra hcontra
  push_neg at hcontra
  set tail := (List.takeWhile Layer.isEmpty t.reverse).reverse with htail_def
  have htail : t.normalize ++ tail = t := by
    show (List.dropWhile Layer.isEmpty t.reverse).reverse ++
          (List.takeWhile Layer.isEmpty t.reverse).reverse = t
    rw [← List.reverse_append, List.takeWhile_append_dropWhile, List.reverse_reverse]
  have hi_tail : i - t.normalize.length < tail.length := by
    have := hi
    rw [← htail, List.length_append] at this
    omega
  have hi' : i < (t.normalize ++ tail).length := by
    rw [List.length_append]; omega
  have hget : t[i]'hi = tail[i - t.normalize.length]'hi_tail := by
    have h1 : t[i]'hi = (t.normalize ++ tail)[i]'hi' := by
      have heq : t[i]? = (t.normalize ++ tail)[i]? := by rw [htail]
      rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi'] at heq
      exact Option.some.inj heq
    rw [h1]
    exact List.getElem_append_right hcontra
  rw [hget] at hne
  have h_in : tail[i - t.normalize.length]'hi_tail ∈ tail := List.getElem_mem hi_tail
  have h_in_tw : tail[i - t.normalize.length]'hi_tail ∈
      List.takeWhile Layer.isEmpty t.reverse := by
    have hmem_rev : tail[i - t.normalize.length]'hi_tail ∈
        (List.takeWhile Layer.isEmpty t.reverse).reverse := htail_def ▸ h_in
    exact List.mem_reverse.mp hmem_rev
  have hp_true := mem_takeWhile_imp h_in_tw
  rw [hp_true] at hne
  exact absurd hne (by decide)

/-- §6.2 補助: `normalize` の有効位置では `getQuarter` が一致する。 -/
private theorem getQuarter_normalize_eq
    (t : Shape) {p : QuarterPos} (hp : p.1 < t.normalize.length) :
    QuarterPos.getQuarter t p = QuarterPos.getQuarter t.normalize p := by
  obtain ⟨tail, htail⟩ := normalize_isPrefix t
  have hpt : p.1 < t.length :=
    lt_of_lt_of_le hp (List.IsPrefix.length_le ⟨tail, htail⟩)
  have getEq : t[p.1]? = t.normalize[p.1]? := by
    conv_lhs => rw [← htail]
    exact List.getElem?_append_left hp
  unfold QuarterPos.getQuarter
  rw [List.getElem?_eq_getElem hpt, List.getElem?_eq_getElem hp] at getEq
  have getEq' : t[p.1]'hpt = t.normalize[p.1]'hp := Option.some.inj getEq
  simp only [hpt, hp, ↓reduceDIte, getEq']

/-- §6.2 補助: `getQuarter t p` 非空 ⇒ `p.1 < t.length`。 -/
private theorem nonEmpty_imp_layer_lt
    {t : Shape} {p : QuarterPos} (hne : ¬ (QuarterPos.getQuarter t p).isEmpty) :
    p.1 < t.length := by
  by_contra hc
  push_neg at hc
  apply hne
  unfold QuarterPos.getQuarter
  have hnot : ¬ p.1 < t.length := Nat.not_lt.mpr hc
  simp [hnot, Quarter.isEmpty]

/-- §6.2 補助: `getQuarter t p` 非空 ⇒ レイヤ `t[p.1]` も非空。 -/
private theorem nonEmpty_imp_layer_isEmpty_false
    {t : Shape} {p : QuarterPos} (hne : ¬ (QuarterPos.getQuarter t p).isEmpty) :
    (t[p.1]'(nonEmpty_imp_layer_lt hne)).isEmpty = false := by
  have hpt := nonEmpty_imp_layer_lt hne
  -- `(t[p.1] p.2).isEmpty = false` を取り出す
  have hgq : (QuarterPos.getQuarter t p).isEmpty = false := by
    cases h : (QuarterPos.getQuarter t p).isEmpty
    · rfl
    · exact absurd h hne
  have hdir : ((t[p.1]'hpt) p.2).isEmpty = false := by
    have : QuarterPos.getQuarter t p = (t[p.1]'hpt) p.2 := by
      unfold QuarterPos.getQuarter; simp [hpt]
    rw [this] at hgq; exact hgq
  -- p.2 のいずれかの値で or を成立させる
  simp only [Layer.isEmpty, Bool.and_eq_false_iff]
  rcases hp2 : p.2 with ⟨val, hval⟩
  rw [hp2] at hdir
  match val, hval with
  | 0, _ => exact Or.inl (Or.inl (Or.inl hdir))
  | 1, _ => exact Or.inl (Or.inl (Or.inr hdir))
  | 2, _ => exact Or.inl (Or.inr hdir)
  | 3, _ => exact Or.inr hdir

/-- §6.2 補助: `IsGroundingEdge` の両端は s で非空。 -/
private theorem IsGroundingEdge.left_nonEmpty
    {s : Shape} {a b : QuarterPos} (he : IsGroundingEdge s a b) :
    ¬ (QuarterPos.getQuarter s a).isEmpty := by
  rcases he with hUp | hBond
  · rcases hUp.1 with ⟨_, _, hneA, _⟩ | ⟨_, _, hneA, _, _, _⟩ <;> exact hneA
  · rcases hBond with ⟨_, _, hcA, _⟩ | ⟨_, _, hcA, _⟩ <;>
    · intro hempty; rw [crystal_isEmpty_eq_false hcA] at hempty; exact Bool.false_ne_true hempty

/-- §6.2 補助: `IsGroundingEdge` の右端も s で非空。 -/
private theorem IsGroundingEdge.right_nonEmpty
    {s : Shape} {a b : QuarterPos} (he : IsGroundingEdge s a b) :
    ¬ (QuarterPos.getQuarter s b).isEmpty := by
  rcases he with hUp | hBond
  · rcases hUp.1 with ⟨_, _, _, hneB⟩ | ⟨_, _, _, hneB, _, _⟩ <;> exact hneB
  · rcases hBond with ⟨_, _, _, hcB⟩ | ⟨_, _, _, hcB⟩ <;>
    · intro hempty; rw [crystal_isEmpty_eq_false hcB] at hempty; exact Bool.false_ne_true hempty

/-- §6.2 補助: 両端が `t.normalize` 範囲内なら `IsGroundingEdge` は normalize でも成立。 -/
private theorem IsGroundingEdge.of_normalize_range
    {t : Shape} {a b : QuarterPos}
    (ha : a.1 < t.normalize.length) (hb : b.1 < t.normalize.length)
    (he : IsGroundingEdge t a b) :
    IsGroundingEdge t.normalize a b := by
  -- `subsumed_by` を local に構築するのではなく、各分枝で getQuarter 同値を直接適用
  have ha_eq := getQuarter_normalize_eq t ha
  have hb_eq := getQuarter_normalize_eq t hb
  rcases he with hUp | hBond
  · refine Or.inl ⟨?_, hUp.2⟩
    rcases hUp.1 with ⟨hcol, hadj, hneA, hneB⟩ | ⟨hrow, hadj, hneA, hneB, hnpA, hnpB⟩
    · exact Or.inl ⟨hcol, hadj, ha_eq ▸ hneA, hb_eq ▸ hneB⟩
    · exact Or.inr ⟨hrow, hadj, ha_eq ▸ hneA, hb_eq ▸ hneB,
        ha_eq ▸ hnpA, hb_eq ▸ hnpB⟩
  · refine Or.inr ?_
    rcases hBond with ⟨hrow, hadj, hcA, hcB⟩ | ⟨hlayer, hcol, hcA, hcB⟩
    · exact Or.inl ⟨hrow, hadj,
        show (QuarterPos.getQuarter t.normalize a).IsCrystal by rw [← ha_eq]; exact hcA,
        show (QuarterPos.getQuarter t.normalize b).IsCrystal by rw [← hb_eq]; exact hcB⟩
    · exact Or.inr ⟨hlayer, hcol,
        show (QuarterPos.getQuarter t.normalize a).IsCrystal by rw [← ha_eq]; exact hcA,
        show (QuarterPos.getQuarter t.normalize b).IsCrystal by rw [← hb_eq]; exact hcB⟩

/-- §6.2 末尾空除去は IsSettled を保存する。
    path 上の各セルは t で非空 ⇒ `t.normalize` の範囲内 ⇒ edge は両 shape で同等。 -/
private theorem IsSettled.normalize
    {t : Shape} (h : IsSettled t) : IsSettled t.normalize := by
  intro p hp_valid hp_ne
  have hp_lt_norm : p.1 < t.normalize.length :=
    (QuarterPos.mem_allValid t.normalize p).mp hp_valid
  have hp_eq : QuarterPos.getQuarter t p = QuarterPos.getQuarter t.normalize p :=
    getQuarter_normalize_eq t hp_lt_norm
  have hp_ne_t : ¬ (QuarterPos.getQuarter t p).isEmpty := by rw [hp_eq]; exact hp_ne
  have hpt : p.1 < t.length := nonEmpty_imp_layer_lt hp_ne_t
  have hp_valid_t : p ∈ QuarterPos.allValid t :=
    (QuarterPos.mem_allValid t p).mpr hpt
  obtain ⟨p₀, hLayer, hNe₀, hPath⟩ := h p hp_valid_t hp_ne_t
  -- root p₀ の normalize 範囲性
  have hp₀_lt_norm : p₀.1 < t.normalize.length := by
    have hp₀_lt_t := nonEmpty_imp_layer_lt hNe₀
    have hne_idx := nonEmpty_imp_layer_isEmpty_false hNe₀
    exact normalize_length_of_nonEmpty t hp₀_lt_t hne_idx
  -- path 上の各セルが t.normalize 範囲内であることを併せて持ち上げる
  have step_lift :
      ∀ {v : QuarterPos},
        Relation.ReflTransGen (IsGroundingEdge t) p₀ v →
        v.1 < t.normalize.length ∧
        Relation.ReflTransGen (IsGroundingEdge t.normalize) p₀ v := by
    intro v hv
    induction hv with
    | refl => exact ⟨hp₀_lt_norm, Relation.ReflTransGen.refl⟩
    | @tail b c _ hedge ih =>
        obtain ⟨hb_lt, hpath_norm⟩ := ih
        have hc_ne : ¬ (QuarterPos.getQuarter t c).isEmpty :=
          IsGroundingEdge.right_nonEmpty hedge
        have hc_lt_t : c.1 < t.length := nonEmpty_imp_layer_lt hc_ne
        have hne_idx := nonEmpty_imp_layer_isEmpty_false hc_ne
        have hc_lt_norm : c.1 < t.normalize.length :=
          normalize_length_of_nonEmpty t hc_lt_t hne_idx
        refine ⟨hc_lt_norm, ?_⟩
        exact hpath_norm.tail (IsGroundingEdge.of_normalize_range hb_lt hc_lt_norm hedge)
  obtain ⟨_, hPath_norm⟩ := step_lift hPath
  have hp₀_eq := getQuarter_normalize_eq t hp₀_lt_norm
  exact ⟨p₀, hLayer, hp₀_eq ▸ hNe₀, hPath_norm⟩

/-- §6.3 `landingDistance` が正値ならば、それは `landingCondition` を満たす。
    `landingDistance` は `find?` で `[1, ..., minLayer]` 範囲を線形探索し、
    `find?` の結果は元 list のメンバ + 述語成立。
    フォールバック値 `getD m` は `m` 自体が `landingCondition` を満たすかどうかは保証しない —
    その場合のみ `d = m` でも `landingCondition` は不成立になり得るが、
    **`d ≥ 1` ∧ `landingCondition obs u d = true`** が成立する場合に話を絞れば取り扱いやすい。 -/
private theorem landingCondition_landingDistance_pos
    (obs : Shape) (u : FallingUnit)
    (_h : landingDistance obs u ≥ 1)
    (hFound : (((List.range (u.minLayer + 1)).filter (· ≥ 1)).find?
                (fun d => landingCondition obs u d)).isSome) :
    landingCondition obs u (landingDistance obs u) = true := by
  -- `hFound` から `find? = some d` を取り出す。
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hFound
  -- `find?` の結果は元述語を満たす（`List.find?_some`）。
  have hpd : landingCondition obs u d = true := List.find?_some hd
  -- `landingDistance` 定義を展開して `hd` で書換 ⇒ `getD` が `d` に簡約。
  have hLD : landingDistance obs u = d := by
    unfold landingDistance
    simp [hd]
  rw [hLD]
  exact hpd

/-! §6.4 補助: `setQuarter` / `setQuarter` 反復の基本性質。
    `placeUnit` は `setQuarter` を `u.positions` 全体で foldl したものなので、
    foldl 段階の length 保存と「書込先以外の getQuarter 不変」を一般化しておく。 -/

/-- `setQuarter` は長さを変えない。 -/
private theorem length_setQuarter (s : Shape) (p : QuarterPos) (q : Quarter) :
    (QuarterPos.setQuarter s p q).length = s.length := by
  unfold QuarterPos.setQuarter
  split <;> simp [List.length_set]

/-- 書込先と異なる位置は `setQuarter` で値を変えない。 -/
private theorem getQuarter_setQuarter_of_ne
    (s : Shape) (p q : QuarterPos) (v : Quarter) (hne : q ≠ p) :
    QuarterPos.getQuarter (QuarterPos.setQuarter s p v) q =
      QuarterPos.getQuarter s q := by
  by_cases hp : p.1 < s.length
  · have hset : QuarterPos.setQuarter s p v = s.set p.1 ((s[p.1]'hp).setDir p.2 v) := by
      unfold QuarterPos.setQuarter; simp [hp]
    rw [hset]
    show (if h : q.1 < (s.set p.1 ((s[p.1]'hp).setDir p.2 v)).length then
            ((s.set p.1 ((s[p.1]'hp).setDir p.2 v))[q.1]'h) q.2 else Quarter.empty) =
         (if h : q.1 < s.length then (s[q.1]'h) q.2 else Quarter.empty)
    have hlen : (s.set p.1 ((s[p.1]'hp).setDir p.2 v)).length = s.length :=
      List.length_set ..
    by_cases hq : q.1 < s.length
    · have hq'' : q.1 < (s.set p.1 ((s[p.1]'hp).setDir p.2 v)).length := hlen ▸ hq
      simp only [hq, hq'', ↓reduceDIte]
      by_cases hidx : q.1 = p.1
      · -- 同レイヤ ⇒ 別方向
        have hd : q.2 ≠ p.2 := fun he => hne (by ext <;> simp [hidx, he])
        have hgs : (s.set p.1 ((s[p.1]'hp).setDir p.2 v))[q.1]'hq'' =
                    (s[p.1]'hp).setDir p.2 v := by
          have hcast : (s.set p.1 ((s[p.1]'hp).setDir p.2 v))[q.1]'hq'' =
              (s.set p.1 ((s[p.1]'hp).setDir p.2 v))[p.1]'(hlen ▸ hp) := by congr 1
          rw [hcast]; exact List.getElem_set_self ..
        rw [hgs]
        unfold Layer.setDir
        simp only [hd, ↓reduceIte]
        have hsidx : s[q.1]'hq = s[p.1]'hp := by congr 1
        rw [hsidx]
      · have hgs : (s.set p.1 ((s[p.1]'hp).setDir p.2 v))[q.1]'hq'' = s[q.1]'hq :=
          List.getElem_set_ne (Ne.symm hidx) _
        rw [hgs]
    · have hq'' : ¬ q.1 < (s.set p.1 ((s[p.1]'hp).setDir p.2 v)).length := hlen ▸ hq
      simp [hq, hq'']
  · have hset : QuarterPos.setQuarter s p v = s := by
      unfold QuarterPos.setQuarter; simp [hp]
    rw [hset]

/-- `setQuarter` の foldl は長さを変えない。 -/
private theorem foldl_setQuarter_length
    {α : Type*} (xs : List α) (s : Shape) (g : α → QuarterPos) (h : α → Quarter) :
    (xs.foldl (fun a p => QuarterPos.setQuarter a (g p) (h p)) s).length = s.length := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact length_setQuarter _ _ _

/-- 書込先 (`g x`) のいずれにも一致しない位置 `q` は foldl で値を変えない。 -/
private theorem foldl_setQuarter_getQuarter_of_not_target
    {α : Type*} (xs : List α) (s : Shape) (g : α → QuarterPos) (h : α → Quarter)
    (q : QuarterPos) (hne : ∀ x ∈ xs, g x ≠ q) :
    QuarterPos.getQuarter (xs.foldl (fun a p => QuarterPos.setQuarter a (g p) (h p)) s) q
      = QuarterPos.getQuarter s q := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hne' : ∀ y ∈ xs, g y ≠ q := fun y hy => hne y (List.mem_cons_of_mem _ hy)
      rw [ih _ hne']
      exact getQuarter_setQuarter_of_ne _ _ _ _ (Ne.symm (hne x List.mem_cons_self))

/-- §6.4 `placeUnit` は `acc` 由来の非空セルを破壊しない（cross-unit 上書き禁止）。

    **条件付き** 補題: `u` の着地像 `{(p.1 - d, p.2) | p ∈ u.positions}` の各位置が
    `acc` で空であることを仮定する（`hDisjoint`）。仮定が成立すれば書込先と既存非空セルが
    互いに素なので `setQuarter` の foldl は既存非空セルを破壊しない。

    foldl 文脈での `hDisjoint` の確立は §6.5 の主要課題（**R-§6.4**）。 -/
private theorem placeUnit_subsumed_by
    (origS acc : Shape) (u : FallingUnit) (d : Nat)
    (hDisjoint : ∀ p ∈ u.positions, ∀ q : QuarterPos,
        q = (p.1 - d, p.2) → (QuarterPos.getQuarter acc q).isEmpty) :
    Shape.subsumed_by acc (placeUnit origS acc u d) := by
  unfold placeUnit
  refine ⟨?_, ?_⟩
  · -- length 不変 ⇒ ≤ も成立
    rw [foldl_setQuarter_length]
  · intro q hq_ne
    -- 各書込ターゲット (p.1-d, p.2) は q と異なる
    -- （hDisjoint より空、q は非空 ⇒ 矛盾を避けて不一致）
    have hne_target : ∀ p ∈ u.positions, ((p.1 - d, p.2) : QuarterPos) ≠ q := by
      intro p hp heq
      have hempty : (QuarterPos.getQuarter acc q).isEmpty :=
        hDisjoint p hp q heq.symm
      exact hq_ne hempty
    exact foldl_setQuarter_getQuarter_of_not_target u.positions acc
      (fun p => (p.1 - d, p.2)) (fun p => QuarterPos.getQuarter origS p) q hne_target

/-- §6.4 `placeUnit` 後、`u` の各着地像位置が grounded になる。
    `landingCondition` で「直下に障害物 or 床到達」が保証されるため、
    `IsGroundingEdge` の `IsUpwardGroundingContact` 縦分枝で接地経路が伸びる。 -/
private theorem placeUnit_grounding
    (origS acc : Shape) (u : FallingUnit) (d : Nat)
    (_hLand : landingCondition acc u d = true)
    (_hAcc  : ∀ q : QuarterPos, q ∈ QuarterPos.allValid acc →
              ¬ (QuarterPos.getQuarter acc q).isEmpty → IsGrounded acc q)
    {p : QuarterPos} (_hp : p ∈ u.positions) :
    IsGrounded (placeUnit origS acc u d) (p.1 - d, p.2) := by
  -- 戦略:
  -- 1. landingCondition 成立 ⇒ 「u 内の少なくとも 1 セル q は q.1 = d または直下障害物」
  -- 2. その q に対して着地像 q' = (q.1 - d, q.2) は layer 0 か、(q.1 - d - 1, q.2) が acc で非空
  -- 3. layer 0 ケース: q' 自身が root
  -- 4. 直下障害物ケース: その障害物セル `obstacle` は acc で grounded（hAcc 帰納仮定）⇒ obstacle から q' へ IsGroundingEdge.IsUpwardGroundingContact (vertical, +1) ⇒ ReflTransGen 拡張
  -- 5. p ≠ q の場合: u 内構造結合（`canFormBond`）または同 minLayer 列での `IsBondedCrossLayer`
  --    で q から (p.1-d, p.2) まで到達できることを示す ← **要 unit 内連結性補題**
  sorry

/-- §6.5 foldl の不変量: 任意のステップ後で「全有効非空位置が IsGrounded」。 -/
private theorem foldl_grounded_invariant
    (s : Shape) (units : List FallingUnit)
    (acc : Shape)
    (_hBase : ∀ q ∈ QuarterPos.allValid acc,
              ¬ (QuarterPos.getQuarter acc q).isEmpty → IsGrounded acc q) :
    let result := units.foldl (fun a u => stepUnit s a u) acc
    ∀ q ∈ QuarterPos.allValid result,
      ¬ (QuarterPos.getQuarter result q).isEmpty → IsGrounded result q := by
  -- units 帰納:
  -- - nil: acc そのまま、hBase
  -- - cons u rest:
  --   acc' = stepUnit s acc u = placeUnit s acc u (landingDistance acc u)
  --   1. acc' の各非空位置 q' は次のいずれか:
  --      (a) q' は acc 由来 (subsumed_by) → IsGrounded acc q' → IsGrounded.mono で IsGrounded acc' q'
  --      (b) q' は u の着地像 → placeUnit_grounding
  --   2. 帰納仮定を acc' に適用
  -- 必要な未確定補題: subsumed_by の disjoint 仮定確立（R-§6.4）。
  sorry

/-- §6.6 基底補題: `obs0 = clearPositions s (floatingUnits.flatMap positions)` の
    各非空位置は `obs0` で IsGrounded である。

    根拠: `obs0` の非空位置 = `s` の非空かつ非 floating 位置 ⇒ `s` で IsGrounded
    （非 floating ⇔ grounded、§3.3 §5 の対偶）⇒ `s.subsumed_by obs0` ではなく
    **逆向き** `obs0.subsumed_by s`（floating セルが空化されただけ）から、
    grounded path 上のセルが floating セルを含まないことを示し再構成する。

    **注**: 本補題は `IsGrounded.mono` の単純 lift では閉じない（mono は拡張のみ）。
    grounded path の各中間頂点が non-floating であることの専用引数が要る。 -/
private theorem obs0_isGrounded_of_nonEmpty
    (s : Shape) :
    let units := floatingUnits s
    let obs0 := initialObstacle s units
    ∀ q ∈ QuarterPos.allValid obs0,
      ¬ (QuarterPos.getQuarter obs0 q).isEmpty → IsGrounded obs0 q := by
  -- 戦略:
  -- 1. q が obs0 で非空 ⇒ q は s で非空（clearPositions は空化のみ）
  -- 2. q は s で floating でない（floating なら clearPositions で空化されているはず）
  -- 3. ∴ s で IsGrounded q（floating の対偶）
  -- 4. s で IsGrounded q の path 上のセル v はすべて非 floating（連結 ⇒ 全 grounded）
  --    ※ ここが non-trivial: structural cluster 連結性 + grounded 1 点で全 grounded
  -- 5. ∴ path は obs0 でも保たれる（floating でないセルは空化されない）
  -- 6. ∴ obs0 で IsGrounded q
  sorry

/-- §6.6 主定理: `gravity` の出力は IsSettled。
    `(sortedUnits (floatingUnits s)).foldl (stepUnit s) (initialObstacle s _)` の
    全有効非空位置が grounded であることを §6.5 で示し、§6.2 で `normalize` を通す。 -/
theorem gravity_isSettled_collision (s : Shape) :
    IsSettled (Shape.gravity s) := by
  -- Step 1: 定義展開
  unfold Shape.gravity
  -- Step 2: normalize 越し（§6.2）
  apply IsSettled.normalize
  -- Step 3: 基底 `obs0 = initialObstacle s units` で「非空位置は grounded」を確立
  --        → `obs0` の非空セルは「s で非 floating な非空セル」⇒ s で grounded
  --        ⇒ `clearPositions` で edge を破壊しない範囲で IsGrounded.mono
  --        （要: `IsGrounded.mono` の逆向き分枝、もしくは別補題）
  -- Step 4: §6.5 を適用
  intro q hValid hNonEmpty
  -- 残りの組立は §6.5 完成後に詰める
  sorry

end Internal
end Gravity
end S2IL
