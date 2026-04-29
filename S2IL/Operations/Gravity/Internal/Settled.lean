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
  push Not at hcontra
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
  push Not at hc
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

/-- `setQuarter` で同位置に書き込んだ後の `getQuarter` は書込値（範囲内）。 -/
private theorem getQuarter_setQuarter_self
    (s : Shape) (q : QuarterPos) (v : Quarter) (hq : q.1 < s.length) :
    QuarterPos.getQuarter (QuarterPos.setQuarter s q v) q = v := by
  have hset : QuarterPos.setQuarter s q v = s.set q.1 ((s[q.1]'hq).setDir q.2 v) := by
    unfold QuarterPos.setQuarter; simp [hq]
  rw [hset]
  have hq2 : q.1 < (s.set q.1 ((s[q.1]'hq).setDir q.2 v)).length := by
    simp [List.length_set, hq]
  unfold QuarterPos.getQuarter
  simp only [hq2, ↓reduceDIte]
  rw [List.getElem_set_self]
  unfold Layer.setDir
  simp

/-- 書込先 (`g x = q`) のいずれかが xs に存在し、書込値が `Quarter.empty` 定数のとき、
    foldl 後の値は `Quarter.empty`。範囲外位置でも `getQuarter` は `empty` を返すため
    範囲内仮定不要。 -/
private theorem foldl_setQuarter_const_empty_at_in_target
    {α : Type*} (xs : List α) (s : Shape) (g : α → QuarterPos)
    {q : QuarterPos} (hin : ∃ x ∈ xs, g x = q) :
    QuarterPos.getQuarter
        (xs.foldl (fun a p => QuarterPos.setQuarter a (g p) Quarter.empty) s) q
      = Quarter.empty := by
  induction xs generalizing s with
  | nil =>
      obtain ⟨_, hmem, _⟩ := hin
      simp at hmem
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hxs : ∃ y ∈ xs, g y = q
      · exact ih _ hxs
      · push Not at hxs
        rw [foldl_setQuarter_getQuarter_of_not_target xs _ g _ q hxs]
        obtain ⟨z, hz, hgz⟩ := hin
        rcases List.mem_cons.mp hz with rfl | hzxs
        · -- g x = q ⇒ setQuarter at q with empty
          rw [hgz]
          by_cases hq1 : q.1 < s.length
          · exact getQuarter_setQuarter_self s q Quarter.empty hq1
          · -- 範囲外: setQuarter は s を変えず、getQuarter は empty
            unfold QuarterPos.setQuarter QuarterPos.getQuarter
            simp [hq1]
        · exact absurd hgz (hxs z hzxs)

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

/-! §6.4 補助: `placeUnit_grounding` の MECE 分解。

    `placeUnit_grounding` は次の 3 段階に分解する:
    - **6.4.A** `landingCondition_witness`: `landingCondition` から「床到達 or 直下障害物」
      を満たす witness `q* ∈ u.positions` を取り出す（純粋に `List.any` の特徴付け）。
    - **6.4.B** `placeUnit_witness_grounded`: witness `q*` の着地像が
      `placeUnit ... acc u d` で grounded であることを示す（layer 0 root 直接 / 障害物経由 +
      `IsUpwardGroundingContact`）。
    - **6.4.C** `placeUnit_unit_internal_path`: 任意の `p ∈ u.positions` から witness `q*` の
      着地像へ `IsGroundingEdge` の `ReflTransGen` で到達できる（unit の構造結合が
      `placeUnit` 後も保たれる）。

    主補題 `placeUnit_grounding` は B + C の合成。
    A は今セッションで証明、B / C は次セッション以降。
-/

/-- §6.4.A `landingCondition` 成立から witness `q ∈ u.positions` を取り出す。

    具体的には: ∃ q ∈ u.positions,
      `q.1 = d` ∨ (`q.1 > d` ∧ `(q.1 - d - 1, q.2)` が acc で非空)。 -/
private theorem landingCondition_witness
    {acc : Shape} {u : FallingUnit} {d : Nat}
    (h : landingCondition acc u d = true) :
    ∃ q ∈ u.positions,
      q.1 = d ∨ (q.1 > d ∧ ¬ (QuarterPos.getQuarter acc (q.1 - d - 1, q.2)).isEmpty) := by
  unfold landingCondition at h
  rw [List.any_eq_true] at h
  obtain ⟨q, hq_in, hq_pred⟩ := h
  refine ⟨q, hq_in, ?_⟩
  rw [Bool.or_eq_true] at hq_pred
  rcases hq_pred with hfloor | hbelow
  · exact Or.inl (by simpa using hfloor)
  · rw [Bool.and_eq_true] at hbelow
    obtain ⟨hgt, hne⟩ := hbelow
    have hgt' : q.1 > d := by simpa using hgt
    have hne' : ¬ (QuarterPos.getQuarter acc (q.1 - d - 1, q.2)).isEmpty := by
      simpa [Bool.not_eq_true'] using hne
    exact Or.inr ⟨hgt', hne'⟩

/-- §6.4.B witness `q* ∈ u.positions` の着地像が `placeUnit ... acc u d` で grounded。

    ケース分解:
    - **q*.1 = d (床到達)**: `(0, q*.2)` 自身が layer 0 root。`placeUnit` が `(0, q*.2)`
      へ `quarterAt origS q*` を書き込み、これは origS で非空（u は origS の non-empty 集合
      由来）⇒ root として有効。
    - **q*.1 > d ∧ 直下障害物**: 障害物位置 `obstacle = (q*.1 - d - 1, q*.2)` は acc で
      非空 ⇒ hAcc から `IsGrounded acc obstacle`。`hDisjoint` で `placeUnit` が obstacle を
      上書きしないため `IsGrounded.mono` で `IsGrounded (placeUnit ...) obstacle`。さらに
      `obstacle` から `(q*.1 - d, q*.2)` へ垂直 `IsUpwardGroundingContact` を貼る
      （両端 origS 由来非空 + `+1` 隣接 + 同方角）。

    **要補助**: `placeUnit_writes_origS_value`（書込先で origS 値が確定）+
    `quarterAt_nonEmpty_of_origS`（落下単位の position は origS で非空）。 -/
private theorem placeUnit_witness_grounded
    (origS acc : Shape) (u : FallingUnit) (d : Nat)
    (_hAcc : ∀ q : QuarterPos, q ∈ QuarterPos.allValid acc →
             ¬ (QuarterPos.getQuarter acc q).isEmpty → IsGrounded acc q)
    (_hDisjoint : ∀ p ∈ u.positions, ∀ q : QuarterPos,
        q = (p.1 - d, p.2) → (QuarterPos.getQuarter acc q).isEmpty)
    (_hOrigS : ∀ p ∈ u.positions, ¬ (QuarterPos.getQuarter origS p).isEmpty)
    {q : QuarterPos} (_hq_in : q ∈ u.positions)
    (_hq_pred : q.1 = d ∨ (q.1 > d ∧
      ¬ (QuarterPos.getQuarter acc (q.1 - d - 1, q.2)).isEmpty)) :
    IsGrounded (placeUnit origS acc u d) (q.1 - d, q.2) := by
  sorry

/-- §6.4.C unit 内連結: 任意の `p, q ∈ u.positions` の着地像同士は `placeUnit` 後の
    `IsGroundingEdge` で `ReflTransGen` 関係にある。

    根拠（cluster の場合）: `u.positions` は `structuralCluster s p₀` の元（`canFormBond`
    BFS 連結）。各セルは `placeUnit` で origS の Quarter 値が書かれるため `canFormBond`
    判定が保たれ、`IsBondedInLayer` / `IsBondedCrossLayer` が `placeUnit` 後に成立する。
    着地像 `(p.1 - d, p.2)` 間の隣接性は元 `(p.1, p.2)` の隣接性から `Direction.isAdjacent`
    と `Nat.sub` の単調性で保たれる（同 layer 平行移動 / cross-layer は両 layer から d を
    引くため差分保存）。

    `pin` の場合は単一 position なので refl で自明。 -/
private theorem placeUnit_unit_internal_path
    (origS acc : Shape) (u : FallingUnit) (d : Nat)
    {p q : QuarterPos} (_hp : p ∈ u.positions) (_hq : q ∈ u.positions) :
    Relation.ReflTransGen (IsGroundingEdge (placeUnit origS acc u d))
      (q.1 - d, q.2) (p.1 - d, p.2) := by
  sorry

/-- §6.4 主補題: `placeUnit` 後、`u` の各着地像位置が grounded。

    `landingCondition_witness` (6.4.A) で witness `q*` を取り出し、
    `placeUnit_witness_grounded` (6.4.B) で `q*` の着地像が grounded、
    `placeUnit_unit_internal_path` (6.4.C) で任意の `p` の着地像へ path を伸ばす。 -/
private theorem placeUnit_grounding
    (origS acc : Shape) (u : FallingUnit) (d : Nat)
    (hLand : landingCondition acc u d = true)
    (hAcc  : ∀ q : QuarterPos, q ∈ QuarterPos.allValid acc →
             ¬ (QuarterPos.getQuarter acc q).isEmpty → IsGrounded acc q)
    (hDisjoint : ∀ p ∈ u.positions, ∀ q : QuarterPos,
        q = (p.1 - d, p.2) → (QuarterPos.getQuarter acc q).isEmpty)
    (hOrigS : ∀ p ∈ u.positions, ¬ (QuarterPos.getQuarter origS p).isEmpty)
    {p : QuarterPos} (hp : p ∈ u.positions) :
    IsGrounded (placeUnit origS acc u d) (p.1 - d, p.2) := by
  obtain ⟨q, hq_in, hq_pred⟩ := landingCondition_witness hLand
  have hq_grounded :=
    placeUnit_witness_grounded origS acc u d hAcc hDisjoint hOrigS hq_in hq_pred
  obtain ⟨p₀, hLayer, hNe, hPath⟩ := hq_grounded
  refine ⟨p₀, hLayer, hNe, ?_⟩
  exact hPath.trans (placeUnit_unit_internal_path origS acc u d hp hq_in)

/-! §6.5 補助: `foldl_grounded_invariant` の MECE 分解。

    `foldl` の 1 ステップ `acc → stepUnit s acc u` を以下の補題で支える:
    - **6.5.A** `stepUnit_landing_disjoint` (R-§6.4 の本体): `acc` の非空位置すべてが
      grounded であり、かつ `u ∈ floatingUnits s` のとき、u の着地像 `(p.1 - d, p.2)` は
      acc で空（cross-unit 上書き禁止）。
    - **6.5.B** `stepUnit_subsumed_by`: 上記 disjoint 性から `placeUnit_subsumed_by` を起動、
      `Shape.subsumed_by acc (stepUnit s acc u)`。
    - **6.5.C** `stepUnit_grounded_invariant_step`: 1 ステップで grounded 不変量が保たれる
      （A の場合分けで「acc 由来非空セル」と「u の着地像」に分け、前者は B + IsGrounded.mono、
       後者は `placeUnit_grounding`）。

    A は **R-§6.4** の主要不確定要素。`landingDistance` の最小性 + `floatingUnits s` の
    定義（u の cells は s で互いに非干渉）+ sortedUnits 順序から得る予定。 -/

/-- §6.5.A R-§6.4 中核: grounded 不変量下で u の着地像は acc で空。

    **要件** (要追加引数):
    - `u ∈ floatingUnits s`（u は s の浮遊単位）
    - `acc` 自体が「s 由来の非空セル + 既処理単位の着地像のみ」で構成されることを保証する
      補助構造（typically: `acc.subsumed_by (initialObstacle s units) ∨ acc = stepUnit ...` の
      帰納構造）

    **戦略**: `landingCondition acc u d = true` の最小性により、`d` より小さい `d'` では
    landingCondition が偽 ⇒ u 全体が宙吊り。仮に `(p.1 - d, p.2)` が acc で非空ならば、
    grounded 不変量から acc で grounded ⇒ s でも grounded （subsumed の逆向き保存性、
    要証明）⇒ u が「s で `d` 段下げ可能な単位」という前提と矛盾。

    本補題は **R-§6.4** の正面突破; pivot の場合は `landingCondition'` への強化が代替案。 -/
private theorem stepUnit_landing_disjoint
    (s acc : Shape) (u : FallingUnit)
    (_hAcc : ∀ q ∈ QuarterPos.allValid acc,
             ¬ (QuarterPos.getQuarter acc q).isEmpty → IsGrounded acc q)
    (_hUnit : u ∈ floatingUnits s)
    (_hAccBound : Shape.subsumed_by acc s ∨ acc.length = s.length) :
    let d := landingDistance acc u
    ∀ p ∈ u.positions, ∀ q : QuarterPos,
      q = (p.1 - d, p.2) → (QuarterPos.getQuarter acc q).isEmpty := by
  sorry

/-- §6.5.B disjoint 性から `Shape.subsumed_by acc (stepUnit s acc u)`。 -/
private theorem stepUnit_subsumed_by
    (s acc : Shape) (u : FallingUnit)
    (hAcc : ∀ q ∈ QuarterPos.allValid acc,
            ¬ (QuarterPos.getQuarter acc q).isEmpty → IsGrounded acc q)
    (hUnit : u ∈ floatingUnits s)
    (hAccBound : Shape.subsumed_by acc s ∨ acc.length = s.length) :
    Shape.subsumed_by acc (stepUnit s acc u) := by
  unfold stepUnit
  exact placeUnit_subsumed_by s acc u (landingDistance acc u)
    (stepUnit_landing_disjoint s acc u hAcc hUnit hAccBound)

/-- §6.5.C 1 ステップで grounded 不変量が保たれる。

    `acc'` の任意の非空セル `q` は:
    - **(i)** `q` が acc で非空（`acc.subsumed_by acc'` で値同一）⇒ acc で grounded ⇒
      mono で acc' でも grounded
    - **(ii)** `q` が acc で空、`q = (p.1 - d, p.2)` for some p ∈ u.positions
      ⇒ `placeUnit_grounding` 直接適用
-/
private theorem stepUnit_grounded_invariant_step
    (s acc : Shape) (u : FallingUnit)
    (_hAcc : ∀ q ∈ QuarterPos.allValid acc,
             ¬ (QuarterPos.getQuarter acc q).isEmpty → IsGrounded acc q)
    (_hUnit : u ∈ floatingUnits s)
    (_hAccBound : Shape.subsumed_by acc s ∨ acc.length = s.length) :
    let acc' := stepUnit s acc u
    (∀ q ∈ QuarterPos.allValid acc',
      ¬ (QuarterPos.getQuarter acc' q).isEmpty → IsGrounded acc' q)
    ∧ (Shape.subsumed_by acc' s ∨ acc'.length = s.length) := by
  sorry

/-- §6.5 主補題: foldl の不変量。

    units 帰納: `nil` で hBase、`cons u rest` で `stepUnit_grounded_invariant_step`
    を適用して帰納仮定を `acc' = stepUnit s acc u` に持ち上げる。 -/
private theorem foldl_grounded_invariant
    (s : Shape) (units : List FallingUnit)
    (acc : Shape)
    (hBase : ∀ q ∈ QuarterPos.allValid acc,
             ¬ (QuarterPos.getQuarter acc q).isEmpty → IsGrounded acc q)
    (hUnits : ∀ u ∈ units, u ∈ floatingUnits s)
    (hAccBound : Shape.subsumed_by acc s ∨ acc.length = s.length) :
    let result := units.foldl (fun a u => stepUnit s a u) acc
    ∀ q ∈ QuarterPos.allValid result,
      ¬ (QuarterPos.getQuarter result q).isEmpty → IsGrounded result q := by
  induction units generalizing acc with
  | nil => exact hBase
  | cons u rest ih =>
      simp only [List.foldl_cons]
      have hu : u ∈ floatingUnits s := hUnits u List.mem_cons_self
      have hRest : ∀ v ∈ rest, v ∈ floatingUnits s :=
        fun v hv => hUnits v (List.mem_cons_of_mem _ hv)
      have hStep := stepUnit_grounded_invariant_step s acc u hBase hu hAccBound
      exact ih (stepUnit s acc u) hStep.1 hRest hStep.2

/-! §6.6 補助: `obs0_isGrounded_of_nonEmpty` の MECE 分解。

    `obs0 = clearPositions s (units.flatMap positions)` の構造解析:
    - **6.6.A** `clearPositions_getQuarter_of_not_in`: `q ∉ positions` ⇒
      `getQuarter (clearPositions s positions) q = getQuarter s q`（`foldl_setQuarter_get
      Quarter_of_not_target` の specialize）。
    - **6.6.B** `obs0_nonEmpty_imp_origS_nonEmpty`: obs0 で非空 ⇒ s で同値非空。
    - **6.6.C** `obs0_nonEmpty_imp_not_floating`: obs0 で非空 ⇒ q ∉ 任意 floating unit。
    - **6.6.D** `not_floating_imp_grounded`: 非空 ∧ ∀ floating unit に含まれない ⇒
      `IsGrounded s q`（`floatingUnits_eq_nil_of_isSettled` の局所版で対偶利用）。
    - **6.6.E** `grounded_path_avoids_floating`: `IsGrounded s q` の path 上のセルは
      すべて非 floating（path は構造クラスタ内 + cross-cluster contact のみで構成され、
      floating cluster はそもそも layer 0 root へ到達不可能）。
    - **6.6.F** `obs0_isGrounded_of_nonEmpty`: 上記合成。
-/

/-- §6.6 補助: `IsGroundingEdge` は両端 `getQuarter` 値のみに依存するため、
    両端で値が一致する別シェイプへ lift できる（`subsumed_by` のサブケース）。

    `obs0` への lift（path 上のセルが clear されない ⇒ `s` と `obs0` で値同一）に用いる。 -/
private theorem IsGroundingEdge.of_getQuarter_eq
    {s s' : Shape} {a b : QuarterPos}
    (ha : QuarterPos.getQuarter s a = QuarterPos.getQuarter s' a)
    (hb : QuarterPos.getQuarter s b = QuarterPos.getQuarter s' b)
    (he : IsGroundingEdge s a b) :
    IsGroundingEdge s' a b := by
  rcases he with hUp | hBond
  · refine Or.inl ⟨?_, hUp.2⟩
    rcases hUp.1 with ⟨hcol, hadj, hneA, hneB⟩ | ⟨hrow, hadj, hneA, hneB, hnpA, hnpB⟩
    · exact Or.inl ⟨hcol, hadj, ha ▸ hneA, hb ▸ hneB⟩
    · exact Or.inr ⟨hrow, hadj, ha ▸ hneA, hb ▸ hneB, ha ▸ hnpA, hb ▸ hnpB⟩
  · refine Or.inr ?_
    rcases hBond with ⟨hrow, hadj, hcA, hcB⟩ | ⟨hlayer, hcol, hcA, hcB⟩
    · exact Or.inl ⟨hrow, hadj,
        show (QuarterPos.getQuarter s' a).IsCrystal from ha ▸ hcA,
        show (QuarterPos.getQuarter s' b).IsCrystal from hb ▸ hcB⟩
    · exact Or.inr ⟨hlayer, hcol,
        show (QuarterPos.getQuarter s' a).IsCrystal from ha ▸ hcA,
        show (QuarterPos.getQuarter s' b).IsCrystal from hb ▸ hcB⟩

/-- §6.6.A `clearPositions` で書き込み対象外の位置は値が変わらない。 -/
private theorem clearPositions_getQuarter_of_not_in
    (s : Shape) (positions : List QuarterPos)
    {q : QuarterPos} (hq : q ∉ positions) :
    QuarterPos.getQuarter (Shape.clearPositions s positions) q = QuarterPos.getQuarter s q := by
  unfold Shape.clearPositions
  exact foldl_setQuarter_getQuarter_of_not_target positions s
    (fun p => p) (fun _ => Quarter.empty) q (fun x hx hxq => hq (hxq ▸ hx))

/-- §6.6.B obs0 で非空 ⇒ s で同値非空。 -/
private theorem obs0_nonEmpty_imp_origS_nonEmpty
    (s : Shape) (units : List FallingUnit)
    {q : QuarterPos}
    (hne : ¬ (QuarterPos.getQuarter (initialObstacle s units) q).isEmpty) :
    QuarterPos.getQuarter (initialObstacle s units) q = QuarterPos.getQuarter s q := by
  -- q が clear 対象に含まれていれば clear 後は empty (矛盾) ⇒ 含まれていない
  by_cases hin : q ∈ units.flatMap FallingUnit.positions
  · -- q が clear 対象 ⇒ obs0 で empty ⇒ hne と矛盾
    exfalso; apply hne
    unfold initialObstacle Shape.clearPositions
    rw [foldl_setQuarter_const_empty_at_in_target
          (units.flatMap FallingUnit.positions) s (fun p => p) ⟨q, hin, rfl⟩]
    rfl
  · unfold initialObstacle
    exact clearPositions_getQuarter_of_not_in s _ hin

/-- §6.6.C obs0 で非空 ⇒ q は任意 floating unit に含まれない。

    対偶: 任意 floating unit に q が含まれる ⇒ q は clear 対象 ⇒ obs0 で empty。
    `foldl_setQuarter_const_empty_at_in_target` で帰結。 -/
private theorem obs0_nonEmpty_imp_not_floating
    (s : Shape) {q : QuarterPos}
    (hne : ¬ (QuarterPos.getQuarter (initialObstacle s (floatingUnits s)) q).isEmpty) :
    ∀ u ∈ floatingUnits s, q ∉ u.positions := by
  intro u hu hqu
  apply hne
  unfold initialObstacle Shape.clearPositions
  rw [foldl_setQuarter_const_empty_at_in_target
        ((floatingUnits s).flatMap FallingUnit.positions) s (fun p => p)
        ⟨q, List.mem_flatMap.mpr ⟨u, hu, hqu⟩, rfl⟩]
  rfl

/-- §6.6.D 非空 ∧ 非 floating ⇒ s で IsGrounded。

    `floatingUnits` の補集合は s で grounded（非空セルは `floatingClusters`/`floatingPins`
    のいずれにも入らないので、構造的に layer 0 へ繋がっている）。 -/
private theorem not_floating_imp_grounded
    (s : Shape) {q : QuarterPos}
    (_hValid : q ∈ QuarterPos.allValid s)
    (_hne : ¬ (QuarterPos.getQuarter s q).isEmpty)
    (_hnf : ∀ u ∈ floatingUnits s, q ∉ u.positions) :
    IsGrounded s q := by
  sorry

/-- §6.6.E `IsGrounded s q` の path 上の任意のセルは非 floating。

    `IsGrounded s q` は ∃ root `p₀` (layer 0, 非空) で `ReflTransGen (IsGroundingEdge s) p₀ q`。
    path 上のセル `v` (i.e. `ReflTransGen (IsGroundingEdge s) p₀ v` を満たす) は
    `IsGroundingEdge` 連鎖で root と繋がる ⇒ `IsGrounded s v` ⇒ 非空かつ floating でない。

    `IsGroundingEdge` 連鎖は `IsUpwardGroundingContact` / `IsBonded` で構成され、両端非空 ⇒
    v は s で非空。さらに root から v へ path 存在 ⇒ `IsGrounded s v` ⇒
    `clusterFloating`/`floatingPins` の定義（`isGroundedFast` 偽でフィルタ）から非 floating。 -/
private theorem grounded_path_avoids_floating
    (s : Shape) {p₀ v : QuarterPos}
    (hRoot : p₀.1 = 0 ∧ ¬ (QuarterPos.getQuarter s p₀).isEmpty)
    (hPath : Relation.ReflTransGen (IsGroundingEdge s) p₀ v) :
    ∀ u ∈ floatingUnits s, v ∉ u.positions := by
  -- v は IsGrounded（path のあるセルは root をそのまま流用すれば grounded）
  have hgrV : IsGrounded s v := ⟨p₀, hRoot.1, hRoot.2, hPath⟩
  have hfastV : isGroundedFast s v = true := isGroundedFast_of_isGrounded s v hgrV
  intro u hu hv
  unfold floatingUnits at hu
  rcases List.mem_append.mp hu with hCl | hPin
  · -- cluster ケース: cl ∈ floatingClusters s, v ∈ cl
    obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp hCl
    have hvcl : v ∈ cl := by simpa [FallingUnit.positions] using hv
    unfold floatingClusters at hcl
    rw [List.mem_filter] at hcl
    obtain ⟨_, hflt⟩ := hcl
    unfold clusterFloating at hflt
    rw [List.all_eq_true] at hflt
    have hng : ¬ isGroundedFast s v = true := by
      have := hflt v hvcl
      simpa [Bool.not_eq_true'] using this
    exact hng hfastV
  · -- pin ケース: p ∈ floatingPins s, v = p
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hPin
    have hvp : v = p := by simpa [FallingUnit.positions] using hv
    unfold floatingPins at hp
    rw [List.mem_filter] at hp
    obtain ⟨_, hflt⟩ := hp
    rw [Bool.and_eq_true] at hflt
    obtain ⟨_, hng⟩ := hflt
    have : ¬ isGroundedFast s p = true := by
      simpa [Bool.not_eq_true'] using hng
    exact this (hvp ▸ hfastV)

/-- §6.6.F obs0 の各非空位置は obs0 で IsGrounded。

    合成: B (obs0 非空 ⇒ s 非空 + 値一致) + C (q ∉ floating unit) + D (s で IsGrounded) +
    E (path 上の各セルも非 floating ⇒ obs0 で値一致) + helper
    `IsGroundingEdge.of_getQuarter_eq` で edge を obs0 へ lift。 -/
private theorem obs0_isGrounded_of_nonEmpty
    (s : Shape) :
    ∀ q ∈ QuarterPos.allValid (initialObstacle s (floatingUnits s)),
      ¬ (QuarterPos.getQuarter (initialObstacle s (floatingUnits s)) q).isEmpty →
      IsGrounded (initialObstacle s (floatingUnits s)) q := by
  intro q hValid hNe
  set obs0 := initialObstacle s (floatingUnits s) with hobs0_def
  -- B + C + D で IsGrounded s q を得る
  have hEq := obs0_nonEmpty_imp_origS_nonEmpty s (floatingUnits s) hNe
  have hne_s : ¬ (QuarterPos.getQuarter s q).isEmpty := by rw [← hEq]; exact hNe
  have hLenEq : obs0.length = s.length := by
    show ((floatingUnits s).flatMap FallingUnit.positions |>.foldl
        (fun acc p => QuarterPos.setQuarter acc p Quarter.empty) s).length = s.length
    exact foldl_setQuarter_length _ s (fun p => p) (fun _ => Quarter.empty)
  have hValid_s : q ∈ QuarterPos.allValid s := by
    rw [QuarterPos.mem_allValid] at hValid ⊢
    rw [hLenEq] at hValid
    exact hValid
  have hnf := obs0_nonEmpty_imp_not_floating s hNe
  have hgrounded_s : IsGrounded s q := not_floating_imp_grounded s hValid_s hne_s hnf
  -- E: path 上のセルは非 floating ⇒ clear 対象外 ⇒ obs0 で値一致 ⇒ edge lift
  obtain ⟨p₀, hp0Layer, hp0Ne, hPath⟩ := hgrounded_s
  -- root の obs0 値も s と一致
  have hp0Notfl : ∀ u ∈ floatingUnits s, p₀ ∉ u.positions :=
    grounded_path_avoids_floating s ⟨hp0Layer, hp0Ne⟩ Relation.ReflTransGen.refl
  have hp0NotIn : p₀ ∉ (floatingUnits s).flatMap FallingUnit.positions := by
    intro hin
    rcases List.mem_flatMap.mp hin with ⟨u, hu, hpu⟩
    exact hp0Notfl u hu hpu
  have hp0_eq_obs : QuarterPos.getQuarter obs0 p₀ = QuarterPos.getQuarter s p₀ := by
    show QuarterPos.getQuarter (Shape.clearPositions s _) p₀ = _
    exact clearPositions_getQuarter_of_not_in s _ hp0NotIn
  have hp0NeObs : ¬ (QuarterPos.getQuarter obs0 p₀).isEmpty := by
    rw [hp0_eq_obs]; exact hp0Ne
  -- path を obs0 へ lift（induction、edge ごとに getQuarter 一致 ⇒ helper 適用）
  refine ⟨p₀, hp0Layer, hp0NeObs, ?_⟩
  clear hValid hValid_s hNe hEq hne_s hLenEq hnf hp0NeObs
  induction hPath with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hPath_ab hedge ih =>
      -- ih : ReflTransGen (IsGroundingEdge obs0) p₀ b
      -- hedge : IsGroundingEdge s b c
      -- b は path 上 (p₀ → b) ⇒ 非 floating, c も path 上 (p₀ → c) ⇒ 非 floating
      have hb_notfl : ∀ u ∈ floatingUnits s, b ∉ u.positions :=
        grounded_path_avoids_floating s ⟨hp0Layer, hp0Ne⟩ hPath_ab
      have hc_notfl : ∀ u ∈ floatingUnits s, c ∉ u.positions :=
        grounded_path_avoids_floating s ⟨hp0Layer, hp0Ne⟩ (hPath_ab.tail hedge)
      have hbNotIn : b ∉ (floatingUnits s).flatMap FallingUnit.positions := by
        intro hin
        rcases List.mem_flatMap.mp hin with ⟨u, hu, hpu⟩
        exact hb_notfl u hu hpu
      have hcNotIn : c ∉ (floatingUnits s).flatMap FallingUnit.positions := by
        intro hin
        rcases List.mem_flatMap.mp hin with ⟨u, hu, hpu⟩
        exact hc_notfl u hu hpu
      have hb_eq : QuarterPos.getQuarter s b = QuarterPos.getQuarter obs0 b := by
        show _ = QuarterPos.getQuarter (Shape.clearPositions s _) b
        rw [clearPositions_getQuarter_of_not_in s _ hbNotIn]
      have hc_eq : QuarterPos.getQuarter s c = QuarterPos.getQuarter obs0 c := by
        show _ = QuarterPos.getQuarter (Shape.clearPositions s _) c
        rw [clearPositions_getQuarter_of_not_in s _ hcNotIn]
      exact ih.tail (IsGroundingEdge.of_getQuarter_eq hb_eq hc_eq hedge)

/-- §6.6 主定理: `gravity` の出力は IsSettled。

    合成順序:
    1. `Shape.gravity s = (sortedUnits ...).foldl (stepUnit s) (initialObstacle ...)`
       `.normalize`
    2. `IsSettled.normalize` (§6.2) で normalize を剥がす
    3. `foldl_grounded_invariant` (§6.5) で foldl 後の grounded 不変量を取得
    4. 基底 `obs0_isGrounded_of_nonEmpty` (§6.6) で `hBase` を提供
    5. `hUnits`: sortedUnits の元は floatingUnits の置換 ⇒ membership 保存
    6. `hAccBound`: obs0 = clearPositions s _ で length 不変 -/
theorem gravity_isSettled_collision (s : Shape) :
    IsSettled (Shape.gravity s) := by
  unfold Shape.gravity
  apply IsSettled.normalize
  set units := floatingUnits s with hunits_def
  set order := sortedUnits units with horder_def
  set obs0 := initialObstacle s units with hobs0_def
  -- hBase: obs0 で grounded 不変量
  have hBase :
      ∀ q ∈ QuarterPos.allValid obs0,
        ¬ (QuarterPos.getQuarter obs0 q).isEmpty → IsGrounded obs0 q :=
    obs0_isGrounded_of_nonEmpty s
  -- hUnits: order の元は floatingUnits の元
  have hUnits : ∀ u ∈ order, u ∈ floatingUnits s := by
    intro u hu
    have : u ∈ units := by
      have hperm : order.Perm units :=
        List.mergeSort_perm units (fun a b => decide (a.minLayer ≤ b.minLayer))
      exact hperm.mem_iff.mp hu
    exact this
  -- hAccBound: obs0.length = s.length
  have hAccBound : Shape.subsumed_by obs0 s ∨ obs0.length = s.length := by
    right
    show ((floatingUnits s).flatMap FallingUnit.positions |>.foldl
        (fun acc p => QuarterPos.setQuarter acc p Quarter.empty) s).length = s.length
    exact foldl_setQuarter_length _ s (fun p => p) (fun _ => Quarter.empty)
  exact foldl_grounded_invariant s order obs0 hBase hUnits hAccBound

end Internal
end Gravity
end S2IL
